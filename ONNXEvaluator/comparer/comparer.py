import subprocess
import sys
import onnxruntime as ort
import numpy as np
import os


# use standard parameters
evaluations = 10  # number of evaluations
model_path = "../cartpole.onnx"  # path to the ONNX model
model_name = "cartpole"  # legacy parameter name, no longer used
onnx_proto_schema = "../onnx.proto"  # path to ONNX protobuf schema

# exactly one argument is invalid
if len(sys.argv) < 3:
    print(f"Usage: {sys.argv[0]} <number_evaluations> <model_path> <model_name> [onnx_proto_schema]")
    exit()

# if arguments are given
if len(sys.argv) >= 4:
    # use parameters from command line inputs
    evaluations = int(sys.argv[1])
    model_path = sys.argv[2]
    model_name = sys.argv[3]
    if len(sys.argv) > 4:
        onnx_proto_schema = sys.argv[4]

session = ort.InferenceSession(model_path)  # set up a runtime session

# get input shapes & names
shapes = []  # shapes of the inputs
input_names = []  # names of the inputs
for input_ in session.get_inputs():
    shapes.append(input_.shape)
    input_names.append(input_.name)

# get random inputs
inputs = []
for i in range(evaluations):
    inputs_per_evaluation = []
    for shape in shapes:
        random_array = np.random.rand(*shape).astype(np.float32)
        inputs_per_evaluation.append(random_array)
    inputs.append(inputs_per_evaluation)

# get outputs from onnx runtime
runtime_outputs = []
for i in range(evaluations):
    d = dict(zip(input_names, inputs[i]))
    runtime_outputs_per_evaluation = session.run(None, d)
    runtime_outputs.append(runtime_outputs_per_evaluation)


def array_to_string_list(a: np.ndarray):
    """Convert numpy array to list of string values and list of string dimensions."""
    values = list(a.flatten())
    dims = list(a.shape)
    return values, dims


def format_input_for_runner(input_name: str, values: list, dims: list) -> str:
    """Format a single input as name|value1,value2,...|dim1,dim2,..."""
    values_str = ",".join([f"{v:.6f}" for v in values])
    dims_str = ",".join([str(d) for d in dims])
    return f"{input_name}|{values_str}|{dims_str}"


# Serialize all inputs for the runner
# Format: One line per evaluation, inputs separated by ';;'
# Each input: name|value1,value2,...|dim1,dim2,...
runner_input_lines = []
for inputs_per_evaluation in inputs:
    input_strs = []
    for input_nr, input_array in enumerate(inputs_per_evaluation):
        values, dims = array_to_string_list(input_array)
        input_strs.append(format_input_for_runner(input_names[input_nr], values, dims))
    runner_input_lines.append(";;".join(input_strs))

runner_input = "\n".join(runner_input_lines)

# Path to the runner executable
runner_exe = os.path.join("_build", "default", "ONNXEvaluator", "runner", "onnx_evaluator_runner.exe")

# Set LD_LIBRARY_PATH to avoid GLIBCXX issues with protoc
os.environ["LD_LIBRARY_PATH"] = "/usr/lib/x86_64-linux-gnu:/usr/local/lib"

# Call the runner
print(f"Calling runner: {runner_exe}")
print(f"Model path: {model_path}")
print(f"Proto schema: {onnx_proto_schema}")

result_ = subprocess.run(
    [runner_exe, model_path, onnx_proto_schema],
    input=runner_input.encode(),
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=False
)

# Check for errors
if result_.returncode != 0:
    print(f"Error running ONNX evaluator runner (exit code {result_.returncode}):")
    print("OCaml runner STDOUT:")
    print(result_.stdout.decode())
    print("OCaml runner STDERR:")
    print(result_.stderr.decode())
    exit(1)


def parse_runner_output(output_bytes: bytes):
    """Parse the runner output into numpy arrays.
    
    The runner outputs: [[(vals, dims), ...], [(vals, dims), ...], ...]
    Each evaluation output is a list of (values_list, dims_list) tuples.
    """
    import ast
    
    output_str = output_bytes.decode().strip()
    # The output is a Python list of lists of tuples
    try:
        parsed = ast.literal_eval(output_str)
    except Exception as e:
        print(f"Failed to parse runner output: {e}")
        print(f"Output was: {output_str}")
        return []
    
    results = []
    for evaluation in parsed:
        if evaluation == "":
            continue
        out_inner = []
        # evaluation is a list of (values_list, dims_list) tuples
        for output in evaluation:
            if isinstance(output, tuple) and len(output) == 2:
                values, dims = output
                a = np.array([float(v) for v in values])
                # Reshape using dims
                if dims:
                    a = a.reshape([int(d) for d in dims])
                out_inner.append(a)
        results.append(out_inner)
    return results


# Parse runner output
rocq_results = parse_runner_output(result_.stdout)

# compare
correct = True
for i, (runtime, rocq) in enumerate(zip(runtime_outputs, rocq_results)):
    if not np.allclose(runtime, rocq):
        print(f"Mismatch at evaluation {i}")
        correct = False

print(f"Tested {model_name} on {evaluations} random inputs.")
if correct:
    print("Both the ONNX Runtime and Rocq's ONNX Evaluator return the same results on every tested input.")
    print("The Formalization seems to be correct!")
else:
    print(
        "Unfortunately, the ONNX Runtime and Rocq's ONNX Evaluator do not return the same results on every tested input.")
    print(f"The Formalization is not said the be correct! You should debug this file ({sys.argv[0]}), especially the parameters defined at the beginning.")
