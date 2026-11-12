import subprocess
import sys
import os

import onnxruntime as ort
import numpy as np


# use standard parameters
evaluations = 10  # number of evaluations
model_path = "../cartpole.onnx"  # path to the ONNX model
onnx_proto_schema = "../onnx.proto"  # path to ONNX protobuf schema

# exactly one argument is invalid
if len(sys.argv) < 3:
    print(f"Usage: {sys.argv[0]} <number_evaluations> <model_path> [onnx_proto_schema]")
    exit()

# if arguments are given
if len(sys.argv) >= 3:
    # use parameters from command line inputs
    evaluations = int(sys.argv[1])
    model_path = sys.argv[2]
    if len(sys.argv) > 3:
        onnx_proto_schema = sys.argv[3]

session = ort.InferenceSession(model_path)  # set up a runtime session
print("\n\n\n\n\n\n!!!!!!!!!\n:) Please ignore all 'Schema error:' messages with the same file and line number, they are harmless :)\n!!!!!!!!!\n\n\n\n\n\n")

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
    # repr(float(v)) is the shortest string that parses back to the exact same
    # float64; since v came from a float32, the runner's float_of_string +
    # Int32.bits_of_float then recover the original float32 bit pattern.
    # (The previous "%.6f" rounded inputs to 6 decimals, so the evaluator was
    # tested on different values than ONNX Runtime.)
    values_str = ",".join([repr(float(v)) for v in values])
    dims_str = ",".join([str(d) for d in dims])
    return f"{input_name}|{values_str}|{dims_str}"


# Serialize all inputs for the runner
# Format: One line per evaluation, inputs separated by ';'
# (the runner splits each line on ';', so a multi-char separator like ';;'
# would leave an empty segment and fail with "Invalid input format")
# Each input: name|value1,value2,...|dim1,dim2,...
runner_input_lines = []
for inputs_per_evaluation in inputs:
    input_strs = []
    for input_nr, input_array in enumerate(inputs_per_evaluation):
        values, dims = array_to_string_list(input_array)
        input_strs.append(format_input_for_runner(input_names[input_nr], values, dims))
    runner_input_lines.append(";".join(input_strs))

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


def parse_rocq_runner_output(output_bytes: bytes):
    """Parse the Rocq runner output into numpy arrays.

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
        if isinstance(evaluation, str):
            # The runner reports per-evaluation errors as plain strings, e.g. "Error: ..."
            print(f"Rocq ONNX runner error: {evaluation}")
            results.append([])
            continue
        out_inner = []
        # evaluation is a list of (values_list, dims_list) tuples
        for output in evaluation:
            if isinstance(output, str):
                print(f"Rocq ONNX runner error: {output}")
                continue
            if isinstance(output, tuple) and len(output) == 2:
                values, dims = output
                a = np.array([float(v) for v in values])
                # Reshape using dims
                if dims:
                    a = a.reshape([int(d) for d in dims])
                out_inner.append(a)
        results.append(out_inner)
    return results


# Parse Rocq runner output
runner_output = result_.stdout
rocq_results = parse_rocq_runner_output(runner_output)

# compare
correct = True
if len(rocq_results) != len(runtime_outputs):
    print(f"Runner returned {len(rocq_results)} evaluation results, expected {len(runtime_outputs)}")
    correct = False
for i, (runtime, rocq) in enumerate(zip(runtime_outputs, rocq_results)):
    print("-------------------------------------------------------------------------")
    print("ROCQ:         ", rocq)
    print("ONNX Runtime: ", runtime)
    print("-------------------------------------------------------------------------")
    # Compare per output tensor with explicit shape check: np.allclose alone
    # raises ValueError on non-broadcastable shapes (e.g. runner error -> [])
    same = len(runtime) == len(rocq) and all(
        r.shape == c.shape and np.allclose(r, c) for r, c in zip(runtime, rocq)
    )
    if not same:
        print(f"Mismatch at evaluation {i}")
        correct = False

print(f"Tested model {model_path} on {evaluations} random inputs.")
if correct:
    print("Both the ONNX Runtime and Rocq's ONNX Evaluator return approximately the same results on every tested input.")
    print("The Formalization seems to be correct!")
else:
    print(
        "Unfortunately, the ONNX Runtime and Rocq's ONNX Evaluator do not return the same results on every tested input.")
    print(f"The Formalization is not said the be correct! You should debug this file ({sys.argv[0]}), especially the parameters defined at the beginning.")
    exit(1)
