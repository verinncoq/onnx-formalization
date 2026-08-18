import subprocess
import sys
import onnxruntime as ort
import numpy as np
import os
    

# use standard parameters
evaluations = 10  # number of evaluations
model_path = "../cartpole.onnx"  # path to the ONNX model
model_name = "cartpole"  # name of the model, which must be defined as a string in Rocq


# exactly one argument is invalid
if len(sys.argv) <= 3:
    print(f"Please give either zero parameters or more than one (sys.argv[0] <number_evaluations> <model_path> <neural_network_name>).")
    exit()

# if more than one argument is given
if len(sys.argv) > 3:
    # use parameters from command line inputs
    evaluations = int(sys.argv[1])
    model_path = sys.argv[2]
    model_name = sys.argv[3]


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

# create rocq file

roqc_file = """
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export test_enviroment_helper.
From CoqE2EAI Require Export net.

"""


def array_to_rocq_list(a: np.ndarray):
    value_list = "["
    l = list(a.flatten())
    for value in l:
        value_list += f'"{value:.6f}";'
    value_list = value_list[:-1]
    value_list += "]"
    dim_list = "["
    for dim in list(a.shape):
        dim_list += f'"{dim}";'
    dim_list = dim_list[:-1]
    dim_list += "]"
    return value_list, dim_list


for evaluation, inputs_per_evaluation in enumerate(inputs):
    roqc_file += f"(*evaluation {evaluation}*)\n"
    roqc_file += f"Definition inputs_{evaluation} := ["
    for input_nr, input_ in enumerate(inputs_per_evaluation):
        roqc_file += "("
        roqc_file += f'"""{input_names[input_nr]}""", '
        value_list, dim_list = array_to_rocq_list(input_)
        roqc_file += f"{value_list}, {dim_list}"
        roqc_file += ")"
    roqc_file += f"].\n"
    roqc_file += f"Compute onnx_evaluator_wrapper_reformatter (evaluate {model_name} inputs_{evaluation}).\n\n"

# write file
with open("evaluations.v", "w") as f:
    f.write(roqc_file)

# compile file
result_ = subprocess.run(['coqc', '-w', 'none', '-R', './../target', 'CoqE2EAI', './evaluations.v'],
                         stdout=subprocess.PIPE)

# remove files
os.remove(".evaluations.aux")
os.remove("evaluations.glob")
os.remove("evaluations.v")
os.remove("evaluations.vo")
os.remove("evaluations.vok")
os.remove("evaluations.vos")


def reformat_coqc_out(b: bytes):
    results = str(b).split("= Success")
    results.pop(0)
    out = []
    for result in results:
        result = result.replace("\\r\\n", "")
        result = result.replace(": error_option string", "")
        result = result.replace('"', "")
        result = result.replace("'", "")
        result = result.replace("\\n", "")
        result = result.strip()
        t = eval(result)
        out.append(t)
    return out


def rocq_to_numpy_arrays(b: bytes):
    reformatted = reformat_coqc_out(b)
    out = []
    for evaluation in reformatted:
        out_inner = []
        for output in evaluation:
            a = np.array(output[0])
            a.reshape(output[1])
            out_inner.append(a)
        out.append(out_inner)
    return out


# get rocq results
rocq_results = rocq_to_numpy_arrays(result_.stdout)

# compare
correct = True
for runtime, rocq in zip(runtime_outputs, rocq_results):
    if not np.allclose(runtime, rocq):
        correct = False

print(f"Tested {model_name} on {evaluations} random inputs.")
if correct:
    print("Both the ONNX Runtime and Rocq's ONNX Evaluator return the same results on every tested input.")
    print("The Formalization seems to be correct!")
else:
    print(
        "Unfortunately, the ONNX Runtime and Rocq's ONNX Evaluator do not return the same results on every tested input.")
    print(f"The Formalization is not said the be correct! You should debug this file ({sys.argv[0]}), especially the parameters defined at the beginning.")

