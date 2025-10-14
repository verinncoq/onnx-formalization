import subprocess
import sys
import numpy as np
import os

# check for correct number of arguments
if len(sys.argv) != 3:
    print("Expected 2 argument(s) instead of", len(sys.argv) - 1)
    print("Please use the following program call:", sys.argv[0], "<model_name> <output_type>")
    exit()

model_name = sys.argv[1]
output_type = sys.argv[2]

if output_type == "verification_model":
    used_converter = "onnx_converter"
elif output_type == "onnx_model":
    used_converter = "onnx_converter_to_onnx_model"
else:
    used_converter = ""

# create rocq file

roqc_file = f"""
From Coq Require Import Strings.String.
From CoqE2EAI Require Export net.
From CoqE2EAI Require Export onnx_converter.

Redirect "{model_name}" Compute {used_converter} {model_name}.
"""

# write file

with open("convert_net.v", "w") as f:
    f.write(roqc_file)

result_ = subprocess.run(['coqc', '-w', 'none', '-R', './target', 'CoqE2EAI', './convert_net.v'],
                         stdout=subprocess.PIPE)

# remove files
os.remove(".convert_net.aux")
os.remove("convert_net.glob")
os.remove("convert_net.v")
os.remove("convert_net.vo")
os.remove("convert_net.vok")
os.remove("convert_net.vos")


# format output
