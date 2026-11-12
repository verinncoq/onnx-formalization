import os

import torch
from torch import nn

DEFAULT_WIDTH = 4
LAYER_RANGE = range(1, 16)
# Must match the only opset the Rocq evaluator accepts
# (ONNXEvaluator/theory/onnx_evaluator.v: "Only 23 is supported")
REQUIRED_OPSET = 23

script_dir = os.path.dirname(os.path.abspath(__file__))
example_input = torch.randn(1, DEFAULT_WIDTH)

for l in LAYER_RANGE:
    layers = []
    for i in range(l):
        linear = nn.Linear(DEFAULT_WIDTH, DEFAULT_WIDTH)
        relu = nn.ReLU()
        layers.extend([linear, relu])
    layers.append(nn.Linear(DEFAULT_WIDTH, DEFAULT_WIDTH))
    net = nn.Sequential(*layers)
    exported = torch.onnx.export(net, example_input, dynamo=True, opset_version=REQUIRED_OPSET)
    # Enforce the opset at generation time: fail instead of writing a model
    # the evaluator would reject.
    versions = [op.version for op in exported.model_proto.opset_import]
    if versions != [REQUIRED_OPSET]:
        raise RuntimeError(
            f"testmodel{l}: exported with opset_import versions {versions}, "
            f"expected [{REQUIRED_OPSET}]"
        )
    exported.save(os.path.join(script_dir, f"testmodel{l}.onnx"))

