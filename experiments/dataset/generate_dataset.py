import torch
from torch import nn

DEFAULT_WIDTH = 4
LAYER_RANGE = range(1,16)

example_input = (torch.randn(1,DEFAULT_WIDTH))

for l in LAYER_RANGE:
    layers = []
    for i in range(l):
        linear = nn.Linear(DEFAULT_WIDTH, DEFAULT_WIDTH)
        relu = nn.ReLU()
        layers.extend([linear, relu])
    layers.append(nn.Linear(DEFAULT_WIDTH, DEFAULT_WIDTH))
    net = nn.Sequential(*layers)
    onnx = torch.onnx.export(net, example_input, dynamo=True)
    onnx.save(f"experiments\\dataset\\testmodel{l}.onnx")

