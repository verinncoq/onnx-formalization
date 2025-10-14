#Import os Library
import os

num_files = 0
d = {}

def count_datatype(onnx_file):
    for line in onnx_file.splitlines():
        line = line.strip()
        if line.startswith("data_type") or line.startswith("elem_type"):
            datatype = line.split()[1]
            if datatype in d:
                d[datatype] += 1
            else:
                d[datatype] = 1

print("Searching for .onnx files...")

# Travels through the directory and counts the onnx files
for (root,dirs,files) in os.walk('models',topdown=True):
    for file in files:
        if file.endswith(".onnx"):
            num_files += 1

print(f"Found {num_files} .onnx files!")
print("Decoding .onnx files...")
decoded = 0
print(f"{decoded} / {num_files}")

# Travels through the directory and decodes .onnx files
for (root,dirs,files) in os.walk('models',topdown=True):
    for file in files:
        if file.endswith(".onnx"):
            path = os.path.join(root, file)
            os.system(f"protoc --decode=onnx.ModelProto onnx.proto < {path} > {path}.decoded")
            decoded += 1
            print(f"{decoded} / {num_files}")          


print("Counting datatypes...")
counted = 0
print(f"{counted} / {num_files}")

# Travels through the directory and counts the datatypes
for (root,dirs,files) in os.walk('models',topdown=True):
    for file in files:
        if file.endswith(".decoded"):
            path = os.path.join(root, file)
            with open(path, encoding="utf-8", errors="replace") as f:
                count_datatype(f.read())
                counted += 1
                print(f"{counted} / {num_files}")
          

print(d)
