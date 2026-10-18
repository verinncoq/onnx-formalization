#!/usr/bin/env python3
import os
import subprocess
import sys

# Get the directory where this script is located
script_dir = os.path.dirname(os.path.abspath(__file__))

# Find the project root by looking for the .git directory or dune-project file
# Dune copies files to _build/ and runs them from there, so we cannot rely on
# hardcoded relative paths from this script's location.
def find_project_root(start_path):
    current = start_path
    while True:
        # Check for dune-project file
        dune_project = os.path.join(current, 'dune-project')
        if os.path.exists(dune_project):
            return current
        # Check for .git directory
        git_dir = os.path.join(current, '.git')
        if os.path.exists(git_dir):
            return current
        parent = os.path.dirname(current)
        if parent == current:  # Reached root
            raise Exception("Could not find project root")
        current = parent

project_root = find_project_root(script_dir)

# Paths relative to project root
comparer_path = os.path.join(project_root, 'ONNXEvaluator', 'comparer', 'comparer.py')
dataset_dir = os.path.join(project_root, 'experiments', 'output_comparison', 'dataset')

# Save original directory
original_dir = os.getcwd()

try:
    # Change to project root - comparer.py expects to run from there
    os.chdir(project_root)
    
    # Process each ONNX file in the dataset
    for filename in sorted(os.listdir(dataset_dir)):
        if filename.endswith('.onnx'):
            full_path = os.path.join(dataset_dir, filename)
            onnx_proto_path = os.path.join('data', 'onnx.proto')
            result = subprocess.run([
                sys.executable, comparer_path,
                '10',
                full_path,
                onnx_proto_path
            ], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if result.returncode != 0:
                print(result.stdout, end='')
                print("!!!!!!!=============DIFFERENTIAL TESTS FAILED ON " + filename +  "=============!!!!!!!")
                sys.exit(result.returncode)
            print("FILE TESTED: " + filename)

    print("DIFFERENTIAL TESTS PASSED! :)")
    
finally:
    # Restore original directory
    os.chdir(original_dir)
