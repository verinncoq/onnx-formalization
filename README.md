# ONNX meets VNN-LIB in Rocq: Bridging Execution, Verification and Formalisation of Neural Networks

This repository contains **ONNX Formal Core (ONNX^FC)**, a mechanisation of the ONNX neural network format in Rocq. It makes an ONNX network a formal object that proofs can reason about, and links it to VNN-LIB, the community standard for neural network verification queries.

ONNX^FC has three layers:

* **Syntax.** The Rocq types for ONNX models (`ONNXConverter/theory/model.v`, with `conversion_functions.v`) are generated from the ONNX Protobuf schema by the *Protobuf converter* (`ProtobufConverter/`). The mapping from Protobuf to Rocq data types is in `ProtobufConverter/theory/type_converter.v`.
* **Evaluator.** An executable evaluator for ONNX models (`ONNXEvaluator/`). Like a runtime, it may fail on a model, and it then returns an error message.
* **Verification semantics.** Well-formedness of ONNX models (`VNN-LIB/ONNX/well_formed_model.v`), and floating-point (`inst_sem.v`) and real-valued (`inst_reals.v`) semantics of well-formed models. These are instances of VNN-LIB's abstract network theory (`VNN-LIB/Core/`); `VNN-LIB/VNNLIB_inst.v` gives the resulting VNN-LIB queries over ONNX models.

The repository also contains an updated import of ONNX models into Rocq-NN-Roll (`ONNXConverter/`). It is built on the generated syntax, and `ONNXConverter/theory/isomorphism.v` relates the edges of an imported ONNX graph to those of the resulting Rocq-NN-Roll network.

## Build

### Prerequisites

* [Rocq Platform 2026.07.0](https://github.com/rocq-prover/platform/releases/tag/2026.07.0), which provides Rocq, OCaml, Dune and opam.
* `protoc`, the Protocol Buffers compiler, which the runners call to decode binary `.onnx` files.
* For differential testing: [Python](https://www.python.org/) with `numpy` and [onnxruntime](https://onnxruntime.ai/) (tested with Python 3.14.4 and onnxruntime 1.23).

### Install dependencies (once)

```bash
opam install . --deps-only
```

### Build

```bash
dune build
```

## Usage

Run all commands from the repository root after `dune build`.

### Generate the syntax from the Protobuf schema

```bash
dune exec ./ProtobufConverter/runner/rocq_protobuf_runner.exe \
  ./data/onnx.modified.proto \
  ./out
```

*Arguments: Protobuf schema, output directory.* Writes `model.v` and `conversion_functions.v` to the output directory. `data/onnx.modified.proto` is the ONNX schema with the changes listed at its top (for example, nested subgraphs removed).

### Import an ONNX model into Rocq-NN-Roll

```bash
dune exec ./ONNXConverter/runner/onnx_converter_runner.exe \
  ./data/cartpole.onnx \
  ./out/cartpole.v \
  ./data/onnx.proto
```

*Arguments: ONNX model, output Rocq file, ONNX Protobuf schema.* `out/cartpole_reference.v` is a reference output.

### Differential testing

The differential-testing framework runs the extracted evaluator and a reference runner on the same random inputs and compares their outputs. Any runner can be added to it; the repository illustrates it with ONNX Runtime (`ONNXEvaluator/comparer/comparer.py`).

Test one model:

```bash
python3 ./ONNXEvaluator/comparer/comparer.py \
  20 \
  ./data/cartpole.onnx \
  ./data/onnx.proto
```

*Arguments: number of random inputs, ONNX model, ONNX Protobuf schema.*

Test all models in `experiments/output_comparison/dataset/` (5 random inputs each):

```bash
dune test
```

## License

Apache 2.0, see `LICENSE`.
