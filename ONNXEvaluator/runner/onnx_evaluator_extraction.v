From Stdlib Require Import Extraction extraction.ExtrOcamlNativeString.
From ONNXFormalization.ONNXEvaluator Require Import evaluator_bridge.

Extraction "rocq_onnx_evaluator.ml" evaluate.
