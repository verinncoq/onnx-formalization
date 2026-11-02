From mathcomp Require Import boot algebra order reals.
From mathcomp Require Import interval_inference tensor.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics real.
From ONNXFormalization.VNNLIB.Core Require Import Syntax Semantics.

Section VNNLIB.
Variable onnxSyntax : NetworkTheorySyntax.
Variable onnxSemantics : NetworkTheorySemantics onnxSyntax.

Definition VNNLIBQuery : Type := @Query onnxSyntax.

Definition interpVNNLIBQuery : @QuerySemantics onnxSyntax := query onnxSemantics.

Variable R : realType.

Definition RealVNNLIBQuery : Type := @Query (@realSyntax onnxSyntax R).

Definition interpRealVNNLIBQuery
  (realNetworkSemantics : @RealNetworkSemantics onnxSyntax R) :
  @QuerySemantics (@realSyntax onnxSyntax R)
  := (query (realSemantics realNetworkSemantics)).

End VNNLIB.
