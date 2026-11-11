From mathcomp Require Import boot algebra order reals.
From mathcomp Require Import interval_inference tensor.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics real.
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem inst_reals.
From ONNXFormalization.VNNLIB.Core Require Import Syntax Semantics.
From ONNXFormalization.VNNLIB Require Import VNNLIB.

Definition query : Type := VNNLIBQuery syntax_inst.

Definition interp_query : @QuerySemantics syntax_inst
  := interpVNNLIBQuery syntax_inst semantics_inst.

From Stdlib Require Import Rdefinitions.
From mathcomp Require Import Rstruct.

Definition real_query : Type := RealVNNLIBQuery syntax_inst R.

Definition interp_real_query := interpRealVNNLIBQuery syntax_inst R realSemantics.
