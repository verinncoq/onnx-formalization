Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import boot algebra order reals Rstruct.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Lia Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst real.
From ONNXFormalization.VNNLIB.ONNX Require Export well_formed_model.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

(********************************************)
(**************** SYNTAX ********************)
(********************************************)

Definition nodeOutput (y : NetworkType Elem) (m' : well_formed_model y) (s : string)
(d : TensorType Elem) : eqType :=
match m' with
| exist m _ =>
    { v : ValueInfoProto |
      [&& v \in graph_outputs m, value_info_name v == s & value_has_type d v]}
end.

(*
A function that maps a model to a list of its outputs.
For every declared output type at position i in the network shape y, this
looks up the model's actual list of graph outputs (ModelProto -> GraphProto
-> list ValueInfoProto) at that same position, and pairs that output's name
with the NodeProto that produces it.
*)

(** The network type's outputs line up one-to-one with the graph outputs. **)
Lemma network_dim_match_size {y : NetworkType Elem} {m : ModelProto} :
  network_dim_match m y -> size (outputs Elem y) = size (graph_outputs m).
Proof.
case: y => [[inps Hin] [outs Hout]] /= /andP [_].
by rewrite all2E => /andP [/eqP].
Qed.

(** The graph output at the same position as the i-th declared output. **)
Definition mOutput_value {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) : ValueInfoProto :=
  tnth (in_tuple (graph_outputs m)) (cast_ord (network_dim_match_size H) i).

Lemma mOutput_valueP {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) :
  let v := mOutput_value H i in
  let d := tnth (in_tuple (outputs Elem y)) i in
  [&& v \in graph_outputs m, value_info_name v == value_info_name v & value_has_type d v].
Proof.
rewrite /mOutput_value eqxx /=.
move: (network_dim_match_size H) => E; move: i E H.
case: y => [[inps Hin] [outs Hout]] /= i E /andP [_].
rewrite all2E => /andP [_ /all_nthP outsame].
rewrite mem_tnth /=.
set v := tnth (in_tuple (graph_outputs m)) (cast_ord E i).
set o := tnth (in_tuple outs) i.
have := outsame (o, v) i.
rewrite nth_zip_cond size_zip -[in minn _ _]E minnn ltn_ord /= => /(_ isT).
rewrite -[nth o outs i](tnth_nth o (in_tuple outs) i).
rewrite -[nth v _ i](tnth_nth v (in_tuple (graph_outputs m)) (cast_ord E i)) -/v -/o.
by move=> ->.
Qed.

(** For each out in the graphproto.outputs, find the valueInfoProto  **)
Definition mOutputs (y : NetworkType Elem) (m : well_formed_model y) :
  {dffun forall i : 'I_(size (outputs Elem y)),
 {u : string & nodeOutput y m u (tnth (in_tuple (outputs Elem y)) i)}} :=
  match m as m0 return
    {dffun forall i : 'I_(size (outputs Elem y)),
      {u : string & nodeOutput y m0 u (tnth (in_tuple (outputs Elem y)) i)}}
  with
  | exist m0 H =>
      finfun (fun i : 'I_(size (outputs Elem y)) =>
        let v := mOutput_value (andP H).1 i in
        existT _ (value_info_name v) (exist _ v (mOutput_valueP (andP H).1 i)))
  end.

(** TODO: mOutputs and nodeOutput are wrong. NodeOutput should only be
constructable if there is a node output and modl output should only contain
valid model output. Fix Model so that it holds enough information to construct
this. NodeOutput should be an inductive type that points to constructors **)

(** Ignores renaming and reordering, graph isomorphism problem. **)
Definition is_iso (y1 y2 : NetworkType Elem) (m1 : well_formed_model y1)
(H : NetworkShapesMatch y1 y2) (m2 : well_formed_model y2) : bool :=
match m1, m2 with
| exist (ModelProto_constructor _ _ _ _ _ _ _ x _ _ _ _) _,
  exist (ModelProto_constructor _ _ _ _ _ _ _ x' _ _ _ _) _ =>
    match x, x' with
    | Some y, Some y' =>
        match y, y' with
        | GraphProto_constructor n _ _ _ _ _ _ _ _ _,
          GraphProto_constructor n' _ _ _ _ _ _ _ _ _ => n == n'
        end
    | _, _ => false
    end
end.

Definition syntax_inst : NetworkTheorySyntax :=
  {|
      ElementType := Elem;
      TheoryTensor := well_formed_tensor;
      Model := well_formed_model;
      NodeOutputName := string;
      NodeOutput := nodeOutput;
      modelOutputs := mOutputs;
      iso := is_iso;
  |}.
