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
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

Definition ZEqP : Equality.axiom Z.eqb.
Proof.
move=> x y.
apply: (iffP idP) => [|-> //]; last by rw Z.eqb_refl.
by rw -Z.eqb_eq => ->.
Qed.

HB.instance Definition _ := hasDecEq.Build Z ZEqP.

Lemma relu_canon {t out : TensorProto} :
  canon_tensor t == t -> op_relu.relu t = Success out -> canon_tensor out == out.
Proof.
move=> _; rewrite /op_relu.relu.
repeat match goal with
| |- context [match ?x with _ => _ end] => destruct x
end => //; case=> <-.
all: by [].
Qed.

Definition relu' (t : sized_tensor) : sized_tensor :=
  match t with
  | exist t' Ht' =>
      match op_relu.relu t' as r return op_relu.relu t' = r -> sized_tensor with
      | Success out => fun E =>
                         exist _ (@QTensor out (relu_canon (valP t') E)) (relu_sized _ _ Ht' E)
      | Error e => fun E =>
                     False_rect _ (notF (ecast r (isSuccess r) E (relu_success _ Ht')))
      end erefl
  end.

(* (** [op_relu.relu] on the underlying TensorProto.  The [Error] branch is never *)
(*     taken on a sized tensor (see [relu_success]). *) *)
(* Definition relu_proto (t : TensorProto) : TensorProto := *)
(*   if op_relu.relu t is Success t' then t' else t. *)

(* Lemma relu_proto_sized (t : TensorProto) : *)
(*   tensorProtoSized t -> tensorProtoSized (relu_proto t). *)
(* Proof. *)
(* move=> St; rewrite /relu_proto. *)
(* by case E: (op_relu.relu t) => [t'|e] //; exact: relu_sized St E. *)
(* Qed. *)

(* Definition relu_tp (x : sized_tensor) : sized_tensor := *)
(*   exist _ (@QTensor _ (relu_proto_canon _ (valP (val x)))) (relu_proto_sized _ (valP x)). *)

(* (** On the underlying TensorProto, [relu_tp] is exactly [op_relu.relu]. *) *)
(* Lemma relu_tpE (x : sized_tensor) : op_relu.relu (val (val x)) = Success (val (val (relu_tp x))). *)
(* Proof. *)
(* rewrite /= /relu_proto; have := relu_success _ (valP x). *)
(* by case: (op_relu.relu _). *)
(* Qed. *)

(* (** A sized tensor read as a mathcomp tensor, with the element type and the *)
(*     shape it carries. *) *)
Definition sized_sem (x : sized_tensor) : {e : Elem & T (denote e)} :=
  tensorProto_elem (val (val x)) (valP x).

Lemma relu'E (x : sized_tensor) :
  op_relu.relu (val (val x)) = Success (val (val (relu' x))).
Proof.
case: x => t' Ht'; rewrite /relu' /=.
move: (erefl (op_relu.relu t')).
case: {2 4}(op_relu.relu t') => [out|e] E //=.
by have H := relu_success _ Ht'; rewrite E in H.
Qed.

(** Reading a sized tensor as a mathcomp tensor commutes with relu. *)
Lemma relu_mono : {morph sized_sem : x / relu' x >-> interp_relu x}.
Proof.
move=> x.
move: (relu' x) (relu'E x) => y E.
case: x y E => [[t Ct] t_sized] [[out Cout] Hout] /= E.
case/tensorProtoSizedP: (t_sized) => /= dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 Ht dt_type dims_ok sized.

(* TODO: Let Katya know when this is done *)
