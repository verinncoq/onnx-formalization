From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.

(********************************************)
(******** QUOTIENT BY RELEVANT DATA *********)
(********************************************)

(** A TensorProto carries one data field per storage class, but only the one
 selected by its data_type enum is meaningful. Two TensorProtos are identified
 when they have the same data_type and agree on that field; all other fields
 are ignored. The mapping from data_type to field follows onnx.proto. **)

Inductive tensor_storage :=
| FloatStorage   (* float_data:  FLOAT, COMPLEX64 *)
| Int32Storage   (* int32_data:  UINT8, INT8, UINT16, INT16, INT32, BOOL, FLOAT16,
                    BFLOAT16, FLOAT8*, UINT4, INT4, FLOAT4E2M1 *)
| StringStorage  (* string_data: STRING *)
| Int64Storage   (* int64_data:  INT64 *)
| DoubleStorage  (* double_data: DOUBLE, COMPLEX128 *)
| UInt64Storage  (* uint64_data: UINT32, UINT64 *)
| NoStorage.     (* UNDEFINED, missing or unknown data_type *)

Definition storage_of (data_type : option int32) : tensor_storage :=
  match data_type with
  | None => NoStorage
  | Some d =>
      match Z_of_int32 d with
      | 1%Z | 14%Z => FloatStorage
      | 2%Z | 3%Z | 4%Z | 5%Z | 6%Z | 9%Z | 10%Z | 16%Z
      | 17%Z | 18%Z | 19%Z | 20%Z | 21%Z | 22%Z | 23%Z => Int32Storage
      | 8%Z => StringStorage
      | 7%Z => Int64Storage
      | 11%Z | 15%Z => DoubleStorage
      | 12%Z | 13%Z => UInt64Storage
      | _ => NoStorage
      end
  end.

(** Canonical representative: keep data_type and the field it selects, and
 reset every other field to its default. **)
Definition canon_tensor (t : TensorProto) : TensorProto :=
  match t with
  | TensorProto_constructor dims dt _ fd i32d sd i64d _ _ _ _ _ dd u64d _ =>
      let mk fd i32d sd i64d dd u64d :=
        TensorProto_constructor dims dt None fd i32d sd i64d None None None nil None dd u64d nil in
      match storage_of dt with
      | FloatStorage  => mk fd  nil  nil nil  nil nil
      | Int32Storage  => mk nil i32d nil nil  nil nil
      | StringStorage => mk nil nil  sd  nil  nil nil
      | Int64Storage  => mk nil nil  nil i64d nil nil
      | DoubleStorage => mk nil nil  nil nil  dd  nil
      | UInt64Storage => mk nil nil  nil nil  nil u64d
      | NoStorage     => mk nil nil  nil nil  nil nil
      end
  end.

Lemma canon_tensorK (t : TensorProto) : canon_tensor (canon_tensor t) = canon_tensor t.
Proof.
case: t => ? dt *; rewrite /canon_tensor.
by case E: (storage_of dt); rewrite E.
Qed.

(** Equivalence on TensorProto: same data_type and same relevant data. **)
Definition tensor_eqmod : rel TensorProto :=
  fun t1 t2 => canon_tensor t1 == canon_tensor t2.

Local Open Scope quotient_scope.

Record qTensor := QTensor {
  qtensor_val :> TensorProto;
  _ : canon_tensor qtensor_val == qtensor_val
}.

HB.instance Definition _ := [isSub for qtensor_val].
HB.instance Definition _ := [Equality of qTensor by <:].

Definition qtensor_pi (t : TensorProto) : qTensor :=
  @QTensor (canon_tensor t) (introT eqP (canon_tensorK t)).

Lemma qtensor_reprK : cancel qtensor_val qtensor_pi.
Proof. by move=> q; apply: val_inj => /=; apply/eqP; case: q. Qed.

HB.instance Definition _ := isQuotient.Build TensorProto qTensor qtensor_reprK.

Lemma qtensor_pi_eq : {mono \pi_qTensor : x y / tensor_eqmod x y >-> x == y}.
Proof. by move=> x y; rewrite unlock -val_eqE. Qed.

Lemma qtensor_reprE (t : TensorProto) : repr (\pi_qTensor t) = canon_tensor t.
Proof. by rewrite !unlock. Qed.

HB.instance Definition _ := isEqQuotient.Build TensorProto tensor_eqmod qTensor qtensor_pi_eq.

Lemma qtensor_eqmodP (x y : TensorProto) :
  reflect (x = y %[mod qTensor]) (tensor_eqmod x y).
Proof. by rewrite -qtensor_pi_eq; apply: eqP. Qed.
