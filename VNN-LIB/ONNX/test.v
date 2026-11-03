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
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem inst_reals.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

Definition empty_model : ModelProto :=
  ModelProto_constructor None nil None None None None None None nil nil nil nil.

(* Type checks *)
Definition test := onnx_evaluator empty_model nil.

Compute test.

Lemma Hprec32 : FLX.Prec_gt_0 24. Proof. reflexivity. Qed.
Lemma Hmax32  : BinarySingleNaN.Prec_lt_emax 24 128. Proof. reflexivity. Qed.

Definition f32 (n : Z) : binary32 :=
  Binary.binary_normalize 24 128 Hprec32 Hmax32 BinarySingleNaN.mode_NE n 0 false.

Definition W1 : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 2; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 2; f32 1; f32 (-1); f32 1] nil nil nil (Some """W1"""%string) None None nil None nil nil nil.

Definition W2 : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """W2"""%string) None None nil None nil nil nil.

(** x : float[1,2] --Gemm(W1, transB=1)--> z --Relu--> v --Gemm(W2, transB=1)--> y : float[1,1] *)
Definition g : GraphProto :=
  let float_ty := Some (int32_of_Z 1) in
  let vinfo nm (ds : seq Z) :=
    ValueInfoProto_constructor (Some nm)
      (Some (TypeProto_constructor
               (Some (tensor_type_value_TypeProto
                        (Tensor_TypeProto_constructor float_ty
                           (Some (TensorShapeProto_constructor
                                    [seq Dimension_TensorShapeProto_constructor
                                         (Some (dim_value_value_Dimension_TensorShapeProto (int64_of_Z d))) None
                                    | d <- ds]))))) None))
      None nil in
  let transB1 :=
    AttributeProto_constructor (Some """transB"""%string) None None (Some INT_AttributeProto)
      None (Some (int64_of_Z 1)) None None None None nil nil nil nil nil nil in
  let gemm a b out :=
    NodeProto_constructor [:: a; b] [:: out] None (Some """Gemm"""%string) None None
      [:: transB1] None nil nil in
  let relu a out :=
    NodeProto_constructor [:: a] [:: out] None (Some """Relu"""%string) None None
      nil None nil nil in
  GraphProto_constructor
    [:: gemm """x"""%string """W1"""%string """z"""%string;
        relu """z"""%string """v"""%string;
        gemm """v"""%string """W2"""%string """y"""%string]
    None
    [:: W1; W2]
    nil
    None
    [:: vinfo """x"""%string [:: 1; 2]%Z]
    [:: vinfo """y"""%string [:: 1; 1]%Z]
    [:: vinfo """z"""%string [:: 1; 2]%Z; vinfo """v"""%string [:: 1; 2]%Z]
    nil nil.

Definition model : ModelProto :=
  ModelProto_constructor None nil None None None None None (Some g) nil nil nil nil.

(* Compute (onnx_evaluator model). *)

Definition x : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """x"""%string) None None nil None nil nil nil.

Definition emap {T T'} (f : T -> T') (x : error_option T) : error_option T' :=
match x with
| Success x => Success (f x)
| Error x => Error x
end.

Definition ebind {T T'} (x : error_option T) (f : T -> error_option T') : error_option T' :=
match x with
| Success x' => f x'
| Error x => Error x
end.

Definition eapp {T T'} (f : error_option (T -> T')) (x : error_option T) :
  error_option T' :=
match f with
| Success f' => match x with
             | Success x' => Success (f' x')
             | Error x => Error x
             end
| Error x => Error x
end.

Definition toy_dnn (x : TensorProto) : error_option TensorProto :=
  let W1 := TensorProto_constructor [:: int64_of_Z 2; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 2; f32 1; f32 (-1); f32 1] nil nil nil (Some """W1"""%string) None None nil None nil nil nil in
  let W2 := TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """W2"""%string) None None nil None nil nil nil in
  emap tensor_of_matrix_float32 (ebind (emap (map (map relu_float32)) (ebind (matrix_float32_of_tensor x) (fun x =>
                                                                                                             ebind (matrix_float32_of_tensor W1) (fun y => gemm_float32 x y [:: [:: f32 0]] (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::])))) (fun x => ebind (matrix_float32_of_tensor W2) (fun y => gemm_float32 x y [:: [:: f32 0]] (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::]))).

Definition toy_dnn' {R : numFieldType}
  (x : 'nT[R]_([tuple 1%:posnat; 2%:posnat]))
  : 'nT[R]_([tuple 1%:posnat; 1%:posnat]) :=
  let W1 := \matrix_(i < 2, j < 2) nth 0%R (nth [::] [:: [:: 2%R; 1%R]; [:: -1; 1]]%R i) j in
  let W2 := \matrix_(i < 1, j < 2) nth 0%R [:: -1; 2]%R i in
    (map_mx (fun x => if 0%R < x then x else 0%R) (x *m W1^T)) *m W2^T.



(* Lemma result (x : sized_tensor) : *)
(*   forall x', (matrix_float32_of_tensor (val x)) = Success x' -> *)
(*         forall W1', (matrix_float32_of_tensor W1) = Success W1' -> *)
(*                forall W2', (matrix_float32_of_tensor W2) = Success W2' -> *)
(*                       let x'' := (smap tensor_of_matrix_float32 (gemm_float32 x' W1' [:: [:: f32 0]] *)
(*                                                                    (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::])) in *)
(*   onnx_evaluator model [:: (val (val x))] = smap (fun x => cons (tensor_of_matrix_float32 x) [::]) *)
(*   (sbind (fun a => gemm_float32 a W2' [:: [:: f32 0]] *)
(*   (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::]) (sbind matrix_float32_of_tensor (x''))) *)
(*  . *)
(* Proof. *)
