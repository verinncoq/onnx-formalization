From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith Lia.
From Flocq Require Import Bits BinarySingleNaN.

From mathcomp Require Import tuple.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Import valid_types.

(*relu for various datatypes*)

Definition relu_float32 (f: float32) : float32 :=
  match f with
  | Binary.B754_zero _ => f           (*f is zero*)
  | Binary.B754_infinity sign =>      (*f is infinite*)
    match sign with
    | true => (*f is -inf, result is +0 (IEEE max(+0, -inf) = +0)*)
      Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 0 0 false
    | false => (*f is +inf, result is f*)
      f
    end
  | Binary.B754_nan _ _ _ => f        (*f is Nan*)
  | Binary.B754_finite sign _ _ _ =>  (*f is finite*)
    match sign with
    | true => (*f is less than zero, result is zero*)
      Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 0 0 false
    | false => f (*f is more or equal zero, result is f*)
    end
  end.

Definition relu_int32 (i: int32) : int32 :=
  match Z_of_int32 i with
  | Zneg _ => (Byte.x00, Byte.x00, Byte.x00, Byte.x00) (*i is less than zero, result is zero*)
  | _ => i (*i is more or equal zero, result is i*)
  end.

Definition relu_int64 (i: int64) : int64 :=
  match Z_of_int64 i with
  | Zneg _ => (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) (*i is less than zero, result is zero*)
  | _ => i (*i is more or equal zero, result is i*)
  end.

Open Scope Z_scope.
From ONNXFormalization.ONNXConverter Require Export bytes_converter.

(*Computes ReLU, as definied by ONNX*)
Definition relu (X: TensorProto) : error_option TensorProto :=
  match X with
  | TensorProto_constructor dims data_type_option _ float32 int32 _ int64 _ _ raw_data _ _ _ _ _ =>
    match data_type_option with
    | Some data_type =>
      match Z_of_int32 data_type with

      | 1%Z => (*float32*)
        match float32 with
        | [] =>
          match raw_data with
          | Some bytes =>
            match float32_of_bytes bytes with
            | Success floats =>
              let relu := map relu_float32 floats in
              Success (TensorProto_constructor dims (Some (int32_of_Z 1%Z)) None relu [] [] [] None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type float32 must either have non-empty float_data or non-empty raw_data"
          end
        | floats =>
        let relu := map relu_float32 floats in
        Success (TensorProto_constructor dims (Some (int32_of_Z 1%Z)) None relu [] [] [] None None None [] None [] [] [])
        end

      | 6%Z => (*int32*)
        match int32 with
        | [] =>
          match raw_data with
          | Some bytes =>
            match int32_of_bytes bytes with
            | Success ints =>
              let relu := map relu_int32 ints in
              Success (TensorProto_constructor dims (Some (int32_of_Z 6%Z)) None [] relu [] [] None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type int32 must either have non-empty int32_data or non-empty raw_data"
          end
        | ints =>
        let relu := map relu_int32 ints in
        Success (TensorProto_constructor dims (Some (int32_of_Z 6%Z)) None [] relu [] [] None None None [] None [] [] [])
        end

      | 7%Z => (*int64*)
        match int64 with
        | [] =>
          match raw_data with
          | Some bytes =>
            match int64_of_bytes bytes with
            | Success ints =>
              let relu := map relu_int64 ints in
              Success (TensorProto_constructor dims (Some (int32_of_Z 7%Z))  None [] [] [] relu None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type int64 must either have non-empty int_data or non-empty raw_data"
          end
        | ints =>
        let relu := map relu_int64 ints in
        Success (TensorProto_constructor dims (Some (int32_of_Z 7%Z))  None [] [] [] relu None None None [] None [] [] [])
        end
      | _ => Error "ReLU: Tensor Datatype must either be float32, int32 or int64"
      end
    | None => Error "ReLU: Tensor must have a given Datatype"
    end
  end.

(** SUGGESTED RELU **)
(* This replaces the entire file with these lines *)

Definition relu_valid {R : validType} (i : R) : R :=
  if ge0 i then i else zero.

Definition map_t {R T} (f : R -> T) (x : tensor R) : tensor T :=
  match x with
  | Tensor tdims tdata => Tensor tdims (map f tdata)
  end.

Definition relu_suggested (X: TensorProto) : error_option TensorProto :=
  apply_op (fun _ xs => Success (map_t relu_valid (thead xs))) (cons_tuple X nil).


(** * Equivalence of [relu] and [relu_suggested]

    The error messages differ, so this compares [getValue]: both succeed with
    the same tensor, or both fail. *)

Lemma relu_float32_valid (f : float32) : relu_float32 f = relu_valid f.
Proof. now destruct f as [[]|[]|s pl H|[] m e H]. Qed.

Lemma relu_int32_valid (i : int32) : relu_int32 i = relu_valid i.
Proof. unfold relu_int32, relu_valid; cbn; unfold ge0_int32. now destruct (Z_of_int32 i). Qed.

Lemma relu_int64_valid (i : int64) : relu_int64 i = relu_valid i.
Proof. unfold relu_int64, relu_valid; cbn; unfold ge0_int64. now destruct (Z_of_int64 i). Qed.

Theorem relu_equiv (X : TensorProto) :
  getValue (relu X) = getValue (relu_suggested X).
Proof.
  destruct X as [dims [t|] seg f32 i32 sd i64 nm doc raw ext loc f64 u64 meta].
  2: reflexivity.
  unfold relu_suggested, apply_op, same_dtype, dispatch; cbn -[Z_of_int32].
  rewrite Z.eqb_refl; cbn -[Z_of_int32].
  unfold relu.
  generalize (Z_of_int32 t) as z; intro z.
  destruct z as [|p|p]; try reflexivity.
  repeat (destruct p as [p|p|]; try reflexivity).
  all: cbn; destruct f32, i32, i64, raw as [b|]; cbn; try reflexivity;
       repeat match goal with
       | |- context [match ?e with Success _ => _ | Error _ => _ end] => destruct e
       end; cbn; try reflexivity.
  all: unfold float32_to_tensor, int32_to_tensor, int64_to_tensor;
       rewrite ?(map_ext _ _ relu_float32_valid), ?(map_ext _ _ relu_int32_valid),
               ?(map_ext _ _ relu_int64_valid), ?relu_float32_valid, ?relu_int32_valid,
               ?relu_int64_valid; reflexivity.
Qed.
