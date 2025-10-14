From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.
From Flocq Require Import Bits BinarySingleNaN.

From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export model.

(*relu for various datatypes*)

Definition relu_float32 (f: float32) : float32 :=
  match f with
  | Binary.B754_zero _ _ _ => f           (*f is zero*)
  | Binary.B754_infinity _ _ _ => f       (*f is infinite*)
  | Binary.B754_nan _ _ _ _ _ => f        (*f is Nan*)
  | Binary.B754_finite _ _ sign _ _ _ =>  (*f is finite*)
    match sign with
    | true => (*f is less than zero, result is zero*)
      Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 0 0 true
    | false => (*f is more or equal zero, result is f*)
      f
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
From CoqE2EAI Require Export bytes_converter.

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
              Success (TensorProto_constructor dims (int32_of_Z 1%Z) None relu [] [] [] None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type float32 must either have non-empty float_data or non-empty raw_data"
          end
        | floats =>
        let relu := map relu_float32 floats in
        Success (TensorProto_constructor dims (int32_of_Z 1%Z) None relu [] [] [] None None None [] None [] [] [])
        end

      | 6%Z => (*int32*)
        match int32 with
        | [] =>
          match raw_data with
          | Some bytes =>
            match int32_of_bytes bytes with
            | Success ints =>
              let relu := map relu_int32 ints in
              Success (TensorProto_constructor dims (int32_of_Z 1%Z) None [] relu [] [] None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type int32 must either have non-empty int32_data or non-empty raw_data"
          end
        | ints =>
        let relu := map relu_int32 ints in
        Success (TensorProto_constructor dims (int32_of_Z 1%Z) None [] relu [] [] None None None [] None [] [] [])
        end

      | 7%Z => (*int64*)
        match int64 with
        | [] =>
          match raw_data with
          | Some bytes =>
            match int64_of_bytes bytes with
            | Success ints =>
              let relu := map relu_int64 ints in
              Success (TensorProto_constructor dims (int32_of_Z 1%Z)  None [] [] [] relu None None None [] None [] [] [])
            | Error e => Error e
            end
          | None => Error "TensorProto with type int64 must either have non-empty int_data or non-empty raw_data"
          end
        | ints =>
        let relu := map relu_int64 ints in
        Success (TensorProto_constructor dims (int32_of_Z 1%Z)  None [] [] [] relu None None None [] None [] [] [])
        end
      | _ => Error "ReLU: Tensor Datatype must either be float32, int32 or int64"
      end
    | None => Error "ReLU: Tensor must have a given Datatype"
    end
  end.