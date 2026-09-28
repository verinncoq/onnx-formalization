From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Export matrices.

From Flocq Require Import Bits BinarySingleNaN.
Definition default_minus_one := Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE (-1)%Z 0 false.

Definition neg_tensor (A : TensorProto) : error_option TensorProto :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
    match data_type_A_option with
    | Some data_type_A =>
      match (Z_of_int32 data_type_A) with
      | 1 => (*float32*)
          Success (TensorProto_constructor dims_A (int32_of_Z 1%Z) None (scale_list_float32 float32_A default_minus_one) [] [] [] None None None [] None [] [] [])
      | 6 => (*int32*)
          match int32_of_Z (-1)%Z with
          | Some i =>
              match scale_list_int32 int32_A i with
              | Success x =>
                  Success (TensorProto_constructor dims_A (int32_of_Z 6%Z) None [] x [] [] None None None [] None [] [] [])
              | Error e => Error e
              end
          | _ => Error "Neg: Scaling by -1 caused an overflow"
          end
      | 7 => (*int64*)
          match int64_of_Z (-1)%Z with
          | Some i =>
              match scale_list_int64 int64_A i with
              | Success x =>
                  Success (TensorProto_constructor dims_A (int32_of_Z 7%Z) None [] [] [] x None None None [] None [] [] [])
              | Error e => Error e
              end
          | _ => Error "Neg: Scaling by -1 caused an overflow"
          end
      | _ => Error "Neg: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _ => Error "Neg: all data_type fields must be given"
    end
  end.
