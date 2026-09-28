From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Export matrices.

Definition add_tensor (A B : TensorProto) : error_option TensorProto :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with
      | 1, 1 => (*float32*)
          match add_lists_float32 float32_A float32_B with
          | Success x =>
          Success (TensorProto_constructor dims_A (int32_of_Z 1%Z) None x [] [] [] None None None [] None [] [] [])
          | Error e => Error e
          end
      | 6, 6 => (*int32*)
          match add_lists_int32 int32_A int32_B with
          | Success x =>
              Success (TensorProto_constructor dims_A (int32_of_Z 6%Z) None [] x [] [] None None None [] None [] [] [])
          | Error e => Error e
          end
      | 7, 7 => (*int64*)
          match add_lists_int64 int64_A int64_B with
          | Success x =>
              Success (TensorProto_constructor dims_A (int32_of_Z 7%Z) None [] [] [] x None None None [] None [] [] [])
          | Error e => Error e
          end
      | _, _ => Error "Gemm: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "Gemm: all data_type fields must be given"
    end
  end end.
