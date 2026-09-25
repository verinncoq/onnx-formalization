From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Export matrices.
From ONNXFormalization.ONNXEvaluator Require Export op_gemm.

(* Comparason operators for tensors *)

Definition le_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_le matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_le matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_le matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.

Definition lt_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_lt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_lt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_lt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.

Definition ge_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_ge matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_ge matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_ge matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.

Definition gt_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_gt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_gt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_gt matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.

Definition eq_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_eq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_eq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_eq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.

Definition neq_tensor (A B : TensorProto) : error_option bool :=
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
    (*check for same datatype*)
    match data_type_A_option, data_type_B_option with
    | Some data_type_A, Some data_type_B =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B) with

      | 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_binary binary_neq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
         match matrix_compare_int32 int32_neq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matrix_compare_int64 int64_neq matrix_A matrix_B with
          | Success result => Success (matrix_and result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end
      | _, _ => Error "op_comp: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "op_comp: all data_type fields must be given"
    end
  end end.
