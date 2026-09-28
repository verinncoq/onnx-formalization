From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Export matrices.
From ONNXFormalization.ONNXEvaluator Require Export op_gemm.


(*matmul for various datatypes*)

(*
Matrix Multiplication on float32 matrices as defined by ONNX.
*)
Definition matmul_float32 (A B: matrix float32) : error_option (matrix float32) :=
  matrix_multiplication_float32 A B.

(*
Matrix Multiplication on int32 matrices as defined by ONNX.
*)
Definition matmul_int32 (A B: matrix int32) : error_option (matrix int32) :=
  matrix_multiplication_int32 A B.

(*
Matrix Multiplication on int64 matrices as defined by ONNX.
*)
Definition matmul_int64 (A B: matrix int64) : error_option (matrix int64) :=
  matrix_multiplication_int64 A B.


(*MATMUL*)

Open Scope Z_scope.

(*Computes MatMul for two inputs, as definied by ONNX*)
Definition matmul_tensor (A B: TensorProto) : error_option TensorProto :=
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
          match matmul_float32 matrix_A matrix_B with
          | Success result => tensor_of_matrix_float32 result
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matmul_int32 matrix_A matrix_B with
          | Success result => tensor_of_matrix_int32 result
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match matmul_int64 matrix_A matrix_B with
          | Success result => tensor_of_matrix_int64 result
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | _, _ => Error "MatMul: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "MatMul: all data_type fields must be given"
    end
  end end.
