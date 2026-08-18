From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.

From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export model.
From CoqE2EAI Require Export matrices.


(*gemm for various datatypes*)

(*
General Matrix Multiplication on float32 matrices as defined by ONNX.
Matrices and attributes must be given, as well as dims of tensor c for broadcasting.
*)
Definition gemm_float32 (A B C: matrix float32) (alpha beta: float32) (transA transB: int64) (dims_c: list nat) : error_option (matrix float32) :=
  let A' := match (Z_of_int64 transA) with      (*A' is A, but might be transposed, depending on transA*)
  | 0 => A
  | _ => transpose A
  end in
  let B' := match (Z_of_int64 transB) with      (*B' is B, but might be transposed, depending on transB*)
  | 0 => B
  | _ => transpose B
  end in
  let alpha_A' := scale_matrix_float32 A' alpha in          (*scale A' with alpha*)
  match matrix_multiplication_float32 alpha_A' B' with      (*multiply scaled A' with B'*)
  | Success alpha_A'_B' =>
    let shape_ab := shape alpha_A'_B' in
    match broadcast_2d (fst shape_ab) (snd shape_ab) dims_c C with        (*broadcast C to shape of ((scaled A') * B')*)
    | Success C_b => let scaled_C_b := scale_matrix_float32 C_b beta in   (*scale C with beta*)
      matrix_addition_float32 alpha_A'_B' scaled_C_b                      (*sum ((scaled A') * B') with scaled C*)
    | Error e => Error e
    end
  | Error e => Error e
  end.

(*
General Matrix Multiplication on int32 matrices as defined by ONNX.
Matrices and attributes must be given, as well as dims of tensor c for broadcasting.
*)
Definition gemm_int32 (A B C: matrix int32) (alpha beta: int32) (transA transB: int64) (dims_c: list nat) : error_option (matrix int32) :=
  let A':= match (Z_of_int64 transA) with      (*A' is A, but might be transposed, depending on transA*)
  | 0 => A
  | _ => transpose A
  end in
  let B':= match (Z_of_int64 transB) with      (*B' is B, but might be transposed, depending on transB*)
  | 0 => B
  | _ => transpose B
  end in
  match scale_matrix_int32 A' alpha with                                      (*scale A' with alpha*)
  | Success alpha_A' => match matrix_multiplication_int32 alpha_A' B' with    (*multiply scaled A' with B'*)
    | Success alpha_A'_B' =>
      let shape_ab := shape alpha_A'_B' in
      match broadcast_2d (fst shape_ab) (snd shape_ab) dims_c C with            (*broadcast C to shape of ((scaled A') * B')*)
      | Success C_b => match scale_matrix_int32 C_b beta with                   (*scale C with beta*)
        | Success scaled_C_b => matrix_addition_int32 alpha_A'_B' scaled_C_b    (*sum ((scaled A') * B') with scaled C*)
        | Error e => Error e
        end
      | Error e => Error e
      end
    | Error e => Error e
    end
  | Error e => Error e
  end.

(*
General Matrix Multiplication on int64 matrices as defined by ONNX.
Matrices and attributes must be given, as well as dims of tensor c for broadcasting.
*)
Definition gemm_int64 (A B C: matrix int64) (alpha beta: int64) (transA transB: int64) (dims_c: list nat) : error_option (matrix int64) :=
  let A' := match (Z_of_int64 transA) with      (*A' is A, but might be transposed, depending on transA*)
  | 0 => A
  | _ => transpose A
  end in
  let B' := match (Z_of_int64 transB) with      (*B' is B, but might be transposed, depending on transB*)
  | 0 => B
  | _ => transpose B
  end in
  match scale_matrix_int64 A' alpha with                                      (*scale A' with alpha*)
  | Success alpha_A' => match matrix_multiplication_int64 alpha_A' B' with    (*multiply scaled A' with B'*)
    | Success alpha_A'_B' =>
      let shape_ab := shape alpha_A'_B' in
      match broadcast_2d (fst shape_ab) (snd shape_ab) dims_c C with            (*broadcast C to shape of ((scaled A') * B')*)
      | Success C_b => match scale_matrix_int64 C_b beta with                   (*scale C with beta*)
        | Success scaled_C_b => matrix_addition_int64 alpha_A'_B' scaled_C_b    (*sum ((scaled A') * B') with scaled C*)
        | Error e => Error e
        end
      | Error e => Error e
      end
    | Error e => Error e
    end
  | Error e => Error e
  end.


(*tensor-to-matrix*)

From CoqE2EAI Require Export bytes_converter.

(*Convert a list of int64 dims to a pair of nat. Works only for scalars, vectors and matrices. If not a matrix, dimensions get set to zero.*)
Definition convert_dims (dims: list int64) : error_option (nat * nat) :=
  match dims with
  | [] => Success (1, 1)  (*scalar*)
  | h::[] =>              (*vector*)
    match Z_of_int64 h with
    | Zpos h' => Success (1, Pos.to_nat h')
    | _ => Error "dim cannot be zero or negative"
    end
  | h::w::[] =>           (*matrix*)
    match Z_of_int64 h, Z_of_int64 w with
    | Zpos h', Zpos w' => Success (Pos.to_nat h', Pos.to_nat w')
    | _, _ => Error "dim cannot be zero or negative"
    end
  | _ => Error "dims list cannot be longer than two when converting into a matrix"
  end.

(*
Converts a TensorProto which uses the float32 datatype into a matrix.
The TensorProto must define it's values either in the float32 list or the raw_data list.
*)
Definition matrix_float32_of_tensor (t: TensorProto) : error_option (matrix float32) :=
  match t with
  | TensorProto_constructor dims _ _ float32 _ _ _ _ _ raw_data _ _ _ _ _ =>
    match convert_dims dims with
    | Success (height, width) =>
      match float32 with
      | [] => match raw_data with
        | Some bytes => match float32_of_bytes bytes with
          | Success floats => Success (convert_from_row_major floats height width)
          | Error e => Error e
          end
        | None => Error "TensorProto with type float32 must either have non-empty float_data or non-empty raw_data"
        end
      | floats => Success (convert_from_row_major floats height width)
      end
    | Error e => Error e
    end
  end.

(*
Converts a TensorProto which uses the int32 datatype into a matrix.
The TensorProto must define it's values either in the int32 list or the raw_data list.
*)
Definition matrix_int32_of_tensor (t: TensorProto) : error_option (matrix int32) :=
  match t with
  | TensorProto_constructor dims _ _ _ int32 _ _ _ _ raw_data _ _ _ _ _ =>
    match convert_dims dims with
    | Success (height, width) =>
      match int32 with
      | [] => match raw_data with
        | Some bytes => match int32_of_bytes bytes with
          | Success ints => Success (convert_from_row_major ints height width)
          | Error e => Error e
          end
        | None => Error "TensorProto with type int32 must either have non-empty int32_data or non-empty raw_data"
        end
      | ints => Success (convert_from_row_major ints height width)
      end
    | Error e => Error e
    end
  end.

(*
Converts a TensorProto which uses the int64 datatype into a matrix.
The TensorProto must define it's values either in the int64 list or the raw_data list.
*)
Definition matrix_int64_of_tensor (t: TensorProto) : error_option (matrix int64) :=
  match t with
  | TensorProto_constructor dims _ _ _ _ _ int64 _ _ raw_data _ _ _ _ _ =>
    match convert_dims dims with
    | Success (height, width) =>
      match int64 with
      | [] => match raw_data with
        | Some bytes => match int64_of_bytes bytes with
          | Success ints => Success (convert_from_row_major ints height width)
          | Error e => Error e
          end
        | None => Error "TensorProto with type int64 must either have non-empty int64_data or non-empty raw_data"
        end
      | ints => Success (convert_from_row_major ints height width)
      end
    | Error e => Error e
    end
  end.



(*matrix-to-tensor*)

(*
Converts a matrix which uses the float32 datatype into a TensorProto.
The values are put into the float32 list.
*)
Definition tensor_of_matrix_float32 (m: matrix float32) : error_option TensorProto :=
  let dims_tuple := (shape m) in
  match int64_of_Z (Z.of_nat (fst dims_tuple)) with
  | Some dim_1 => match int64_of_Z (Z.of_nat (snd dims_tuple)) with
    | Some dim_2 =>
      let dims := [dim_1; dim_2] in
      let float_data := convert_to_row_major m in
      Success (TensorProto_constructor dims (int32_of_Z 1%Z) None float_data [] [] [] None None None [] None [] [] [])
    | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
    end
  | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
  end.

(*
Converts a matrix which uses the int32 datatype into a TensorProto.
The values are put into the int32 list.
*)
Definition tensor_of_matrix_int32 (m: matrix int32) : error_option TensorProto :=
  let dims_tuple := (shape m) in
  match int64_of_Z (Z.of_nat (fst dims_tuple)) with
  | Some dim_1 => match int64_of_Z (Z.of_nat (snd dims_tuple)) with
    | Some dim_2 =>
      let dims := [dim_1; dim_2] in
      let int_data := convert_to_row_major m in
      Success (TensorProto_constructor dims (int32_of_Z 6%Z) None [] int_data [] [] None None None [] None [] [] [])
    | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
    end
  | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
  end.

(*
Converts a matrix which uses the int64 datatype into a TensorProto.
The values are put into the int64 list.
*)
Definition tensor_of_matrix_int64 (m: matrix int64) : error_option TensorProto :=
  let dims_tuple := (shape m) in
  match int64_of_Z (Z.of_nat (fst dims_tuple)) with
  | Some dim_1 => match int64_of_Z (Z.of_nat (snd dims_tuple)) with
    | Some dim_2 =>
      let dims := [dim_1; dim_2] in
      let int_data := convert_to_row_major m in
      Success (TensorProto_constructor dims (int32_of_Z 7%Z) None [] [] [] int_data None None None [] None [] [] [])
    | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
    end
  | None => Error "Matrix dimension not convertable to int64 (maybe to big?)"
  end.


(*GEMM*)

Open Scope Z_scope.
From CoqE2EAI Require Export onnx_model_to_premodel.

(*Extracts the Attributes necessary for the gemm operation. If not found, it's replaces by a default*)
Definition get_gemm_attributes (a: list AttributeProto) : (float32 * float32 * int64 * int64) :=
  let alpha := match get_float_attribute a """alpha""" with
  | Success a => a
  | Error _ => default_one
  end in
  let beta := match get_float_attribute a """beta""" with
  | Success b => b
  | Error _ => default_one
  end in
  let transA := match get_int_attribute a """transA""" with
  | Success ta => ta
  | Error _ => default_zero
  end in
  let transB := match get_int_attribute a """transB""" with
  | Success tb => tb
  | Error _ => default_zero
  end in
  (alpha, beta, transA, transB).

(*Computes Gemm for three inputs, as definied by ONNX*)
Definition gemm (A B C: TensorProto) (a: list AttributeProto) : error_option TensorProto :=
  let (r1, transB) := get_gemm_attributes a in
  let (r2, transA) := r1 in
  let (alpha, beta) := r2 in
  match A with
  | TensorProto_constructor dims_A data_type_A_option _ float32_A int32_A _ int64_A _ _ raw_data_A _ _ _ _ _ =>
  match B with
  | TensorProto_constructor dims_B data_type_B_option _ float32_B int32_B _ int64_B _ _ raw_data_B _ _ _ _ _ =>
  match C with
  | TensorProto_constructor dims_C data_type_C_option _ float32_C int32_C _ int64_C _ _ raw_data_C _ _ _ _ _ =>

    (*check for same datatype*)
    match data_type_A_option, data_type_B_option, data_type_C_option with
    | Some data_type_A, Some data_type_B, Some data_type_C =>
      match (Z_of_int32 data_type_A), (Z_of_int32 data_type_B), (Z_of_int32 data_type_C) with

      | 1, 1, 1 => (*float32*)
        match matrix_float32_of_tensor A, matrix_float32_of_tensor B, matrix_float32_of_tensor C with
        | Success matrix_A, Success matrix_B, Success matrix_C =>
          match convert_dims dims_C with
          | Success (dim_C_height, dim_C_width) => 
            match gemm_float32 matrix_A matrix_B matrix_C alpha beta transA transB [dim_C_height; dim_C_width] with
            | Success result => tensor_of_matrix_float32 result
            | Error e => Error e
            end
          | Error e => Error e
          end
        | _, _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B, matrix_int32_of_tensor C with
        | Success matrix_A, Success matrix_B, Success matrix_C =>
          match convert_dims dims_C with
          | Success (dim_C_height, dim_C_width) => 
            match Z_of_float32 alpha, Z_of_float32 beta with
            | Some alpha_z, Some beta_z =>
              match int32_of_Z alpha_z, int32_of_Z beta_z with
              | Some alpha', Some beta' =>
                match gemm_int32 matrix_A matrix_B matrix_C alpha' beta' transA transB [dim_C_height; dim_C_width] with
                | Success result => tensor_of_matrix_int32 result
                | Error e => Error e
                end
              | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
              end
            | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
            end
          | Error e => Error e
          end
        | _, _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B, matrix_int64_of_tensor C with
        | Success matrix_A, Success matrix_B, Success matrix_C =>
          match convert_dims dims_C with
          | Success (dim_C_height, dim_C_width) => 
            match Z_of_float32 alpha, Z_of_float32 beta with
            | Some alpha_z, Some beta_z =>
              match int64_of_Z alpha_z, int64_of_Z beta_z with
              | Some alpha', Some beta' =>
                match gemm_int64 matrix_A matrix_B matrix_C alpha' beta' transA transB [dim_C_height; dim_C_width] with
                | Success result => tensor_of_matrix_int64 result
                | Error e => Error e
                end
              | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
              end
            | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
            end
          | Error e => Error e
          end
        | _, _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | _, _, _ => Error "Gemm: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _, _ => Error "Gemm: all data_type fields must be given"
    end
  end end end.

From Flocq Require Import Bits BinarySingleNaN.

(*Computes Gemm for two inputs, as definied by ONNX. The third input is initialized to zero for the other functions calls.*)
Definition gemm_two_inputs (A B: TensorProto) (a: list AttributeProto) : error_option TensorProto :=
  let (r1, transB) := get_gemm_attributes a in
  let (r2, transA) := r1 in
  let (alpha, beta) := r2 in
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
          let zero := Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 0 0 false in
          match gemm_float32 matrix_A matrix_B [[zero]] alpha beta transA transB [] with
          | Success result => tensor_of_matrix_float32 result
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match Z_of_float32 alpha, Z_of_float32 beta with
          | Some alpha_z, Some beta_z =>
            match int32_of_Z alpha_z, int32_of_Z beta_z with
            | Some alpha', Some beta' =>
              let zero := (Byte.x00, Byte.x00, Byte.x00, Byte.x00) in
              match gemm_int32 matrix_A matrix_B [[zero]] alpha' beta' transA transB [] with
              | Success result => tensor_of_matrix_int32 result
              | Error e => Error e
              end
            | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
            end
          | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 7, 7 => (*int64*)
        match matrix_int64_of_tensor A, matrix_int64_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match Z_of_float32 alpha, Z_of_float32 beta with
          | Some alpha_z, Some beta_z =>
            match int64_of_Z alpha_z, int64_of_Z beta_z with
            | Some alpha', Some beta' =>
              let zero := (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) in
              match gemm_int64 matrix_A matrix_B [[zero]] alpha' beta' transA transB [] with
              | Success result => tensor_of_matrix_int64 result
              | Error e => Error e
              end
            | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
            end
          | _, _ => Error "Could not convert alpha or beta to int, which is necessary when operating on int datatypes"
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | _, _ => Error "Gemm: all tensors must have the same datatype, which must be FLOAT, INT32 or INT64"
      end
    | _, _ => Error "Gemm: all data_type fields must be given"
    end
  end end.