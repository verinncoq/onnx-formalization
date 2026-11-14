From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXEvaluator Require Export matrices.


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
  let alpha_A' := scale_matrix_int32 A' alpha in                                       (*scale A' with alpha*)
  match matrix_multiplication_int32 alpha_A' B' with    (*multiply scaled A' with B'*)
    | Success alpha_A'_B' =>
      let shape_ab := shape alpha_A'_B' in
      match broadcast_2d (fst shape_ab) (snd shape_ab) dims_c C with            (*broadcast C to shape of ((scaled A') * B')*)
      | Success C_b => let scaled_C_b := scale_matrix_int32 C_b beta in                    (*scale C with beta*)
        matrix_addition_int32 alpha_A'_B' scaled_C_b    (*sum ((scaled A') * B') with scaled C*)
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
  let alpha_A' := scale_matrix_int64 A' alpha in                                        (*scale A' with alpha*)
  match matrix_multiplication_int64 alpha_A' B' with    (*multiply scaled A' with B'*)
    | Success alpha_A'_B' =>
      let shape_ab := shape alpha_A'_B' in
      match broadcast_2d (fst shape_ab) (snd shape_ab) dims_c C with            (*broadcast C to shape of ((scaled A') * B')*)
      | Success C_b => let scaled_C_b := scale_matrix_int64 C_b beta in                  (*scale C with beta*)
        matrix_addition_int64 alpha_A'_B' scaled_C_b    (*sum ((scaled A') * B') with scaled C*)
      | Error e => Error e
      end
  | Error e => Error e
  end.


(*tensor-to-matrix*)

From ONNXFormalization.ONNXConverter Require Export bytes_converter.

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
Definition tensor_of_matrix_float32 (m: matrix float32) : TensorProto :=
  let dims_tuple := (shape m) in
  let dim_1 := int64_of_Z (Z.of_nat (fst dims_tuple)) in
  let dim_2 := int64_of_Z (Z.of_nat (snd dims_tuple)) in
      let dims := [dim_1; dim_2] in
      let float_data := convert_to_row_major m in
      TensorProto_constructor dims (Some (int32_of_Z 1%Z)) None float_data [] [] [] None None None [] None [] [] [].

(*
Converts a matrix which uses the int32 datatype into a TensorProto.
The values are put into the int32 list.
*)
Definition tensor_of_matrix_int32 (m: matrix int32) : TensorProto :=
  let dims_tuple := (shape m) in
  let dim_1 := int64_of_Z (Z.of_nat (fst dims_tuple)) in
  let dim_2 := int64_of_Z (Z.of_nat (snd dims_tuple)) in
      let dims := [dim_1; dim_2] in
      let int_data := convert_to_row_major m in
      TensorProto_constructor dims (Some (int32_of_Z 6%Z)) None [] int_data [] [] None None None [] None [] [] [].

(*
Converts a matrix which uses the int64 datatype into a TensorProto.
The values are put into the int64 list.
*)
Definition tensor_of_matrix_int64 (m: matrix int64) : TensorProto :=
  let dims_tuple := (shape m) in
  let dim_1 := int64_of_Z (Z.of_nat (fst dims_tuple)) in
  let dim_2 := int64_of_Z (Z.of_nat (snd dims_tuple)) in
      let dims := [dim_1; dim_2] in
      let int_data := convert_to_row_major m in
      TensorProto_constructor dims (Some (int32_of_Z 7%Z)) None [] [] [] int_data None None None [] None [] [] [].


(*GEMM*)

From ONNXFormalization.ONNXConverter Require Export onnx_model_to_premodel.
Open Scope Z_scope.

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
Definition gemm' (A B C: TensorProto) (a: list AttributeProto) : error_option TensorProto :=
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
            | Success result => Success (tensor_of_matrix_float32 result)
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
              let alpha' := int32_of_Z alpha_z in
              let beta' := int32_of_Z beta_z in
                match gemm_int32 matrix_A matrix_B matrix_C alpha' beta' transA transB [dim_C_height; dim_C_width] with
                | Success result => Success (tensor_of_matrix_int32 result)
                | Error e => Error e
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
              let alpha' := int64_of_Z alpha_z in
              let beta' := int64_of_Z beta_z in
                match gemm_int64 matrix_A matrix_B matrix_C alpha' beta' transA transB [dim_C_height; dim_C_width] with
                | Success result => Success (tensor_of_matrix_int64 result)
                | Error e => Error e
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
Definition gemm_two_inputs' (A B: TensorProto) (a: list AttributeProto) : error_option TensorProto :=
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
          | Success result => Success (tensor_of_matrix_float32 result)
          | Error e => Error e
          end
        | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)"
        end

      | 6, 6 => (*int32*)
        match matrix_int32_of_tensor A, matrix_int32_of_tensor B with
        | Success matrix_A, Success matrix_B =>
          match Z_of_float32 alpha, Z_of_float32 beta with
          | Some alpha_z, Some beta_z =>
            let alpha' := int32_of_Z alpha_z in
            let beta' := int32_of_Z beta_z in
              let zero := (Byte.x00, Byte.x00, Byte.x00, Byte.x00) in
              match gemm_int32 matrix_A matrix_B [[zero]] alpha' beta' transA transB [] with
              | Success result => Success (tensor_of_matrix_int32 result)
              | Error e => Error e
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
            let alpha' := int64_of_Z alpha_z in
            let beta' := int64_of_Z beta_z in
              let zero := (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) in
              match gemm_int64 matrix_A matrix_B [[zero]] alpha' beta' transA transB [] with
              | Success result => Success (tensor_of_matrix_int64 result)
              | Error e => Error e
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

(** SUGGESTED GeMM **)

From ONNXFormalization.ONNXEvaluator Require Import valid_types.

Definition matrix_of_tensor {R : validType} (t: tensor R)
  : error_option (matrix R) :=
  match t with
  | Tensor tdims tdata =>
    match convert_dims tdims with
    | Success (height, width) => Success (convert_from_row_major tdata height width)
    | Error e => Error e
    end
  end.

Definition tensor_of_matrix {R : validType} (m: matrix R) : tensor R :=
  let dims_tuple := (shape m) in
  let dim_1 := int64_of_Z (Z.of_nat (fst dims_tuple)) in
  let dim_2 := int64_of_Z (Z.of_nat (snd dims_tuple)) in
      let dims := [dim_1; dim_2] in
      let data := convert_to_row_major m in
      Tensor dims data.

Definition scale_matrix {R : validType} (m : matrix R) (a : R) : matrix R :=
  map (map (mul a)) m.

Fixpoint add_lists {R : validType} (a b: list R) : error_option (list R) :=
  match a, b with
  | [], [] => Success []
  | h1::t1, h2::t2 => match add_lists t1 t2 with
                      | Success recursive =>
                          let new := add h1 h2 in
                          Success (new::recursive)
                      | Error e => Error e
                      end
  | _, _ => Error "Add lists: lists must have the same length"
  end.

Fixpoint matrix_addition {R : validType} (a b : matrix R) : error_option (matrix R) :=
  match a, b with
  | [], [] => Success []
  | ha::ta, hb::tb => match add_lists ha hb with
    | Success new => match matrix_addition ta tb with
      | Success recursive => Success (new::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  | _, _ => Error "Matrix addition: matrices must have the same shape"
  end.

Fixpoint list_product {R : validType} (a b : list R) : error_option R :=
  match a, b with
  | x::xs, y::ys =>
      match list_product xs ys with
      | Success recursive =>
          let result := add (mul x y) recursive in
          Success result
      | Error e => Error e
      end
  | [], [] => Success zero
  | _, _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)"
  end.

Definition matrix_multiplicaiton_helper {R : validType} (a b : matrix R)
  (row: list R) (j: nat) : error_option R :=
  match get_column b j with
  | Success c => list_product row c
  | Error e => Error e
  end.

Fixpoint matrix_multiplication {R : validType} (a b : matrix R)
  : error_option (matrix R) :=
  match a with
  | [] => Success []
  | row_a :: rows_a =>
      let num_columns_b := match b with
                           | [] => 0%nat
                           | row :: _ => length row
                           end in
      match list_error_option_to_error_option_list 
              (map (matrix_multiplicaiton_helper a b row_a) (seq 0 num_columns_b))
    [] with
    | Success new_row => match matrix_multiplication rows_a b with
      | Success recursive => Success (new_row::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.

Definition mgemm {R : validType} (A B C : matrix R) (alpha : R) (beta : R)
                 (transA : int64) (transB : int64) (C_dims : list nat) : error_option (matrix R) :=
  let A' := match (Z_of_int64 transA) with
            | 0%Z => A
            | _ => transpose A
            end in
  let B' := match (Z_of_int64 transB) with
            | 0%Z => B
            | _ => transpose B
            end in
  let alpha_A' := scale_matrix A' alpha in
  alpha_A'_B' <- matrix_multiplication alpha_A' B' ;;
  let shape_ab := shape alpha_A'_B' in
  C_b <- broadcast_2d (fst shape_ab) (snd shape_ab) C_dims C ;;
  let scaled_C_b := scale_matrix C_b beta in
  matrix_addition alpha_A'_B' scaled_C_b.

From mathcomp Require Import tuple.
Open Scope form_scope.

Definition gemm_3 (a: list AttributeProto) {R : validType} (ts : 3.-tuple (tensor R))
  : error_option (tensor R) :=
  let A := [tnth ts 0] in
  let B := [tnth ts 1] in
  let C := [tnth ts 2] in
  let (r1, transB) := get_gemm_attributes a in
  let (r2, transA) := r1 in
  let (alpha, beta) := r2 in
  match of_float32 alpha, of_float32 beta with
  | Some alpha', Some beta' =>
      match matrix_of_tensor A, matrix_of_tensor B, matrix_of_tensor C with
      | Success ma, Success mb, Success mc =>
          C_dims <- convert_dims (tdims C) ;;
          eapp tensor_of_matrix (mgemm ma mb mc alpha' beta' transA transB [fst C_dims; snd C_dims])
      | _, _, _ => Error "Gemm: Could not convert tensors intro matrices."
      end
  | _, _ => Error "Could not convert attributes into valid type."
  end.

Definition gemm_2 (a : list AttributeProto) {R : validType} (ts : 2.-tuple (tensor R))
  : error_option (tensor R) :=
  let A := [tnth ts 0] in
  let B := [tnth ts 1] in
  let (r1, transB) := get_gemm_attributes a in
  let (r2, transA) := r1 in
  let (alpha, beta) := r2 in
  match of_float32 alpha, of_float32 beta with
  | Some alpha', Some beta' =>
      match matrix_of_tensor A, matrix_of_tensor B with
      | Success ma, Success mb =>
          eapp tensor_of_matrix (mgemm ma mb [[zero]] alpha' beta' transA transB [])
      | _, _ => Error "Gemm: Could not convert tensors intro matrices."
      end
  | _, _ => Error "Could not convert attributes into valid type."
  end.

Definition gemm (A B C : TensorProto) (attribs : list AttributeProto)
  : error_option (TensorProto) :=
  apply_op (@gemm_3 attribs) [tuple A; B; C].

Definition gemm_two_inputs (A B : TensorProto) (attribs : list AttributeProto)
  : error_option (TensorProto) :=
  apply_op (@gemm_2 attribs) [tuple A; B].

(** * Equivalence of the old Gemm and the [apply_op] form

    The old and new versions return different error *messages*, so the
    statements compare [getValue]: both succeed with the same tensor, or both
    fail. *)

From mathcomp Require Import tuple.
From Stdlib Require Import Lia.
Open Scope Z_scope.

(** ** int32 / int64 wrap-around *)

Lemma byte_of_spec (z : Z) :
  Z.of_N (Byte.to_N (match Byte.of_N (Z.to_N (z mod 256)) with Some b => b | None => Byte.x00 end))
  = z mod 256.
Proof.
  pose proof (Z.mod_pos_bound z 256 ltac:(lia)).
  destruct (Byte.of_N _) eqn:E.
  - apply Byte.to_of_N in E. rewrite E. apply Z2N.id. lia.
  - apply Byte.of_N_None_iff in E. apply N2Z.inj_lt in E. rewrite Z2N.id in E; lia.
Qed.

Lemma div_mod_byte (z b c : Z) : 0 < b -> 0 < c ->
  ((z mod (b * (256 * c))) / b) mod 256 = (z / b) mod 256.
Proof.
  intros Hb Hc.
  rewrite (Z.div_mod z (b * (256 * c))) at 2 by lia.
  replace (b * (256 * c) * (z / (b * (256 * c)))) with ((256 * c * (z / (b * (256 * c)))) * b) by ring.
  rewrite Z.div_add_l by lia.
  replace (256 * c * (z / (b * (256 * c)))) with ((c * (z / (b * (256 * c)))) * 256) by ring.
  rewrite Z.add_comm, Z.mod_add by lia.
  reflexivity.
Qed.

Lemma int32_of_Z_mod (z : Z) : int32_of_Z (z mod 4294967296) = int32_of_Z z.
Proof.
  unfold int32_of_Z, uint32_of_Z. cbv beta zeta.
  repeat f_equal;
  (match goal with
    | |- (match Byte.of_N (Z.to_N (?x mod 256)) with Some _ => _ | None => _ end) =
         (match Byte.of_N (Z.to_N (?y mod 256)) with Some _ => _ | None => _ end) =>
        replace (x mod 256) with (y mod 256); [reflexivity|]
    end;
    match goal with
    | |- (?z / ?b) mod 256 = ((?z mod ?M) / ?b) mod 256 =>
        symmetry; replace M with (b * (256 * (M / (b * 256)))) by reflexivity;
        apply div_mod_byte; reflexivity
    | |- ?z mod 256 = (?z mod ?M) mod 256 =>
        rewrite (Z.div_mod z M) at 1 by lia;
        replace (M * (z / M)) with ((M / 256 * (z / M)) * 256) by (rewrite Z.mul_comm, Z.mul_assoc; reflexivity);
        rewrite Z.add_comm, Z.mod_add by lia; reflexivity
    end).
Qed.

(* z mod (256 * M) = z mod 256 + 256 * ((z / 256) mod M) *)
Lemma mod_256_split (z M : Z) : 0 < M ->
  z mod (256 * M) = z mod 256 + 256 * ((z / 256) mod M).
Proof.
  intros HM.
  rewrite (Z.div_mod z 256) at 1 by lia.
  rewrite (Z.div_mod (z / 256) M) at 1 by lia.
  set (q := z / 256 / M). set (r := (z / 256) mod M). set (s := z mod 256).
  replace (256 * (M * q + r) + s) with (s + 256 * r + q * (256 * M)) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small.
  subst r s. pose proof (Z.mod_pos_bound z 256). pose proof (Z.mod_pos_bound (z / 256) M). lia.
Qed.

Lemma Z_of_uint32_of_Z (z : Z) : Z_of_uint32 (uint32_of_Z z) = z mod 4294967296.
Proof.
  unfold Z_of_uint32, uint32_of_Z. cbv beta zeta iota.
  rewrite !byte_of_spec.
  change 4294967296 with (256 * (256 * (256 * 256))).
  rewrite (mod_256_split z), (mod_256_split (z / 256)), (mod_256_split (z / 256 / 256)) by lia.
  rewrite !Z.div_div by lia. lia.
Qed.

Lemma Z_of_int32_of_Z_mod (z : Z) :
  Z_of_int32 (int32_of_Z z) mod 4294967296 = z mod 4294967296.
Proof.
  unfold Z_of_int32, int32_of_Z. rewrite Z_of_uint32_of_Z.
  destruct (_ <=? _).
  - apply Z.mod_mod; lia.
  - change uint32_max with 4294967295.
    replace (z mod 4294967296 - 4294967295 - 1) with (z mod 4294967296 + (-1) * 4294967296) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

Lemma int32_of_Z_wrap (a b : Z) :
  int32_of_Z (Z_of_int32 (int32_of_Z a) + b) = int32_of_Z (a + b).
Proof.
  rewrite <- (int32_of_Z_mod (Z_of_int32 _ + b)), <- (int32_of_Z_mod (a + b)).
  rewrite Z.add_mod, Z_of_int32_of_Z_mod, <- Z.add_mod by lia.
  reflexivity.
Qed.

(* 64-bit versions *)

Lemma int64_of_Z_mod (z : Z) : int64_of_Z (z mod 18446744073709551616) = int64_of_Z z.
Proof.
  unfold int64_of_Z, uint64_of_Z. cbv beta zeta.
  repeat f_equal;
  (match goal with
    | |- (match Byte.of_N (Z.to_N (?x mod 256)) with Some _ => _ | None => _ end) =
         (match Byte.of_N (Z.to_N (?y mod 256)) with Some _ => _ | None => _ end) =>
        replace (x mod 256) with (y mod 256); [reflexivity|]
    end;
    match goal with
    | |- (?z / ?b) mod 256 = ((?z mod ?M) / ?b) mod 256 =>
        symmetry; replace M with (b * (256 * (M / (b * 256)))) by reflexivity;
        apply div_mod_byte; reflexivity
    | |- ?z mod 256 = (?z mod ?M) mod 256 =>
        rewrite (Z.div_mod z M) at 1 by lia;
        replace (M * (z / M)) with ((M / 256 * (z / M)) * 256) by (rewrite Z.mul_comm, Z.mul_assoc; reflexivity);
        rewrite Z.add_comm, Z.mod_add by lia; reflexivity
    end).
Qed.

Lemma Z_of_uint64_of_Z (z : Z) : Z_of_uint64 (uint64_of_Z z) = z mod 18446744073709551616.
Proof.
  unfold Z_of_uint64, uint64_of_Z. cbv beta zeta iota.
  rewrite !byte_of_spec.
  change 18446744073709551616 with (256 * (256 * (256 * (256 * (256 * (256 * (256 * 256))))))).
  rewrite (mod_256_split z), (mod_256_split (z / 256)), (mod_256_split (z / 256 / 256)),
    (mod_256_split (z / 256 / 256 / 256)), (mod_256_split (z / 256 / 256 / 256 / 256)),
    (mod_256_split (z / 256 / 256 / 256 / 256 / 256)),
    (mod_256_split (z / 256 / 256 / 256 / 256 / 256 / 256)) by lia.
  rewrite !Z.div_div by lia. lia.
Qed.

Lemma Z_of_int64_of_Z_mod (z : Z) :
  Z_of_int64 (int64_of_Z z) mod 18446744073709551616 = z mod 18446744073709551616.
Proof.
  unfold Z_of_int64, int64_of_Z. rewrite Z_of_uint64_of_Z.
  destruct (_ <=? _).
  - apply Z.mod_mod; lia.
  - change uint64_max with 18446744073709551615.
    replace (z mod 18446744073709551616 - 18446744073709551615 - 1)
      with (z mod 18446744073709551616 + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

Lemma int64_of_Z_wrap (a b : Z) :
  int64_of_Z (Z_of_int64 (int64_of_Z a) + b) = int64_of_Z (a + b).
Proof.
  rewrite <- (int64_of_Z_mod (Z_of_int64 _ + b)), <- (int64_of_Z_mod (a + b)).
  rewrite Z.add_mod, Z_of_int64_of_Z_mod, <- Z.add_mod by lia.
  reflexivity.
Qed.

(** ** Old per-type matrix functions agree with the generic ones *)

(* float32 *)
Lemma list_product_float32_eq (a b : list float32) : list_product_float32 a b = list_product a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite IH. reflexivity.
Qed.

Lemma mm_helper_float32_eq (a b : matrix float32) r j :
  matrix_multiplicaiton_float32_helper a b r j = matrix_multiplicaiton_helper a b r j.
Proof.
  unfold matrix_multiplicaiton_float32_helper, matrix_multiplicaiton_helper.
  destruct (get_column b j) eqn:E; change (@get_column _ b j) with (@get_column float32 b j); rewrite E;
    [apply list_product_float32_eq | reflexivity].
Qed.

Lemma matrix_multiplication_float32_eq (a b : matrix float32) :
  matrix_multiplication_float32 a b = matrix_multiplication a b.
Proof.
  induction a as [|r a IH]; [reflexivity|].
  cbn. rewrite IH, (map_ext _ _ (mm_helper_float32_eq (r :: a) b r)). reflexivity.
Qed.

Lemma add_lists_float32_eq (a b : list float32) : add_lists_float32 a b = add_lists a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite IH. reflexivity.
Qed.

Lemma matrix_addition_float32_eq (a b : matrix float32) :
  matrix_addition_float32 a b = matrix_addition a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite add_lists_float32_eq, IH. reflexivity.
Qed.

Lemma scale_matrix_float32_eq (m : matrix float32) (s : float32) :
  scale_matrix_float32 m s = scale_matrix m s.
Proof. reflexivity. Qed.

(* int32 *)
Lemma list_product_int32_eq (a b : list int32) : list_product_int32 a b = list_product a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite <- IH. destruct (list_product_int32 a b); [|reflexivity].
  cbn. now rewrite int32_of_Z_wrap.
Qed.

Lemma mm_helper_int32_eq (a b : matrix int32) r j :
  matrix_multiplicaiton_int32_helper a b r j = matrix_multiplicaiton_helper a b r j.
Proof.
  unfold matrix_multiplicaiton_int32_helper, matrix_multiplicaiton_helper.
  destruct (get_column b j) eqn:E; change (@get_column _ b j) with (@get_column int32 b j); rewrite E;
    [apply list_product_int32_eq | reflexivity].
Qed.

Lemma matrix_multiplication_int32_eq (a b : matrix int32) :
  matrix_multiplication_int32 a b = matrix_multiplication a b.
Proof.
  induction a as [|r a IH]; [reflexivity|].
  cbn. rewrite IH, (map_ext _ _ (mm_helper_int32_eq (r :: a) b r)). reflexivity.
Qed.

Lemma add_lists_int32_eq (a b : list int32) : add_lists_int32 a b = add_lists a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite IH. reflexivity.
Qed.

Lemma matrix_addition_int32_eq (a b : matrix int32) :
  matrix_addition_int32 a b = matrix_addition a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite add_lists_int32_eq, IH. reflexivity.
Qed.

Lemma scale_matrix_int32_eq (m : matrix int32) (s : int32) :
  scale_matrix_int32 m s = scale_matrix m s.
Proof.
  unfold scale_matrix_int32, scale_matrix. rewrite !map_map.
  apply map_ext; intro r. rewrite !map_map. reflexivity.
Qed.

(* int64 *)
Lemma list_product_int64_eq (a b : list int64) : list_product_int64 a b = list_product a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite <- IH. destruct (list_product_int64 a b); [|reflexivity].
  cbn. now rewrite int64_of_Z_wrap.
Qed.

Lemma mm_helper_int64_eq (a b : matrix int64) r j :
  matrix_multiplicaiton_int64_helper a b r j = matrix_multiplicaiton_helper a b r j.
Proof.
  unfold matrix_multiplicaiton_int64_helper, matrix_multiplicaiton_helper.
  destruct (get_column b j) eqn:E; change (@get_column _ b j) with (@get_column int64 b j); rewrite E;
    [apply list_product_int64_eq | reflexivity].
Qed.

Lemma matrix_multiplication_int64_eq (a b : matrix int64) :
  matrix_multiplication_int64 a b = matrix_multiplication a b.
Proof.
  induction a as [|r a IH]; [reflexivity|].
  cbn. rewrite IH, (map_ext _ _ (mm_helper_int64_eq (r :: a) b r)). reflexivity.
Qed.

Lemma add_lists_int64_eq (a b : list int64) : add_lists_int64 a b = add_lists a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite IH. reflexivity.
Qed.

Lemma matrix_addition_int64_eq (a b : matrix int64) :
  matrix_addition_int64 a b = matrix_addition a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn. rewrite add_lists_int64_eq, IH. reflexivity.
Qed.

Lemma scale_matrix_int64_eq (m : matrix int64) (s : int64) :
  scale_matrix_int64 m s = scale_matrix m s.
Proof.
  unfold scale_matrix_int64, scale_matrix. rewrite !map_map.
  apply map_ext; intro r. rewrite !map_map. reflexivity.
Qed.

(* per-type gemm vs generic mgemm *)

Lemma gemm_float32_mgemm A B C alpha beta tA tB dC :
  gemm_float32 A B C alpha beta tA tB dC = mgemm A B C alpha beta tA tB dC.
Proof.
  unfold gemm_float32, mgemm.
  cbv zeta. rewrite scale_matrix_float32_eq, matrix_multiplication_float32_eq.
  destruct (matrix_multiplication _ _); [|reflexivity]. cbn [ebind].
  destruct (broadcast_2d _ _ _ _); [|reflexivity]. cbn [ebind].
  rewrite scale_matrix_float32_eq, matrix_addition_float32_eq. reflexivity.
Qed.

Lemma gemm_int32_mgemm A B C alpha beta tA tB dC :
  gemm_int32 A B C alpha beta tA tB dC = mgemm A B C alpha beta tA tB dC.
Proof.
  unfold gemm_int32, mgemm.
  cbv zeta. rewrite scale_matrix_int32_eq, matrix_multiplication_int32_eq.
  destruct (matrix_multiplication _ _); [|reflexivity]. cbn [ebind].
  destruct (broadcast_2d _ _ _ _); [|reflexivity]. cbn [ebind].
  rewrite scale_matrix_int32_eq, matrix_addition_int32_eq. reflexivity.
Qed.

Lemma gemm_int64_mgemm A B C alpha beta tA tB dC :
  gemm_int64 A B C alpha beta tA tB dC = mgemm A B C alpha beta tA tB dC.
Proof.
  unfold gemm_int64, mgemm.
  cbv zeta. rewrite scale_matrix_int64_eq, matrix_multiplication_int64_eq.
  destruct (matrix_multiplication _ _); [|reflexivity]. cbn [ebind].
  destruct (broadcast_2d _ _ _ _); [|reflexivity]. cbn [ebind].
  rewrite scale_matrix_int64_eq, matrix_addition_int64_eq. reflexivity.
Qed.

(** ** Gemm with three inputs *)

Theorem gemm_equiv (A B C : TensorProto) (a : list AttributeProto) :
  getValue (gemm' A B C a) = getValue (gemm A B C a).
Proof.
  unfold gemm', gemm, gemm_3.
  destruct (get_gemm_attributes a) as [[[alpha beta] tA] tB].
  destruct A as [dA [ta|] sgA fA iA sA lA nA cA rA eA oA gA uA mA];
  destruct B as [dB [tb|] sgB fB iB sB lB nB cB rB eB oB gB uB mB];
  destruct C as [dC [tc|] sgC fC iC sC lC nC cC rC eC oC gC uC mC];
    try reflexivity.
  all: unfold apply_op, same_dtype, dispatch, option_map.
  all: cbn -[matrix_float32_of_tensor matrix_int32_of_tensor matrix_int64_of_tensor
            gemm_float32 gemm_int32 gemm_int64 mgemm matrix_of_tensor convert_dims
            Z_of_int32 Z_of_float32].
  all: rewrite ?Z.eqb_refl, ?Bool.andb_false_r; try reflexivity.
  generalize (Z_of_int32 ta) (Z_of_int32 tb) (Z_of_int32 tc); intros za zb zc.
  destruct za as [|p|p]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ].
  all: repeat (destruct p as [p|p|]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ]).
  all: destruct zb as [|p|p]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ].
  all: repeat (destruct p as [p|p|]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ]).
  all: destruct zc as [|p|p]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ].
  all: repeat (destruct p as [p|p|]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ]).
  all: cbv beta iota; cbn [Z.eqb Pos.eqb andb negb].
  all: unfold matrix_float32_of_tensor, matrix_int32_of_tensor, matrix_int64_of_tensor, matrix_of_tensor.
  all: repeat (
    cbn -[gemm_float32 gemm_int32 gemm_int64 mgemm convert_dims Z_of_float32
          float32_of_bytes int32_of_bytes int64_of_bytes convert_from_row_major];
    try unfold int32_of_float32, int64_of_float32;
    try reflexivity;
    match goal with
    | H : convert_dims ?d = _ |- context [convert_dims ?d] => rewrite H
    | H : Z_of_float32 ?f = _ |- context [Z_of_float32 ?f] => rewrite H
    | |- context [match convert_dims ?d with _ => _ end] =>
        let H := fresh "Hd" in destruct (convert_dims d) as [[? ?]|] eqn:H
    | |- context [match ?l with [] => _ | _ :: _ => _ end] => is_var l; destruct l
    | |- context [match ?o with Some _ => _ | None => _ end] => is_var o; destruct o
    | |- context [float32_of_bytes ?b] => destruct (float32_of_bytes b)
    | |- context [int32_of_bytes ?b] => destruct (int32_of_bytes b)
    | |- context [int64_of_bytes ?b] => destruct (int64_of_bytes b)
    | |- context [match Z_of_float32 ?f with _ => _ end] =>
        let H := fresh "Hz" in destruct (Z_of_float32 f) eqn:H
    end).
  all: cbn [ebind fst snd];
       rewrite ?gemm_float32_mgemm, ?gemm_int32_mgemm, ?gemm_int64_mgemm;
       destruct (mgemm _ _ _ _ _ _ _ _); reflexivity.
Qed.


(** Same result on success, and failure in exactly the same cases
    (only the error message may differ). *)
Corollary gemm_equiv_success (A B C : TensorProto) (a : list AttributeProto) (t : TensorProto) :
  gemm' A B C a = Success t <-> gemm A B C a = Success t.
Proof.
  pose proof (gemm_equiv A B C a) as H.
  destruct (gemm' A B C a), (gemm A B C a); cbn in H; split; intro E;
    try discriminate; congruence.
Qed.

Corollary gemm_equiv_error (A B C : TensorProto) (a : list AttributeProto) :
  (exists e, gemm' A B C a = Error e) <-> (exists e, gemm A B C a = Error e).
Proof.
  pose proof (gemm_equiv A B C a) as H.
  destruct (gemm' A B C a), (gemm A B C a); cbn in H; split; intros [e E];
    try discriminate; eauto.
Qed.

Corollary gemm_equiv_isSuccess (A B C : TensorProto) (a : list AttributeProto) :
  isSuccess (gemm' A B C a) = isSuccess (gemm A B C a).
Proof.
  pose proof (gemm_equiv A B C a) as H.
  destruct (gemm' A B C a), (gemm A B C a); cbn in H; try discriminate; reflexivity.
Qed.

(** ** Gemm with two inputs *)

Theorem gemm_2_equiv (A B : TensorProto) (a : list AttributeProto) :
  getValue (gemm_two_inputs' A B a) = getValue (gemm_two_inputs A B a).
Proof.
  unfold gemm_two_inputs', gemm_two_inputs, gemm_2.
  destruct (get_gemm_attributes a) as [[[alpha beta] tA] tB].
  destruct A as [dA [ta|] sgA fA iA sA lA nA cA rA eA oA gA uA mA];
  destruct B as [dB [tb|] sgB fB iB sB lB nB cB rB eB oB gB uB mB];
    try reflexivity.
  all: unfold apply_op, same_dtype, dispatch, option_map.
  all: cbn -[matrix_float32_of_tensor matrix_int32_of_tensor matrix_int64_of_tensor
            gemm_float32 gemm_int32 gemm_int64 mgemm matrix_of_tensor convert_dims
            Z_of_int32 Z_of_float32].
  all: rewrite ?Z.eqb_refl, ?Bool.andb_false_r; try reflexivity.
  generalize (Z_of_int32 ta) (Z_of_int32 tb); intros za zb.
  destruct za as [|p|p]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ].
  all: repeat (destruct p as [p|p|]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ]).
  all: destruct zb as [|p|p]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ].
  all: repeat (destruct p as [p|p|]; try solve [ cbv beta iota; cbn [Z.eqb Pos.eqb andb negb]; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity ]).
  all: cbv beta iota; cbn [Z.eqb Pos.eqb andb negb].
  all: unfold matrix_float32_of_tensor, matrix_int32_of_tensor, matrix_int64_of_tensor, matrix_of_tensor.
  all: repeat (
    cbn -[gemm_float32 gemm_int32 gemm_int64 mgemm convert_dims Z_of_float32
          float32_of_bytes int32_of_bytes int64_of_bytes convert_from_row_major];
    try unfold int32_of_float32, int64_of_float32;
    try reflexivity;
    match goal with
    | H : convert_dims ?d = _ |- context [convert_dims ?d] => rewrite H
    | H : Z_of_float32 ?f = _ |- context [Z_of_float32 ?f] => rewrite H
    | |- context [match convert_dims ?d with _ => _ end] =>
        let H := fresh "Hd" in destruct (convert_dims d) as [[? ?]|] eqn:H
    | |- context [match ?l with [] => _ | _ :: _ => _ end] => is_var l; destruct l
    | |- context [match ?o with Some _ => _ | None => _ end] => is_var o; destruct o
    | |- context [float32_of_bytes ?b] => destruct (float32_of_bytes b)
    | |- context [int32_of_bytes ?b] => destruct (int32_of_bytes b)
    | |- context [int64_of_bytes ?b] => destruct (int64_of_bytes b)
    | |- context [match Z_of_float32 ?f with _ => _ end] =>
        let H := fresh "Hz" in destruct (Z_of_float32 f) eqn:H
    end).
  all: cbn [ebind fst snd];
       rewrite ?gemm_float32_mgemm, ?gemm_int32_mgemm, ?gemm_int64_mgemm;
       destruct (mgemm _ _ _ _ _ _ _ _); reflexivity.
Qed.

(** Same result on success, and failure in exactly the same cases
    (only the error message may differ). *)
Corollary gemm_2_equiv_success (A B : TensorProto) (a : list AttributeProto) (t : TensorProto) :
  gemm_two_inputs' A B a = Success t <-> gemm_two_inputs A B a = Success t.
Proof.
  pose proof (gemm_2_equiv A B a) as H.
  destruct (gemm_two_inputs' A B a), (gemm_two_inputs A B a); cbn in H; split; intro E;
    try discriminate; congruence.
Qed.

Corollary gemm_2_equiv_error (A B : TensorProto) (a : list AttributeProto) :
  (exists e, gemm_two_inputs' A B a = Error e) <-> (exists e, gemm_two_inputs A B a = Error e).
Proof.
  pose proof (gemm_2_equiv A B a) as H.
  destruct (gemm_two_inputs' A B a), (gemm_two_inputs A B a); cbn in H; split; intros [e E];
    try discriminate; eauto.
Qed.

Corollary gemm_2_equiv_isSuccess (A B : TensorProto) (a : list AttributeProto) :
  isSuccess (gemm_two_inputs' A B a) = isSuccess (gemm_two_inputs A B a).
Proof.
  pose proof (gemm_2_equiv A B a) as H.
  destruct (gemm_two_inputs' A B a), (gemm_two_inputs A B a); cbn in H; try discriminate; reflexivity.
Qed.
