From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From Flocq Require Import Bits BinarySingleNaN.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export conversion_functions.


(*general definitions*)

(*
Returns a matrix Type with entries of Type T. Matrix is defined row-major (row-by-row).
Each inner list represents a row, while the outer list combines them.
*)
Definition matrix (T: Type) := list (list T).

(*
Returns the shape of the matrix as
1. number of rows
2. number of columns
*)
Definition shape {T: Type} (m: matrix T) : (nat * nat) :=
  match m with
  | [] => (0%nat, 0%nat)
  | []::_ => (0%nat, 0%nat)
  | h::_ => ((length m), (length h))
  end.

(*converts a matrix given as a one-dimensional row-major list into a matrix given as a list of rows*)
Fixpoint convert_from_row_major {T: Type} (l: list T) (height width: nat) : matrix T :=
  match height with
  | O => []
  | S n => (firstn width l) :: (convert_from_row_major (skipn width l) n width)
  end.

(*converts a matrix given as a list of rows into a matrix given as a one-dimensional row-major list*)
Fixpoint convert_to_row_major {T: Type} (m: matrix T) : list T :=
  match m with
  | [] => []
  | h::t => h ++ (convert_to_row_major t)
  end.

(*with the help of chat-gpt; returns the j'th column of m*)
Fixpoint get_column {T: Type} (m : matrix T) (j : nat) : error_option (list T) :=
  match m with
  | [] => Success []
  | row :: rows =>
      match nth_error row j with
      | Some x => match get_column rows j with
        | Success recursive => Success (x::recursive)
        | Error e => Error e
        end
      | None => Error "Cannot get column: matrix is not wide enought (probably wrong dimension)"
      end
  end.

(*returns the first element of the list, if there is some*)
Definition head {T: Type} (l: list T) : option T :=
  match l with
  | [] => None
  | h::t => Some h
  end.

(*
This is a helper function.
If all elements of the input list are Some, the result is Some, with all the values of the elements.
If not, the result is None.
*)
Fixpoint option_list_of_list_option {T: Type} (l: list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | h::t => match h with
    | Some h' => match option_list_of_list_option t with
      | Some t' => Some (h'::t')
      | None => None
      end
    | None => None
    end
  end.

(*with the help of chat-gpt, recursive helper to transpose a matrix*)
Fixpoint transpose_rec {T: Type} (d: nat) (m : matrix T) : option (matrix T) :=
  match d with
  | O => None
  | S n => match m with
    | [] => Some []
    | [] :: _ => Some []
    | _ => match option_list_of_list_option (map head m) with
      | Some first_column => let rest_matrix := map (fun l => tl l) m in
        match transpose_rec n rest_matrix with
        | Some recursive => Some (first_column :: recursive)
        | None => None
        end
      | None => None
      end
    end
  end.

(*transposes a matrix m*)
Definition transpose {T: Type} (m: matrix T) : matrix T :=
  match (transpose_rec ((snd (shape m)) + 1) m) with
  | Some out => out
  | None => m (*due to the call of transpose_rec with the given shape, this case should never be true*)
  end.

Open Scope nat_scope.

(*helper for broadcast_2d*)
Definition broadcast_2d_vector {T: Type} (dim1_a dim2_a: nat) (b: matrix T) : error_option (matrix T) :=
  match shape b with
  | (1%nat, defined_dim_b) => (*b is a row vector*)
    match b with
    | [row] => match defined_dim_b =? dim2_a with
      | true => Success (repeat row dim1_a)
      | false => Error "Broadcast: Dimension which is not one must match at least one given dimension"
      end
    | _ => Error "Cannot happen, because of shape check"
    end
  | (defined_dim_b, 1%nat) => (*b is a column vector*)
    match transpose b with
    | [row] => let result := transpose (repeat row dim2_a) in
      match defined_dim_b =? dim1_a with
      | true => Success result
      | false => Error "Broadcast: Dimension which is not one must match at least one given dimension"
      end
    | _ => Error "Transpose should lead to exactly one dimension"
    end
  | _ => Error "Broadcast: Vector matrices must have at least one dimension which is one"
  end.

(*unidirectional broadcasting for two dimensions, as needed in Gemm and defined in ONNX' semantics*)
Definition broadcast_2d {T: Type} (dim1_a dim2_a: nat) (dims_b: list nat) (b: matrix T) : error_option (matrix T) :=
  match dims_b with
  | [] => (*b is a scalar*)
    match b with
    | [[scale]] => Success (repeat (repeat scale dim2_a) dim1_a)
    | _ => Error "Broadcast: Scalar matrices must have exactly one element"
    end
  | _::[] => (*b is a vector*)
    broadcast_2d_vector dim1_a dim2_a b
  | 1::_::[] => (*b is a vector*)
    broadcast_2d_vector dim1_a dim2_a b
  | _::1::[] => (*b is a vector*)
    broadcast_2d_vector dim1_a dim2_a b
  | dim1_b::dim2_b::[] => (*b is a matrix*)
    match dim1_a =? dim1_b, dim2_a =? dim2_b with
    | true, true => Success b
    | _, _ => Error "Broadcast: Matrices must have matching shape"
    end
  | _ => (*b is a tensor, but not a scalar, vector or matix*)
    Error "Broadcast: Can only broadcast scalars, vectors and matrices"
  end.

Close Scope nat_scope.




(*float32*)

(*with the help of chat-gpt, computes the pairwise product between two lists*)
Fixpoint list_product_float32 (a b: list float32) : error_option float32 :=
  match a, b with
  | x::xs, y::ys =>
    match list_product_float32 xs ys with
    | Success recursive => Success (b32_plus mode_NE (b32_mult mode_NE x y) recursive)
    | Error e => Error e
    end
  | [], [] => Success (Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 0 0 false)
  | _, _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)"
  end.

Definition matrix_multiplicaiton_float32_helper (a b: matrix float32) (row: list float32) (j: nat) : error_option float32 :=
  match get_column b j with
  | Success c => list_product_float32 row c
  | Error e => Error e
  end.

(*with the help of chat-gpt, computes the dot product between two matrices, returns error if shapes do not match*)
Fixpoint matrix_multiplication_float32 (a b: matrix float32) : error_option (matrix float32) :=
  match a with
  | [] => Success []
  | row_a :: rows_a =>
    let num_columns_b := match b with
    | [] => 0%nat
    | row :: _ => length row
    end in
    match list_error_option_to_error_option_list 
    (map (matrix_multiplicaiton_float32_helper a b row_a) (seq 0 num_columns_b))
    [] with
    | Success new_row => match matrix_multiplication_float32 rows_a b with
      | Success recursive => Success (new_row::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.

(*computes the pairwise sum of two lists*)
Fixpoint add_lists_float32 (a b: list float32) : error_option (list float32) :=
  match a, b with
  | [], [] => Success []
  | h1::t1, h2::t2 => match add_lists_float32 t1 t2 with
    | Success recursive => Success ((b32_plus mode_NE h1 h2)::recursive)
    | Error e => Error e
    end
  | _, _ => Error "Add lists: lists must have the same length"
  end.

(*computes the pairwise sum of two matrices*)
Fixpoint matrix_addition_float32 (a b : matrix float32) : error_option (matrix float32) :=
  match a, b with
  | [], [] => Success []
  | ha::ta, hb::tb => match add_lists_float32 ha hb with
    | Success new => match matrix_addition_float32 ta tb with
      | Success recursive => Success (new::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  | _, _ => Error "Matrix addition: matrices must have the same shape"
  end.

(*scales the matrix by a factor s*)
Definition scale_matrix_float32 (a: matrix float32) (s: float32) : matrix float32 :=
  map (map (b32_mult mode_NE s)) a.

(*converts the whole matrix into a readable string*)
Definition string_matrix_of_matrix_float32 (m: matrix float32) : matrix string :=
  map (map string_of_float32) m.



(*int32*)

(*with the help of chat-gpt, computes the pairwise product between two lists*)
Fixpoint list_product_int32 (a b : list int32) : error_option int32 :=
  match a, b with
  | x::xs, y::ys =>
    let Z_x := Z_of_int32 x in
    let Z_y := Z_of_int32 y in
    match list_product_int32 xs ys with
    | Success recursive =>
      let result := Z_x * Z_y + (Z_of_int32 recursive) in
      match int32_of_Z result with
      | Some f => Success f
      | None => Error "Dot product between two int32 yields to infinity or NaN"
      end
    | Error e => Error e
    end
  | [], [] => Success (Byte.x00, Byte.x00, Byte.x00, Byte.x00)
  | _, _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)"
  end.

Definition matrix_multiplicaiton_int32_helper (a b : matrix int32) (row: list int32) (j: nat) : error_option int32 :=
  match get_column b j with
  | Success c => list_product_int32 row c
  | Error e => Error e
  end.

(*with the help of chat-gpt, computes the dot product between two matrices, returns error if shapes do not match*)
Fixpoint matrix_multiplication_int32 (a b : matrix int32) : error_option (matrix int32) :=
  match a with
  | [] => Success []
  | row_a :: rows_a =>
    let num_columns_b := match b with
    | [] => 0%nat
    | row :: _ => length row
    end in
    match list_error_option_to_error_option_list 
    (map (matrix_multiplicaiton_int32_helper a b row_a) (seq 0 num_columns_b))
    [] with
    | Success new_row => match matrix_multiplication_int32 rows_a b with
      | Success recursive => Success (new_row::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.

(*computes the pairwise sum of two lists*)
Fixpoint add_lists_int32 (a b: list int32) : error_option (list int32) :=
  match a, b with
  | [], [] => Success []
  | h1::t1, h2::t2 => match add_lists_int32 t1 t2 with
    | Success recursive => match int32_of_Z ((Z_of_int32 h1) + (Z_of_int32 h2)) with
      | Some new => Success (new::recursive)
      | None => Error "Addition between two int32 yields to infinity or NaN"
      end
    | Error e => Error e
    end
  | _, _ => Error "Add lists: lists must have the same length"
  end.

(*computes the pairwise sum of two matrices*)
Fixpoint matrix_addition_int32 (a b : matrix int32) : error_option (matrix int32) :=
  match a, b with
  | [], [] => Success []
  | ha::ta, hb::tb => match add_lists_int32 ha hb with
    | Success new => match matrix_addition_int32 ta tb with
      | Success recursive => Success (new::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  | _, _ => Error "Matrix addition: matrices must have the same shape"
  end.

(*scales the matrix by a factor s*)
Definition scale_matrix_int32 (a: matrix int32) (s: int32) : error_option (matrix int32) :=
  let z_matrix := map (map Z_of_int32) a in
  let scaled_z_matrix := map (map (Z.mul (Z_of_int32 s))) z_matrix in
  let result_option := map (map int32_of_Z) scaled_z_matrix in
  match option_list_of_list_option 
    (map option_list_of_list_option result_option)
  with  
  | Some result => Success result
  | None => Error "Matrix scaling results in overflow"
  end.

(*converts the whole matrix into a readable string*)
Definition string_matrix_of_matrix_int32 (m: matrix int32) : matrix string :=
  map (map string_of_int32) m.



(*int64*)

(*with the help of chat-gpt, computes the pairwise product between two lists*)
Fixpoint list_product_int64 (a b : list int64) : error_option int64 :=
  match a, b with
  | x::xs, y::ys =>
    let Z_x := Z_of_int64 x in
    let Z_y := Z_of_int64 y in
    match list_product_int64 xs ys with
    | Success recursive =>
      let result := Z_x * Z_y + (Z_of_int64 recursive) in
      match int64_of_Z result with
      | Some f => Success f
      | None => Error "Dot product between two int64 yields to infinity or NaN"
      end
    | Error e => Error e
    end
  | [], [] => Success (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00)
  | _, _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)"
  end.

Definition matrix_multiplicaiton_int64_helper (a b : matrix int64) (row: list int64) (j: nat) : error_option int64 :=
  match get_column b j with
  | Success c => list_product_int64 row c
  | Error e => Error e
  end.

(*with the help of chat-gpt, computes the dot product between two matrices, returns error if shapes do not match*)
Fixpoint matrix_multiplication_int64 (a b : matrix int64) : error_option (matrix int64) :=
  match a with
  | [] => Success []
  | row_a :: rows_a =>
    let num_columns_b := match b with
    | [] => 0%nat
    | row :: _ => length row
    end in
    match list_error_option_to_error_option_list 
    (map (matrix_multiplicaiton_int64_helper a b row_a) (seq 0 num_columns_b))
    [] with
    | Success new_row => match matrix_multiplication_int64 rows_a b with
      | Success recursive => Success (new_row::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.


(*computes the pairwise sum of two lists*)
Fixpoint add_lists_int64 (a b: list int64) : error_option (list int64) :=
  match a, b with
  | [], [] => Success []
  | h1::t1, h2::t2 => match add_lists_int64 t1 t2 with
    | Success recursive => match int64_of_Z ((Z_of_int64 h1) + (Z_of_int64 h2)) with
      | Some new => Success (new::recursive)
      | None => Error "Addition between two int64 yields to infinity or NaN"
      end
    | Error e => Error e
    end
  | _, _ => Error "Add lists: lists must have the same length"
  end.

(*computes the pairwise sum of two matrices*)
Fixpoint matrix_addition_int64 (a b : matrix int64) : error_option (matrix int64) :=
  match a, b with
  | [], [] => Success []
  | ha::ta, hb::tb => match add_lists_int64 ha hb with
    | Success new => match matrix_addition_int64 ta tb with
      | Success recursive => Success (new::recursive)
      | Error e => Error e
      end
    | Error e => Error e
    end
  | _, _ => Error "Matrix addition: matrices must have the same shape"
  end.

(*scales the matrix by a factor s*)
Definition scale_matrix_int64 (a: matrix int64) (s: int64) : error_option (matrix int64) :=
  let z_matrix := map (map Z_of_int64) a in
  let scaled_z_matrix := map (map (Z.mul (Z_of_int64 s))) z_matrix in
  let result_option := map (map int64_of_Z) scaled_z_matrix in
  match option_list_of_list_option 
    (map option_list_of_list_option result_option)
  with  
  | Some result => Success result
  | None => Error "Matrix scaling results in overflow"
  end.

(*converts the whole matrix into a readable string*)
Definition string_matrix_of_matrix_int64 (m: matrix int64) : matrix string :=
  map (map string_of_int64) m.
