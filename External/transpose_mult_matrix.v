From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Nat.

(*file useful when executing output file of converter*)

From Coquelicot Require Import Coquelicot.

From ONNXFormalization.External Require Import neural_networks piecewise_affine.
From ONNXFormalization.External Require Import string_to_number.

Definition transpose {n m}(matrix: matrix n m) := mk_matrix m n (fun i j => coeff_mat (real_of_string "0"%string) matrix j i).
