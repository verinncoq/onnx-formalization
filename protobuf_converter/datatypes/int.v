From Coq Require Import String Ascii.
From Coq Require Import Lists.List. Import ListNotations.
Require Import ZArith Init.Byte Strings.Byte.

From CoqE2EAI Require Import string_to_number.
From CoqE2EAI Require Import stringifyN.


Open Scope Z_scope.

(*Definitions*)

(*32 bits*)

(*maximum value of an unsigned integer with 32 bits [(2^32)-1]*)
Definition uint32_max := (Zpos (shift 32 1)) - 1.

(*minimum value of an signed integer with 32 bits [-(2^31)]*)
Definition int32_min := Zneg (shift 31 1).

(*maximum value of an signed integer with 32 bits [(2^31)-1]*)
Definition int32_max := (Zpos (shift 31 1)) - 1.

(*implementation of a unsigned integer with 32 bits as a tuple of 4 bytes*)
Definition uint32 : Type := (byte * byte * byte * byte).

(*
Implementation of a signed integer with 32 bits as a tuple of 4 bytes.
It uses two's complement representation.
*)
Definition int32 : Type := (byte * byte * byte * byte).


(*64 bits*)

(*maximum value of an unsigned integer with 64 bits [(2^64)-1]*)
Definition uint64_max := (Zpos (shift 64 1)) - 1.

(*minimum value of an signed integer with 64 bits [-(2^63)]*)
Definition int64_min := Zneg (shift 63 1).

(*maximum value of an signed integer with 64 bits [(2^63)-1]*)
Definition int64_max := (Zpos (shift 63 1)) - 1.

(*implementation of a unsigned integer with 64 bits as a tuple of 8 bytes*)
Definition uint64 : Type := (byte * byte * byte * byte * byte * byte * byte * byte).

(*
Implementation of a signed integer with 64 bits as a tuple of 8 bytes.
It uses two's complement representation.
*)
Definition int64 : Type := (byte * byte * byte * byte * byte * byte * byte * byte).



(*Convert Z to int*)

(*helper*)
Definition N_of_Z (z: Z) : option N :=
  match z with
  | Z0 => Some N0
  | Zpos p => Some (Npos p)
  | Zneg _ => None
  end.

(*
Determies if z is between min and max.
If z is exactly min or max, the result is also true.
*)
Definition in_range (z min max : Z) : bool :=
  andb (Z.leb min z) (Z.leb z max).

Open Scope byte_scope.

(*
Converts a Z into a unsigned integer with 32 bits.
If the input is out of the bounds, None is returned.
*)
Definition uint32_of_Z (z: Z) : option uint32 :=
  match in_range z 0 uint32_max with
  | true =>
    let z_0 := z mod 256 in
    let z_1 := (z/256) mod 256 in
    let z_2 := (z/(256*256)) mod 256 in
    let z_3 := (z/(256*256*256)) mod 256 in
    match (N_of_Z z_0), (N_of_Z z_1), (N_of_Z z_2), (N_of_Z z_3) with
    | Some n_0, Some n_1, Some n_2, Some n_3 =>
      match (of_N n_0), (of_N n_1), (of_N n_2), (of_N n_3) with
      | Some b0, Some b1, Some b2, Some b3 => Some (b3, b2, b1, b0)
      | _, _, _, _ => None
      end
    | _, _, _, _ => None
    end
  | false => None
  end.

(*
Converts a Z into a unsigned integer with 64 bits.
If the input is out of the bounds, None is returned.
*)
Definition uint64_of_Z (z: Z) : option uint64 :=
  match in_range z 0 uint64_max with
  | true =>
    let z_0 := z mod 256 in
    let z_1 := (z/256) mod 256 in
    let z_2 := (z/(256*256)) mod 256 in
    let z_3 := (z/(256*256*256)) mod 256 in
    let z_4 := (z/(256*256*256*256)) mod 256 in
    let z_5 := (z/(256*256*256*256*256)) mod 256 in
    let z_6 := (z/(256*256*256*256*256*256)) mod 256 in
    let z_7 := (z/(256*256*256*256*256*256*256)) mod 256 in
    match (N_of_Z z_0), (N_of_Z z_1), (N_of_Z z_2), (N_of_Z z_3), (N_of_Z z_4), (N_of_Z z_5), (N_of_Z z_6), (N_of_Z z_7) with
    | Some n_0, Some n_1, Some n_2, Some n_3, Some n_4, Some n_5, Some n_6, Some n_7 =>
      match (of_N n_0), (of_N n_1), (of_N n_2), (of_N n_3), (of_N n_4), (of_N n_5), (of_N n_6), (of_N n_7) with
      | Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 => Some (b7, b6, b5, b4, b3, b2, b1, b0)
      | _, _, _, _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _, _ => None
    end
  | false => None
  end.

(*
Converts a Z into a signed integer with 32 bits.
If the input is out of the bounds, None is returned.
If the input is positive, convertion happens with the function for the unsigned version
(because the input is inside the bounds, the first bit will never be set for a positive input).
If the input is negative, its absolute value gets substracted from the maximum for unsigend integers + 1.
Then, again, convertion happens with the function for the unsigned version.
Example: z = -1, the value (uint32_max + 1) - 1 = uint32_max gets converted,
which is every bit 1 (11111111 11111111 11111111 11111111).
This is the two's complement representation for -1.
Example: z = -2, the value (uint32_max + 1) - 2 = uint32_max - 1 gets converted,
which is every bit 1 except for the last one (11111111 11111111 11111111 11111110).
This is the two's complement representation for -2.
*)
Definition int32_of_Z (z: Z) : option int32 :=
  match in_range z int32_min int32_max with
  | true =>
    match z with
    | Zneg p => uint32_of_Z ((uint32_max + 1) - (Zpos p))
    | _ => uint32_of_Z z
    end
  | false => None
  end.

(*
Converts a Z into a signed integer with 64 bits.
It works exaclty as int32_of_Z defined and documented above.
*)
Definition int64_of_Z (z: Z) : option int64 :=
  match z with
  | Zneg p => uint64_of_Z ((uint64_max + 1) - (Zpos p))
  | _ => uint64_of_Z z
  end.



(*Convert int to Z*)

(*Converts an uint32 into a Z*)
Definition Z_of_uint32 (i: uint32) : Z :=
  let (r0, b0) := i in
  let (r1, b1) := r0 in
  let (b3, b2) := r1 in
  (
  256*256*256*(Z.of_N (to_N b3)) +
  256*256*(Z.of_N (to_N b2)) +
  256*(Z.of_N (to_N b1)) +
  Z.of_N (to_N b0)
  ).

(*
Converts an int32 into a Z.
First, its converted using the function for the unsigned version.
If the result is lower than the bounds, its gets returned.
If the result is larger than the bounds, it must be negative,
so the upper bound of the unsiged version gets substracted.
*)
Definition Z_of_int32 (i: int32) : Z :=
  let z := Z_of_uint32 i in
  match Z.leb z int32_max with
  | true => z
  | false => z - uint32_max - 1
  end.

(*Converts an uint64 into a Z*)
Definition Z_of_uint64 (i: uint64) : Z :=
  let (r0, b0) := i in
  let (r1, b1) := r0 in
  let (r2, b2) := r1 in
  let (r3, b3) := r2 in
  let (r4, b4) := r3 in
  let (r5, b5) := r4 in
  let (b7, b6) := r5 in
  (
  256*256*256*256*256*256*256*(Z.of_N (to_N b7)) +
  256*256*256*256*256*256*(Z.of_N (to_N b6)) +
  256*256*256*256*256*(Z.of_N (to_N b5)) +
  256*256*256*256*(Z.of_N (to_N b4)) +
  256*256*256*(Z.of_N (to_N b3)) +
  256*256*(Z.of_N (to_N b2)) +
  256*(Z.of_N (to_N b1)) +
  Z.of_N (to_N b0)
  ).

(*
Converts an int64 into a Z.
First, its converted using the function for the unsigned version.
If the result is lower than the bounds, its gets returned.
If the result is larger than the bounds, it must be negative,
so the upper bound of the unsiged version gets substracted.
*)
Definition Z_of_int64 (i: int64) : Z :=
  let z := Z_of_uint64 i in
  match Z.leb z int64_max with
  | true => z
  | false => z - uint64_max - 1
  end.


(*Convert string to int*)

(*
Converts a string into an uint32.
The string is converted into a Z,
then the result is converted into an uint32 with the function defined above.
*)
Definition uint32_of_string (s: list ascii) : option uint32 :=
  match Z_of_string s with
  | Some z => uint32_of_Z z
  | None => None
  end.

(*
Converts a string into an uint64.
The string is converted into a Z,
then the result is converted into an uint64 with the function defined above.
*)
Definition uint64_of_string (s: list ascii) : option uint64 :=
  match Z_of_string s with
  | Some z => uint64_of_Z z
  | None => None
  end.

(*
Converts a string into an int32.
The string is converted into a Z,
then the result is converted into an int32 with the function defined above.
*)
Definition int32_of_string (s: list ascii) : option int32 :=
  match Z_of_string s with
  | Some z => int32_of_Z z
  | None => None
  end.

(*
Converts a string into an int64.
The string is converted into a Z,
then the result is converted into an int64 with the function defined above.
*)
Definition int64_of_string (s: list ascii) : option int64 :=
  match Z_of_string s with
  | Some z => int64_of_Z z
  | None => None
  end.

(*convert int to string*)

(*
Converts an uint32 into a string.
The uint32 is first converted into a Z using the function defined above.
Then, it gets converted to a string.
The depth parameter is choosen to be 11,
because the maximum value for uint32 has 10 digits.
*)
Definition string_of_uint32 (i: uint32) : string :=
  match N_of_Z (Z_of_uint32 i) with
  | Some n => writeN 11 n
  | None => "NaN"
  end.

(*
Converts an uint64 into a string.
The uint64 is first converted into a Z using the function defined above.
Then, it gets converted to a string.
The depth parameter is choosen to be 21,
because the maximum value for uint64 has 20 digits.
*)
Definition string_of_uint64 (i: uint64) : string :=
  match N_of_Z (Z_of_uint64 i) with
  | Some n => writeN 21 n
  | None => "NaN"
  end.

(*
Converts an int32 into a string.
The int32 is first converted into a Z using the function defined above.
Then, it's absolute value gets converted to a string.
The depth parameter is choosen to be 11,
because the maximum value for int32 has 10 digits.
If the Z value was negative, "-" gets appended in front
*)
Definition string_of_int32 (i: int32) : string :=
  match Z_of_int32 i with
  | Z0 => "0"
  | Zpos p => writeN 11 (Npos p)
  | Zneg p => "-" ++ writeN 11 (Npos p)
  end.

(*
Converts an int64 into a string.
The int64 is first converted into a Z using the function defined above.
Then, it's absolute value gets converted to a string.
The depth parameter is choosen to be 21,
because the maximum value for int64 has 19 digits.
If the Z value was negative, "-" gets appended in front
*)
Definition string_of_int64 (i: int64) : string :=
  match Z_of_int64 i with
  | Z0 => "0"
  | Zpos p => writeN 21 (Npos p)
  | Zneg p => "-" ++ writeN 21 (Npos p)
  end.