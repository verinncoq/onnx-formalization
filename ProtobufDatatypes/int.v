From Stdlib Require Import String Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.

From ONNXFormalization.External Require Import string_to_number.
From ONNXFormalization.External Require Import stringifyN.


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
If the input is out of the bounds, it overflows, i.e. it is taken modulo 2^32.
*)
Definition uint32_of_Z (z: Z) : uint32 :=
  let byte_of (z' : Z) : byte :=
    match of_N (Z.to_N (z' mod 256)) with
    | Some b => b
    | None => x00
    end in
  let b0 := byte_of z in
  let b1 := byte_of (z/256) in
  let b2 := byte_of (z/(256*256)) in
  let b3 := byte_of (z/(256*256*256)) in
  (b3, b2, b1, b0).

(*
Converts a Z into a unsigned integer with 64 bits.
If the input is out of the bounds, it overflows, i.e. it is taken modulo 2^64.
*)
Definition uint64_of_Z (z: Z) : uint64 :=
  let byte_of (z' : Z) : byte :=
    match of_N (Z.to_N (z' mod 256)) with
    | Some b => b
    | None => x00
    end in
  let b0 := byte_of z in
  let b1 := byte_of (z/256) in
  let b2 := byte_of (z/(256*256)) in
  let b3 := byte_of (z/(256*256*256)) in
  let b4 := byte_of (z/(256*256*256*256)) in
  let b5 := byte_of (z/(256*256*256*256*256)) in
  let b6 := byte_of (z/(256*256*256*256*256*256)) in
  let b7 := byte_of (z/(256*256*256*256*256*256*256)) in
  (b7, b6, b5, b4, b3, b2, b1, b0).

(*
Converts a Z into a signed integer with 32 bits.
If the input is out of the bounds, it overflows (wraps around) like a
two's complement integer.
Since uint32_of_Z takes its input modulo 2^32 and Z.modulo by a positive
number is never negative, a negative z is converted to (uint32_max + 1) + z.
Example: z = -1, the value (uint32_max + 1) - 1 = uint32_max gets converted,
which is every bit 1 (11111111 11111111 11111111 11111111).
This is the two's complement representation for -1.
Example: z = -2, the value (uint32_max + 1) - 2 = uint32_max - 1 gets converted,
which is every bit 1 except for the last one (11111111 11111111 11111111 11111110).
This is the two's complement representation for -2.
*)
Definition int32_of_Z (z: Z) : int32 := uint32_of_Z z.

(*
Converts a Z into a signed integer with 64 bits.
It works exaclty as int32_of_Z defined and documented above.
*)
Definition int64_of_Z (z: Z) : int64 := uint64_of_Z z.



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
  | Some z => Some (uint32_of_Z z)
  | None => None
  end.

(*
Converts a string into an uint64.
The string is converted into a Z,
then the result is converted into an uint64 with the function defined above.
*)
Definition uint64_of_string (s: list ascii) : option uint64 :=
  match Z_of_string s with
  | Some z => Some (uint64_of_Z z)
  | None => None
  end.

(*
Converts a string into an int32.
The string is converted into a Z,
then the result is converted into an int32 with the function defined above.
*)
Definition int32_of_string (s: list ascii) : option int32 :=
  match Z_of_string s with
  | Some z => Some (int32_of_Z z)
  | None => None
  end.

(*
Converts a string into an int64.
The string is converted into a Z,
then the result is converted into an int64 with the function defined above.
*)
Definition int64_of_string (s: list ascii) : option int64 :=
  match Z_of_string s with
  | Some z => Some (int64_of_Z z)
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
