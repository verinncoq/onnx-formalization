From Stdlib Require Import String Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.

(*Definition of bytes as a list of byte*)
Definition bytes := list byte.


(*Convert from string*)

(*Converts an ascii character into a bool, if and only if the ascii character is 0 or 1*)
Definition bit_of_ascii (a: ascii) : option bool :=
  match a with
  | "0"%char => Some false
  | "1"%char => Some true
  | _ => None
  end.

(*helper for bytes_of_string*)
Fixpoint bytes_of_string_recursive (s: list ascii) : option bytes :=
  match s with
  | [] => Some []
  | b0::b1::b2::b3::b4::b5::b6::b7::t =>
    match (bit_of_ascii b0), (bit_of_ascii b1), (bit_of_ascii b2), (bit_of_ascii b3), (bit_of_ascii b4), (bit_of_ascii b5), (bit_of_ascii b6), (bit_of_ascii b7) with
    | Some bit0, Some bit1, Some bit2, Some bit3, Some bit4, Some bit5, Some bit6, Some bit7 =>
      let new_byte := of_bits (bit7, (bit6, (bit5, (bit4, (bit3, (bit2, (bit1, bit0))))))) in
      match bytes_of_string_recursive t with
      | Some b => Some (new_byte::b)
      | None => None
      end
    | _, _, _, _, _, _, _, _ => None
    end
  | _ => None (*not exaclty 8 more, should never happen*)
  end.

(*
Converts a string into a bytes element, if the string consists of only zeros and ones.
The length of the string must be divisible by eigth.
*)
Definition bytes_of_string (s: list ascii) : option bytes :=
  match (length s) mod 8 with
  | 0 => bytes_of_string_recursive s
  | _ => None
  end.

(*Convert to list bool*)

(*Converts a bytes element into a list of bools*)
Fixpoint list_bool_of_bytes (b: bytes) : list bool :=
  match b with
  | [] => []
  | h::t =>
    let bits := to_bits h in
    let (b0, r0) := bits in
    let (b1, r1) := r0 in
    let (b2, r2) := r1 in
    let (b3, r3) := r2 in
    let (b4, r4) := r3 in
    let (b5, r5) := r4 in
    let (b6, b7) := r5 in
    b7::b6::b5::b4::b3::b2::b1::b0::(list_bool_of_bytes t)
  end.

(*Converts a bool into the ascii character zero or one*)
Definition ascii_of_bit (b: bool) : ascii :=
  match b with
  | false => "0"%char
  | true => "1"%char
  end.


(*Convert to string*)

(*Converts a list of bools into a string, consisting only of zeros and ones*)
Definition string_of_list_bool (l: list bool) : list ascii := map ascii_of_bit l.

(*Converts a bytes element into a string consisting only of zeros and ones*)
Definition string_of_bytes (b: bytes) : string := string_of_list_ascii (string_of_list_bool (list_bool_of_bytes b)).