From Stdlib Require Import String Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.
From Flocq Require Import Bits BinarySingleNaN.

From ONNXFormalization.External Require Import string_to_number.
From ONNXFormalization.External Require Import stringifyN.

(*Convert string to float decomposition (i.e. sign, exponent and mantissa)*)

Open Scope Z_scope.

(*splits a string into two parts, the delimiter is the first dot, which gets removed*)
Fixpoint split_at_dot (s buffer: string): (string * string) :=
  match s with
  | EmptyString => match buffer with
    | ""%string => ("0"%string, "0"%string)
    | _ => (buffer, "0"%string)
    end
  | String a s' => match a with
            | "."%char => match buffer with
              | ""%string => ("0"%string, s')
              | _ => (buffer, s')
              end
            | _ => split_at_dot s' (buffer ++ (String a EmptyString))
            end
  end.

(*
Splits a string representing a float into four parts:
1. The sign (- true; + false)
2. The part before the dot as a Z
3. The part after the dot as a Z
4. The amout of digits used to represent the part after the dot in the input
*)
Definition decompose_float_string (s: string) : option (bool * Z * Z * nat) :=
  match s with
  | EmptyString => None
  | String a s' => let (sign, rest) := match a with
    | "-"%char => (true, s')
    | _ => (false, s)
    end in
    let (before, after) := split_at_dot rest "" in
    match Z_of_string (list_ascii_of_string before) with
    | Some before_nat => match Z_of_string (list_ascii_of_string after) with
      | Some after_nat => 
      Some (sign, before_nat, after_nat, length (list_ascii_of_string after))
      | None => None
      end
    | None => None
    end
  end.

(*
Converts a decimal number into a binary number.
The binary number is represented as a list of bools.
The depth parameter is used to give rocq a structural recursion.
It must be greater than the entries in the output list.
If not, the output is None.
This functions devides the input by two as long as the result is not zero.
The remainders of the devision form the output.
*)
Fixpoint dec_to_bin_greater_one (depth: nat) (dec: Z) : option (list bool) :=
  match depth with
  | O => None
  | S n => match dec with
    | 0 => Some []
    | _ => match dec_to_bin_greater_one n (dec/2) with
      | Some recursive => match dec mod 2 with
        | 1 => Some (recursive ++ [true])
        | 0 => Some (recursive ++ [false])
        | _ => None
        end
      | None => None
      end
    end
  end.

(*
Converts a decimal number into a binary number.
The decimal number represents the part of another decimal number after the dot
(one could read both the in- and output starting with "0.").
The binary number is represented as a list of bools.
The depth parameter is used to give rocq a structural recursion.
It must be as large as the entries in the output list.
If not, the output is rounded to the nearest value.
The delimiter parameter should be the first power of ten greater than dec
(if dec is 75, delimiter should be 100).
This functions multiplies the input by two and checks if the result is greater or equal than the delimiter.
If so, add a true (1), if not, a false (0) and continue on the result mod delimiter.
Example: dec := 25, delimiter := 100.
dec * 2 = 50 => less than delimiter, add false (0)
continue with dec := 50 mod 100 = 50, delimiter := 100
dec * 2 = 100 => greater or equal than delimiter, add true (0)
continue with dec := 100 mod 100 = 0, delimiter := 100
finish, because dec is 0
result: 01, because 0.25 in decimal is 0.01 in binary
*)
Fixpoint dec_to_bin_less_one (depth: nat) (dec delimiter: Z) : option (list bool) :=
  match depth with
  | O => Some []
  | S n => match dec with
    | 0 => Some []
    | _ => let times_two := dec * 2 in
      match dec_to_bin_less_one n (times_two mod delimiter) delimiter with
      | Some recursive => match delimiter <=? times_two with
        | true => Some (true::recursive)
        | false => Some (false::recursive)
        end
      | None => None
      end
    end
  end.

(*
Takes a string representing a float and splits it into three parts:
1. Sign (bool)
2. Part before the dot in binary (list bool)
3. Part after  the dot in binary (list bool)
The parameter depth must be:
1. greater than the length of list in part 2
2. greater or equal than the length of list in part 3
If 1 does not hold, None is returned. If 2 does not hold, the output is rounded to the nearest value.
*)
Definition string_to_binstring (depth: nat) (s: string) : option (bool * (list bool) * (list bool)) :=
  match decompose_float_string s with
  | None => None
  | Some (sign, greater_one, less_one, less_one_length) =>
    match dec_to_bin_greater_one depth greater_one with
    | None => None
    | Some greater_one_list => match dec_to_bin_less_one depth less_one (Z.of_N (N.pow 10 (N.of_nat less_one_length))) with
      | None => None
      | Some less_one_list => Some (sign, greater_one_list, less_one_list)
      end
    end
  end.

(*helper for binstring_to_N*)
Fixpoint binstring_to_N_recursive (binstring: list bool) : N :=
  match binstring with
  | [] => 0
  | h::t => match h with
    | true => 1 + (2 * binstring_to_N_recursive t)
    | false => 0 + (2 * binstring_to_N_recursive t)
    end
  end.

(*
Converts a binary number to a natural number.
The binary number is given as a list of booleans.
*)
Definition binstring_to_N (binstring: list bool) : N := binstring_to_N_recursive (rev binstring).

(*helper for binstring_to_N_after_dot*)
Fixpoint binstring_to_N_after_dot_recursive (binstring: list bool) (d: N) : N :=
  match binstring with
  | [] => 0
  | h::t => let d' := (d/2)%N in match h with
    | true => d' + (binstring_to_N_after_dot_recursive t d')
    | false => 0 + (binstring_to_N_after_dot_recursive t d')
    end
  end.

(*
Converts a binary number that represents the part of a float after the dot into a natural number.
The binary number is given as a list of booleans.
*)
Definition binstring_to_N_after_dot (binstring: list bool) := binstring_to_N_after_dot_recursive binstring (N.pow 10 (N.of_nat (length binstring))).


(*
Takes a string representing a float and spilts it into three parts:
1. Sign (bool)
2. Mantissa
3. Exponent
If we compute Mantissa * 2^(Exponent), we get the unsigned input
The parameter depth must be:
1. greater than the binary representation of the part before the dot in the input
2. greater or equal than the binary representation of the part after the dot in the input
If 1 does not hold, None is returned. If 2 does not hold, the output is rounded to the nearest value.
*)
Definition string_to_float_decomposition (depth: nat) (s: string) : option (bool * Z * Z) :=
  match string_to_binstring depth s with
  | None => None
  | Some (sign, before, after) => Some (sign, Z.of_N (binstring_to_N (before ++ after)), -(Z.of_nat (length(after))))
  end.

(*Convert float decomposition (i.e. sign, exponent and mantissa) to string*)

(*
When before and after represent the part of a binary number before and after the dot,
this functions moves the dot one place to the left.
It takes the last element of the before list and puts it before all elements of the after list.
*)
Definition move_dot_left_once (before after: list bool) : (list bool * list bool) :=
  let before_flipped := rev before in
  match before_flipped with
  | [] => (before, false::after)
  | h::t => (rev t, h::after)
  end.

(*
When before and after represent the part of a binary number before and after the dot,
this functions moves the dot 'times' places to the left.
It takes the last element of the before list and puts it before all elements of the after list,
and repeats this 'times' times.
*)
Fixpoint move_dot_left (times: nat) (before after: list bool) : (list bool * list bool) :=
  match times with
  | O => (before, after)
  | S n => let (before', after') := move_dot_left_once before after in
    move_dot_left n before' after'
  end.

(*
When before and after represent the part of a binary number before and after the dot,
this functions moves the dot one place to the right.
It takes the first element of the after list and puts it after all elements of the before list.
*)
Definition move_dot_right_once (before after: list bool) : (list bool * list bool) :=
  match after with
  | [] => (before ++ [false], [])
  | h::t => (before ++ [h], t)
  end.

(*
When before and after represent the part of a binary number before and after the dot,
this functions moves the dot 'times' places to the right.
It takes the first element of the after list and puts it after all elements of the before list,
and repeats this 'times' times.
*)
Fixpoint move_dot_right (times: nat) (before after: list bool) : (list bool * list bool) :=
  match times with
  | O => (before, after)
  | S n => let (before', after') := move_dot_right_once before after in
    move_dot_right n before' after'
  end.

Open Scope string_scope.

(*returns a string consisting of 'times' times the character "0"*)
Fixpoint zeros (times: nat) : string :=
  match times with
  | O => EmptyString
  | S n => String "0"%char (zeros n)
  end.

(*returns a string consisting of (expected_len - result_len) times the character "0"*)
Definition missing_zeros (result_len expected_len: N) : string :=
  match (Z.of_N expected_len) - (Z.of_N result_len) with
  | Z0 => ""
  | Zpos p => zeros (N.to_nat (Npos p))
  | Zneg _ => "Error"
  end.


(*
Takes a float decomposition and converts it into a string. 
A float decomposition consists of:
1. Sign (bool)
2. Mantissa
3. Exponent
First, the mantissa is converted to a binary number
(parameter depth must be greater than the binary representation of the mantissa)
Then, the binary mantissa is interpreted a mantissa.0, and the dot gets moved exponent times.
The direction of the movement is determined by the sign of the exponent (minus to the left, plus to the right).
Then, both the binary part before and after the dot are converted to decimal using their corresponding functions.
Then, both parts are converted into a string.
Here, the depth parameter must be larger than the length of the resulting string minus 2
(If the result is 1500, the depth parameter must be larger than 2).
Then, if leading zeros in the after part are missing, they get appended.
The result is the before and after part concatenated together, with a dot character between them.
*)
Definition float_decomposition_to_string (depth: nat) (sign: bool) (exponent mantissa: Z) : option string :=
  let sign_string := match sign with
  | true => "-"
  | false => ""
  end in
  match dec_to_bin_greater_one depth mantissa with
  | None => None
  | Some binstring => let (before, after_) := match exponent with
    | Z0 => (writeN depth (binstring_to_N binstring), ("", []))
    | Zpos e => let (before', after') := (move_dot_right (Pos.to_nat e) binstring []) in (
      writeN depth (binstring_to_N before'),
      (writeN depth (binstring_to_N_after_dot after'),
      after')
      )
    | Zneg e => let (before', after') := (move_dot_left (Pos.to_nat e) binstring []) in (
      writeN depth (binstring_to_N before'),
      (writeN depth (binstring_to_N_after_dot after'),
      after')
      )
    end in
    let after := fst after_ in
    let after' := snd after_ in
    let zeros := missing_zeros (N.of_nat (length (list_ascii_of_string after))) (N.of_nat (length after')) in
    match after with
    | "" => Some (sign_string ++ before ++ "." ++ zeros ++ "0")
    | _ => Some (sign_string ++ before ++ "." ++ zeros ++ after)
    end
  end.


(*Definitions*)

(*binary32 and binary64 defined in Flocq.IEEE754.Bits*)
(*inspiration: https://discourse.rocq-prover.org/t/how-to-use-binary-floats-in-flocq/2236*)
(*see https://inria.hal.science/hal-04114233/document for mode_NE*)

(*renaming of binary32 for clarity reasons*)
Definition float32 := binary32.

(*renaming of binary64 for clarity reasons*)
Definition float64 := binary64.


(*Converters*)

(*
Converts a string representing a float into a float32.
If the float32 type cannot represent the float, it is rounded to the nearest value.
We choose the depth parameter to be 161 because it is the maximum exponent for the float32 type plus the amount of bits plus one.
*)
Definition float32_of_string (s: list ascii) : option float32 :=
  match string_to_float_decomposition 161 (string_of_list_ascii s) with
  | Some tuple =>
    let sign := (fst (fst tuple)) in
    let mantissa := (snd (fst tuple)) in
    let exponent := (snd tuple) in
    let bin := Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE mantissa exponent sign in
    match sign with
    | false => Some bin
    | true => Some (b32_opp bin)
    end
  | None => None
  end.

(*
Converts a string representing a float into a float64.
If the float64 type cannot represent the float, it is rounded to the nearest value.
We choose the depth parameter to be 1088 because it is the maximum exponent for the float64 type plus the amount of bits plus one.
*)
Definition float64_of_string (s: list ascii) : option float64 :=
  match string_to_float_decomposition 1088 (string_of_list_ascii s) with
  | Some tuple =>
    let sign := (fst (fst tuple)) in
    let mantissa := (snd (fst tuple)) in
    let exponent := (snd tuple) in
    let bin := Binary.binary_normalize 53 1024 eq_refl eq_refl mode_NE mantissa exponent sign in
    match sign with
    | false => Some bin
    | true => Some (b64_opp bin)
    end
  | None => None
  end.

(*
Converts a float32 into a string representing the float.
We choose the depth parameter the be 128 because it is always
greater than the binary representation of the mantissa (float32 uses a 32 bits)
and allways greater than the amount of characters used to represent the float.
*)
Definition string_of_float32 (f: float32) : string :=
  match f with
  | Binary.B754_zero _ _ _ => "0"
  | Binary.B754_infinity _ _ _ => "Inf"
  | Binary.B754_nan _ _ _ _ _ => "NaN"
  | Binary.B754_finite _ _ sign mantissa exponent _ =>
    match float_decomposition_to_string 128 sign exponent (Zpos mantissa) with
    | Some s => s
    | None => "NaN"
    end
  end.

(*
Converts a float64 into a string representing the float.
We choose the depth parameter the be 1024 because it is always
greater than the binary representation of the mantissa (float64 uses a 64 bits)
and allways greater than the amount of characters used to represent the float.
*)
Definition string_of_float64 (f: float64) : string :=
  match f with
  | Binary.B754_zero _ _ _ => "0"
  | Binary.B754_infinity _ _ _ => "Inf"
  | Binary.B754_nan _ _ _ _ _ => "NaN"
  | Binary.B754_finite _ _ sign mantissa exponent _ =>
    match float_decomposition_to_string 1024 sign exponent (Zpos mantissa) with
    | Some s => s
    | None => "NaN"
    end
  end.

(*Converts a float32 into Z, but only if the float has no decimal places*)
Definition Z_of_float32 (f: float32) : option Z :=
  match decompose_float_string (string_of_float32 f) with
  | Some (sign, before, after, _) => match after with
    | 0%Z => match sign with
      | true => Some (-before)
      | false => Some before
      end
    | _ => None (*float is not an integer*)
    end
  | None => None
  end.

(*Converts a float64 into Z, but only if the float has no decimal places*)
Definition Z_of_float64 (f: float64) : option Z :=
  match decompose_float_string (string_of_float64 f) with
  | Some (sign, before, after, _) => match after with
    | 0%Z => match sign with
      | true => Some (-before)
      | false => Some before
      end
    | _ => None (*float is not an integer*)
    end
  | None => None
  end.