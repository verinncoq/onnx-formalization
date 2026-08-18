From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import BinNat.
From Stdlib Require Import Numbers.NatInt.NZDiv.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From Flocq Require Import Bits BinarySingleNaN.

From ONNXFormalization.External Require Export bitstrings.
From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.External Require Export unpack.

From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.

From ONNXFormalization.ONNXConverter Require Export bytes_decoder.


(*little helpers*)

Definition string_of_bool (b: bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Definition little_endian (b: bytes) : bytes := rev b.


(*Functions to convert a single element*)

(*
Converts a string of length 32 consisting of 0 and 1 into a float.
This calls the IEEE standard for Floating-Point arithmetic (IEEE 754) for 32-bits in little-endian order.
If any requirement does not hold, Error is returned. Borrowed from leo/helpers/functions/IEEE754.v
*)
Definition IEEE754_decomposed (bitstring: string) : error_option float32 :=
  match String.length bitstring with
  | 32%nat => match list_bool_of_string bitstring with
    | Error e => Error e
    | Success l => Success (b32_of_bits (Z.of_N (binstring_to_N l)))
    end
  | _ => Error "IEEE754: The bitstring must contain exactly 32 bits."
  end.

(*Converts a byte to a bool, as descibes in onnx.proto: '00000001 for true, 00000000 for false'*)
Definition bool_of_byte (b: byte) : error_option bool :=
  match b with
  | x00 => Success false
  | x01 => Success true
  | _ => Error "Byte which gets interpreted as a bool must always be either x00 or x01"
  end.




(*Functions to convert multiple elements*)

Definition float32_of_bytes (b: bytes) : error_option (list float32) :=
  list_error_option_to_error_option_list (map IEEE754_decomposed (map string_of_bytes (map little_endian (fourPacks b)))).

Definition bool_of_bytes (b: bytes) : error_option (list bool) :=
  list_error_option_to_error_option_list (map bool_of_byte (b)).

(*Converts four bytes to a int32, in little endian order*)
Fixpoint int32_of_bytes (b: bytes) : error_option (list int32) := 
  match b with
  | [] => Success []
  | b1::b2::b3::b4::tail => match int32_of_bytes tail with
    | Success ints => Success ((b4, b3, b2, b1)::ints)
    | Error e => Error e
    end
  | _ => Error "Not exaclty four Bytes for int32 found"
  end.

(*Converts eight bytes to a int64, in little endian order*)
Fixpoint int64_of_bytes (b: bytes) : error_option (list int64) := 
  match b with
  | [] => Success []
  | b1::b2::b3::b4::b5::b6::b7::b8::tail => match int64_of_bytes tail with
    | Success ints => Success ((b8, b7, b6, b5, b4, b3, b2, b1)::ints)
    | Error e => Error e
    end
  | _ => Error "Not exaclty eight Bytes for int64 found"
  end.





(*Functions to convert multiple elements to strings*)

Definition float32_string_of_bytes (b: bytes) : error_option (list string) :=
  match float32_of_bytes b with
  | Success f => Success (map string_of_float32 f)
  | Error e => Error e
  end.

Definition bool_string_of_bytes (b: bytes) : error_option (list string) :=
  match bool_of_bytes b with
  | Success bools => Success (map string_of_bool bools)
  | Error e => Error e
  end.

Definition int32_string_of_bytes (b: bytes) : error_option (list string) :=
  match int32_of_bytes b with
  | Success ints => Success (map string_of_int32 ints)
  | Error e => Error e
  end.

Definition int64_string_of_bytes (b: bytes) : error_option (list string) :=
  match int64_of_bytes b with
  | Success ints => Success (map string_of_int64 ints)
  | Error e => Error e
  end.
