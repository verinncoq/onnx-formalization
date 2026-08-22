From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Nat.
Open Scope string_scope.

From ONNXFormalization.External Require Export escapeSequenceExtractor.

From ONNXFormalization.ProtobufDatatypes Require Export bytes.

(*decodes a bytes string with escape sequences into a string consisting of 0 and 1*)
Definition decode_bytes (s: string) : error_option string :=
  match escapeSequenceExtractor (list_ascii_of_string s) with
  | Success s => Success (string_of_bytes (map byte_of_ascii s))
  | Error e => Error e
  end.

Open Scope nat_scope.

(*many functions taken from leo/preprocessing/raw_data_converter.v*)

Definition isWhite (c : ascii) : bool :=
  let n := Ascii.nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)) (* Carriage return. *)
  .

(*Removes all white characters at the beginning of s.*)
Fixpoint removeWhitesAtBeginning (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => match isWhite c with
                   | true  => removeWhitesAtBeginning s'
                   | false => s
                   end
  end.

Open Scope string_scope.
(*returns true if line contins s field*)
Definition is_s (s: string) : bool :=
  let raw_data_possible := substring 0 2 (removeWhitesAtBeginning s) in
  raw_data_possible =? "s:".

(*returns true if line contins strings field*)
Definition is_strings (s: string) : bool :=
  let raw_data_possible := substring 0 7 (removeWhitesAtBeginning s) in
  raw_data_possible =? "strings".

(*returns true if line contins string_data field*)
Definition is_string_data (s: string) : bool :=
  let raw_data_possible := substring 0 11 (removeWhitesAtBeginning s) in
  raw_data_possible =? "string_data".

(*returns true if line contins raw_data field*)
Definition is_raw_data (s: string) : bool :=
  let raw_data_possible := substring 0 8 (removeWhitesAtBeginning s) in
  raw_data_possible =? "raw_data".

(*Removes n chars (if possible) at the beginning of s.*)
Fixpoint remove_at_beginning (s: string) (n: nat) : string :=
  match n with
  | O    => s
  | S n' => match s with
           | EmptyString => s
           | String c s' => remove_at_beginning s' n'
           end
  end.

Definition reverse_string (s: string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

(*Removes n chars (if possible) at the end of s.*)
Definition remove_at_end (s: string) (n: nat) : string :=
  reverse_string (remove_at_beginning (reverse_string s) n).

(*Returns the content of the raw_data field in a line.*)
Definition extract_field (s: string) : string :=
  remove_at_end (remove_at_beginning (removeWhitesAtBeginning s) 11) 1.

(*Adds a field to the bits to make it readable for the tokenizer.*)
Definition rearrange_s (s: string) : string :=
  ("s: " ++ s) ++ "
  ".

(*Adds a field to the bits to make it readable for the tokenizer.*)
Definition rearrange_strings (s: string) : string :=
  ("strings: " ++ s) ++ "
  ".

(*Adds a field to the bits to make it readable for the tokenizer.*)
Definition rearrange_string_data (s: string) : string :=
  ("string_data: " ++ s) ++ "
  ".

(*Adds a field to the bits to make it readable for the tokenizer.*)
Definition rearrange_raw_data (s: string) : string :=
  ("raw_data: " ++ s) ++ "
  ".

(*Converts a line (with or without s field) into bytes.*)
Definition convert_line_s (s: string) : error_option string :=
  match is_s s with
  | false => Success s
  | true  => match (decode_bytes (extract_field s)) with
             | Error e => Error e
             | Success s => Success (rearrange_s s)
             end
  end.

(*Converts a line (with or without raw_data field) into bytes.*)
Definition convert_line_strings (s: string) : error_option string :=
  match is_strings s with
  | false => Success s
  | true  => match (decode_bytes (extract_field s)) with
             | Error e => Error e
             | Success s => Success (rearrange_strings s)
             end
  end.

(*Converts a line (with or without raw_data field) into bytes.*)
Definition convert_line_string_data (s: string) : error_option string :=
  match is_string_data s with
  | false => Success s
  | true  => match (decode_bytes (extract_field s)) with
             | Error e => Error e
             | Success s => Success (rearrange_string_data s)
             end
  end.

(*Converts a line (with or without raw_data field) into bytes.*)
Definition convert_line_raw_data (s: string) : error_option string :=
  match is_raw_data s with
  | false => Success s
  | true  => match (decode_bytes (extract_field s)) with
             | Error e => Error e
             | Success s => Success (rearrange_raw_data s)
             end
  end.

Definition convert_line (s: string) : error_option string :=
  match convert_line_s s with
  | Success s => match convert_line_strings s with
    | Success s => match convert_line_string_data s with
      | Success s => convert_line_raw_data s
      | Error e => Error e
      end
    | Error e => Error e
    end
  | Error e => Error e
  end.

(*
Helper for split_lines.
Is called by that function.
Should not be called manually.
*)
Fixpoint split_lines_rec (s buf: string) : list string :=
  match s with
  | EmptyString => [buf]
  | String c s' => match c with
                   | "010"%char => buf::(split_lines_rec s' EmptyString) (*linefeed*)
                   | _          => split_lines_rec s' (buf ++ (String c EmptyString))
                   end
  end.

(*Splits a string by linefeed characters*)
Definition split_lines (s: string) : list string := split_lines_rec s EmptyString.

Definition bytes_decoder (s: list ascii) : error_option (list ascii) :=
  let lines := split_lines (string_of_list_ascii s) in
  let convertion := list_error_option_to_error_option_list (map convert_line lines) in
  match convertion with
  | Error e => Error e
  | Success s => let seperator := String "010"%char EmptyString in (*linefeed*)
                 Success (list_ascii_of_string (String.concat seperator s))
  end.