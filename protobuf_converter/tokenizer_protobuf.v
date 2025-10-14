From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.


(*Source: https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)) (* Carriage return. *).

(*returns true if c is not space, tab, linefeed or carriage return*)
Definition isNotWhite (c: ascii): bool :=
  negb (isWhite c).

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isLeftBrace (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 123.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isRightBrace (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 125.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isSemicolon (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 59.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isEqualSign (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 61.

(*reverses a string*)
Fixpoint reverse_string (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a s' => reverse_string s' ++ String a EmptyString
  end.

(*
Splits a string at all characters where f evaluates to true.
Those characters are put in an extra string
*)
Fixpoint split_string (f: ascii->bool) (z s: string): list string :=
let revz := match z with EmptyString => [EmptyString] | String _ _ => [reverse_string z] end in
match s with
| EmptyString => revz
| String a s' => match f a with
  | true => (revz ++ [String a EmptyString]) ++ (split_string f EmptyString s')
  | false => (split_string f (String a z) s')
  end
end.

(*maps split_string on multiple strings*)
Fixpoint split_strings (f: ascii->bool) (s: list string): list (string) :=
match s with
| [] => []
| h::t => (split_string f EmptyString h) ++ (split_strings f t)
end.

(*returns true if the s does not consist of only white characters (space, tab, linefeed or carriage return)*)
Definition no_only_white (s: string): bool :=
negb (forallb isWhite (list_ascii_of_string s)).


(*
Tokenizer funktion. Takes a string and returns a list of string, containing the tokens.
Splits at semicolons, curly brackets equal signs and white characters (space, tab, linefeed or carriage return).
*)
Definition tokenize(s: string): list (string) :=
  filter no_only_white (
      split_strings isSemicolon (
        split_strings isRightBrace (
          split_strings isLeftBrace (
            split_strings isEqualSign (
              split_string isWhite EmptyString s
))))).

(*
Definition test := "message TensorShapeProto {
  message Dimension {
    oneof value {
      int64 dim_value = 1;
      string dim_param = 2;
    };
    optional string denotation = 3;
  };
  repeated Dimension dim = 1;
}"%string.

Compute tokenize test.*)