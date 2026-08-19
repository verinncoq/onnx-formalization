From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.

Open Scope string_scope.

(* 
   Dune has a bug where it cannot distinguish between proper Rocq imports and Rocq imports 
   wrapped in a string. This functions helps to avoid a problem.
*)

(*Adds a linefeed at the end of the string*)
Definition add_linefeed (s: string) : string := s ++ String (ascii_of_nat 10) EmptyString.
