From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.

(*concats lists with adding commas*)
Fixpoint listToString (l: list (list ascii)) : list ascii :=
match l with
| [] => []
| [h] => h
| h::t => h ++ (list_ascii_of_string ", ") ++ (listToString t)
end.