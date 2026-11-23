(** * Elaboration of literals

    The parser keeps every token as its lexeme (a string), exactly as in
    grammar.cf and BNFC. This file gives those strings their meaning:
    a Number lexeme becomes an exact decimal, a VersionToken a pair of numbers. *)
From Stdlib Require Import String Ascii List NArith ZArith QArith.
Import ListNotations.
From ONNXFormalization.VNNLIB.Parser Require Import Ast.

(** An exact decimal: value = (-1)^dneg * dmant / 10^dscale.
    "-0.50" is {| dneg := true; dmant := 50; dscale := 2 |}. No rounding ever. *)
Record decimal := { dneg : bool; dmant : N; dscale : nat }.

Definition digit (c : ascii) : option N :=
  let n := nat_of_ascii c in
  if (Nat.leb 48 n && Nat.leb n 57)%bool then Some (N.of_nat (n - 48)) else None.

(** Read digits while they come: returns (value so far, number of digits read, rest). *)
Fixpoint digits (l : list ascii) (acc : N) (k : nat) : N * nat * list ascii :=
  match l with
  | c :: r => match digit c with
              | Some d => digits r (10 * acc + d)%N (S k)
              | None => (acc, k, l)
              end
  | [] => (acc, k, [])
  end.

(* LBNF: position token Number '-'? digit+ ('.' digit+)? ; *)
Definition decimal_of_number (s : Number) : option decimal :=
  let l := list_ascii_of_string s in
  let '(neg, l) := match l with "-"%char :: r => (true, r) | _ => (false, l) end in
  match digits l 0%N 0 with
  | (m, S _, []) => Some {| dneg := neg; dmant := m; dscale := 0 |}
  | (m, S _, "."%char :: r) =>
      match digits r m 0 with
      | (m', S k, []) => Some {| dneg := neg; dmant := m'; dscale := S k |}
      | _ => None
      end
  | _ => None
  end.

(* LBNF: position token VersionToken '<' digit+ '.' digit+ '>' ; *)
Definition version_of_token (s : VersionToken) : option (N * N) :=
  match list_ascii_of_string s with
  | "<"%char :: r =>
      match digits r 0%N 0 with
      | (major, S _, "."%char :: r') =>
          match digits r' 0%N 0 with
          | (minor, S _, [">"%char]) => Some (major, minor)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(** The value of a decimal as a rational number (Stdlib QArith). *)
Definition decimal_to_Q (d : decimal) : Q :=
  let z := Z.of_N (dmant d) in
  Qmake (if dneg d then Z.opp z else z) (Nat.iter (dscale d) (Pos.mul 10) 1%positive).
