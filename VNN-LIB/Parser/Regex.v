(** * Regular expressions

    Grammar-independent, Stdlib only, unverified. Used by Lexer.v to match the
    token regexes of LexSpec.v (transcribed from the [token] lines of grammar.cf).
    One constructor or helper per LBNF regex operator:
      char class -> RCls/RChr/RDigit/RLetter/RUpper/RLower/RAny/RSet,
      sequence -> RSeq, | -> RAlt, * -> RStar, + -> rplus, ? -> ropt,
      difference (r - s) -> RDiff.
    Matching: the derivative of r by c matches exactly the words w such that
    c w is matched by r; a word is matched iff deriving by all its characters
    gives a nullable regex. *)
From Stdlib Require Import String Ascii Bool List.
Import ListNotations.

Inductive regex :=
| REmpty
| REps
| RCls (p : ascii -> bool)          (* one character satisfying p *)
| RSeq (r s : regex)
| RAlt (r s : regex)
| RStar (r : regex)
| RDiff (r s : regex).              (* LBNF difference: matches r but not s *)

Definition in_range (lo hi : nat) (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb lo n && Nat.leb n hi)%bool.
Definition RChr (c : ascii) : regex := RCls (fun d => Ascii.eqb c d).
Definition RAny : regex := RCls (fun _ => true).
Definition RDigit : regex := RCls (in_range 48 57).
Definition RUpper : regex := RCls (in_range 65 90).
Definition RLower : regex := RCls (in_range 97 122).
Definition RLetter : regex := RCls (fun c => in_range 65 90 c || in_range 97 122 c).
Fixpoint mem_string (c : ascii) (s : string) : bool :=
  match s with EmptyString => false | String d r => Ascii.eqb c d || mem_string c r end.
Definition RSet (s : string) : regex := RCls (fun c => mem_string c s).
Fixpoint rstr (s : string) : regex :=
  match s with EmptyString => REps | String c r => RSeq (RChr c) (rstr r) end.
Definition rplus (r : regex) : regex := RSeq r (RStar r).
Definition ropt (r : regex) : regex := RAlt r REps.

(** constructors keep derivatives small and let dead states collapse to REmpty. *)
Definition seq (r s : regex) : regex :=
  match r, s with
  | REmpty, _ | _, REmpty => REmpty
  | REps, _ => s
  | _, REps => r
  | _, _ => RSeq r s
  end.
Definition alt (r s : regex) : regex :=
  match r, s with REmpty, _ => s | _, REmpty => r | _, _ => RAlt r s end.
Definition diff (r s : regex) : regex :=
  match r, s with REmpty, _ => REmpty | _, REmpty => r | _, _ => RDiff r s end.

Fixpoint nullable (r : regex) : bool :=
  match r with
  | REmpty | RCls _ => false
  | REps | RStar _ => true
  | RSeq r s => nullable r && nullable s
  | RAlt r s => nullable r || nullable s
  | RDiff r s => nullable r && negb (nullable s)
  end.

Fixpoint deriv (c : ascii) (r : regex) : regex :=
  match r with
  | REmpty | REps => REmpty
  | RCls p => if p c then REps else REmpty
  | RSeq r s => let d := seq (deriv c r) s in if nullable r then alt d (deriv c s) else d
  | RAlt r s => alt (deriv c r) (deriv c s)
  | RStar r => seq (deriv c r) (RStar r)
  | RDiff r s => diff (deriv c r) (deriv c s)
  end.

Definition is_empty (r : regex) : bool := match r with REmpty => true | _ => false end.

(** Length of the longest prefix of [l] matched by [r] (None if no prefix matches).
    Structural on [l]. *)
Fixpoint longest_aux (r : regex) (l : list ascii) (k : nat) (best : option nat) : option nat :=
  let best := if nullable r then Some k else best in
  if is_empty r then best else
  match l with
  | [] => best
  | c :: l' => longest_aux (deriv c r) l' (S k) best
  end.
Definition longest (r : regex) (l : list ascii) : option nat := longest_aux r l 0 None.
