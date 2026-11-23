(** * Generic longest-match lexer

    Grammar-independent, Stdlib only, unverified. Interprets LexSpec.v.
    At each position: skip whitespace (space, tab, LF, CR) and line comments;
    otherwise take the longest match among all literals and token categories.
    On equal length a literal beats a category, and an earlier category beats a
    later one. *)
From Stdlib Require Import String Ascii List Bool.
Import ListNotations.
From ONNXFormalization.VNNLIB.Parser Require Import Regex Parser LexSpec.

Inductive lex_error := LexError (pos : nat) (msg : string).

Fixpoint is_prefix (p : list ascii) (l : list ascii) : bool :=
  match p, l with
  | [], _ => true
  | a :: p', b :: l' => Ascii.eqb a b && is_prefix p' l'
  | _, _ => false
  end.

Fixpoint len_acc {A} (l : list A) (n : nat) : nat :=
  match l with [] => n | _ :: r => len_acc r (S n) end.
Definition len {A} (l : list A) : nat := len_acc l 0.

Fixpoint firstn_rev {A} (n : nat) (l : list A) (acc : list A) : list A :=
  match n, l with S n', x :: l' => firstn_rev n' l' (x :: acc) | _, _ => acc end.
Definition take {A} (n : nat) (l : list A) : list A := rev_append (firstn_rev n l []) [].

(** Best candidate so far: (length, token), first one kept on ties. *)
Definition better (cand : option (nat * token)) (k : nat) (t : token) : option (nat * token) :=
  match cand with
  | Some (k', _) => if Nat.ltb k' k then Some (k, t) else cand
  | None => Some (k, t)
  end.

Definition best_literal (l : list ascii) (cand : option (nat * token)) : option (nat * token) :=
  fold_left (fun c '(s, t) => let p := list_ascii_of_string s in
                              if is_prefix p l then better c (len p) t else c)
            literals cand.

Definition best_class (l : list ascii) (cand : option (nat * token)) : option (nat * token) :=
  fold_left (fun c '(r, mk) =>
               match longest r l with
               | Some (S _ as k) => better c k (mk (string_of_list_ascii (take k l)))
               | _ => c
               end) token_classes cand.

Fixpoint skip_line (l : list ascii) (k : nat) : list ascii * nat :=
  match l with
  | "010"%char :: r => (r, S k)
  | _ :: r => skip_line r (S k)
  | [] => ([], k)
  end.

Definition is_space (c : ascii) : bool :=
  match c with " "%char | "009"%char | "010"%char | "013"%char => true | _ => false end.

Fixpoint drop {A} (n : nat) (l : list A) : list A :=
  match n, l with S n', _ :: l' => drop n' l' | _, _ => l end.

Fixpoint lex_aux (fuel pos : nat) (l : list ascii) (acc : list token) : list token + lex_error :=
  match fuel with
  | O => inr (LexError pos "out of fuel")
  | S fuel =>
    match l with
    | [] => inl (rev_append acc [])
    | c :: r =>
      if is_space c then lex_aux fuel (S pos) r acc
      else if existsb (fun s => is_prefix (list_ascii_of_string s) l) line_comments then
        let '(r', k) := skip_line l 0 in lex_aux fuel (pos + k) r' acc
      else match best_class l (best_literal l None) with
           | Some (k, t) => lex_aux fuel (pos + k) (drop k l) (t :: acc)
           | None => inr (LexError pos "no token matches")
           end
    end
  end.

(** Tail-recursive replacement for Stdlib's [list_ascii_of_string], whose
    extracted code recurses once per character and overflows the stack on
    multi-megabyte inputs. *)
Fixpoint chars_rev (s : string) (acc : list ascii) : list ascii :=
  match s with EmptyString => acc | String c s' => chars_rev s' (c :: acc) end.
Definition chars (s : string) : list ascii := rev_append (chars_rev s []) [].

Definition lex (s : string) : list token + lex_error :=
  let l := chars s in lex_aux (S (len l)) 0 l [].
