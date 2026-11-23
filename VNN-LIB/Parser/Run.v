(** * Lexer and parser together: from a string to an Ast.Query *)
From Stdlib Require Import String List.
From ONNXFormalization.VNNLIB.Parser Require Import Ast Parser Lexer.
Import MenhirLibParser.Inter.

(** The four possible outcomes of parsing a file. *)
Inductive outcome :=
| Ok (q : Ast.Query)        (* lexed and parsed *)
| LexFail (e : lex_error)   (* no token matches at some position *)
| ParseFail                 (* tokens do not form a Query *)
| Timeout.                  (* parser ran out of fuel (2^log_fuel steps) *)

(** MenhirLib reads an infinite token stream ("buffer"): our tokens, then EOF forever. *)
CoFixpoint eofs : buffer := Buf_cons (EOF tt) eofs.

(** With [log_fuel = 40] the parser may take 2^40 steps; real files need far fewer. *)
Definition log_fuel : nat := 40.

Definition parse_query (s : string) : outcome :=
  match lex s with
  | inr e => LexFail e
  | inl ts =>
      match Parser.pQuery log_fuel (app_buf ts eofs) with
      | Parsed_pr q _ => Ok q
      | Fail_pr_full _ _ => ParseFail
      | Timeout_pr => Timeout
      end
  end.
