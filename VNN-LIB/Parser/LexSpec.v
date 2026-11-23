(** * Lexer specification for VNN-LIB 2.0 queries

    Transcribed by hand from grammar/grammar.cf.
    This is data only; the generic lexer in Lexer.v interprets it:
    longest match wins; on equal length a literal beats a token category,
    and an earlier token category beats a later one (as in BNFC/ocamllex).
    Whitespace separates tokens and is skipped. *)
From Stdlib Require Import String Ascii List.
Import ListNotations.
From ONNXFormalization.VNNLIB.Parser Require Import Regex Parser.
Local Open Scope string_scope.

(** ** Literals: every quoted terminal that occurs in a rule of grammar.cf,
    with the Parser.vy token it produces. *)
Definition literals : list (string * token) := [
  (* keywords; the opening parenthesis is part of the token in grammar.cf *)
  ("(vnnlib-version",  VNNLIB_VERSION tt);
  ("(declare-network", DECLARE_NETWORK tt);
  ("(declare-input",   DECLARE_INPUT tt);
  ("(declare-hidden",  DECLARE_HIDDEN tt);
  ("(declare-output",  DECLARE_OUTPUT tt);
  ("(equal-to",        EQUAL_TO tt);
  ("(isomorphic-to",   ISOMORPHIC_TO tt);
  ("(assert",          ASSERT tt);
  ("and", AND tt);  ("or", OR tt);
  (* symbols *)
  ("(", LPAREN tt);  (")", RPAREN tt);  ("[", LBRACK tt);  ("]", RBRACK tt);
  (",", COMMA tt);   ("+", PLUS tt);    ("-", MINUS tt);   ("*", STAR tt);
  (">", GT tt);  ("<", LT tt);  (">=", GE tt);  ("<=", LE tt);
  ("==", EQ tt); ("!=", NE tt)
].

(** ** Token categories, in the order of grammar.cf (order matters on ties). *)
Definition token_classes : list (regex * (string -> token)) := [
  (* LBNF: position token VersionToken '<' digit+ '.' digit+ '>' ; *)
  (RSeq (RChr "<"%char) (RSeq (rplus RDigit) (RSeq (RChr "."%char) (RSeq (rplus RDigit) (RChr ">"%char)))),
   fun s => VERSION s);
  (* LBNF: position token Number '-'? digit+ ('.' digit+)? ; *)
  (RSeq (ropt (RChr "-"%char)) (RSeq (rplus RDigit) (ropt (RSeq (RChr "."%char) (rplus RDigit)))),
   fun s => NUMBER s);
  (* LBNF: position token VariableName letter (letter|digit|'_')* ; *)
  (RSeq RLetter (RStar (RAlt RLetter (RAlt RDigit (RChr "_"%char)))),
   fun s => NAME s);
  (* LBNF: token OnnxString '"' ((char - ["\"\\"]) | ('\\' ["\"\\nt"]))* '"'; *)
  (* In Rocq string and char literals only "" is special: """"%char is the
     double quote character, and "\"%char is a backslash. *)
  (RSeq (RChr """"%char) (RSeq (RStar (RAlt (RDiff RAny (RSet """\"))
                                       (RSeq (RChr "\"%char) (RSet """\nt"))))
                          (RChr """"%char)),
   fun s => ONNXSTRING s)
].

(* LBNF: comment ";" ; *)
Definition line_comments : list string := [";"].
