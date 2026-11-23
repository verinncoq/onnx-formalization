(** * Abstract syntax of VNN-LIB 2.0 queries

    Transcribed from grammar/grammar.cf.
    Each [(* LBNF: ... *)] comment is the grammar line, verbatim; the Rocq
    definition directly below it is its translation. Constructor names are the
    LBNF labels, so values coincide with BNFC's AbsGrammar.

    Only the shape of a parse result lives here. Which token sequences are
    valid is defined in Parser.vy; which characters form a token in LexSpec.v. *)
From Stdlib Require Import String List.

(** ** Tokens. A token's value is its lexeme (the matched text), as in BNFC.
    LBNF's [position] (record line/column) is not kept. *)

(* LBNF: position token VersionToken '<' digit+ '.' digit+ '>' ; *)
Definition VersionToken : Type := string.

(* LBNF: position token Number '-'? digit+ ('.' digit+)? ; *)
Definition Number : Type := string.

(* LBNF: position token VariableName letter (letter|digit|'_')* ; *)
Definition VariableName : Type := string.

(* LBNF: token OnnxString '"' ((char - ["\"\\"]) | ('\\' ["\"\\nt"]))* '"'; *)
Definition OnnxString : Type := string.

(** ** Categories. One [Inductive] per LBNF category, one constructor per
    labelled rule. Terminals (keywords, brackets) do not appear: they carry no
    information. [[C]] in LBNF becomes [list C]. *)

Inductive TensorShape : Type :=
(* LBNF: ScalarDims.     TensorShape ::= "[" "]" ; *)
| ScalarDims
(* LBNF: TensorDims.     TensorShape ::= "[" [Number] "]" ; *)
| TensorDims (dims : list Number).

Inductive ArithExpr : Type :=
(* LBNF: ScalarVarExpr.  ArithExpr   ::= VariableName ; *)
| ScalarVarExpr (x : VariableName)
(* LBNF: TensorVarExpr.  ArithExpr   ::= VariableName "[" [Number] "]" ; *)
| TensorVarExpr (x : VariableName) (indices : list Number)
(* LBNF: ValExpr.        ArithExpr   ::= Number ; *)
| ValExpr (n : Number)
(* LBNF: Negate.         ArithExpr   ::= "(" "-" ArithExpr  ")" ; *)
| Negate (e : ArithExpr)
(* LBNF: Plus.           ArithExpr   ::= "(" "+" [ArithExpr] ")"; *)
| Plus (es : list ArithExpr)
(* LBNF: Minus.          ArithExpr   ::= "(" "-" ArithExpr [ArithExpr] ")" ; *)
| Minus (e : ArithExpr) (es : list ArithExpr)
(* LBNF: Multiply.       ArithExpr   ::= "(" "*" [ArithExpr] ")" ; *)
| Multiply (es : list ArithExpr).

Inductive BoolExpr : Type :=
(* LBNF: GreaterThan.    BoolExpr   ::= "(" ">" ArithExpr ArithExpr ")" ; *)
| GreaterThan (e1 e2 : ArithExpr)
(* LBNF: LessThan.       BoolExpr   ::= "(" "<" ArithExpr ArithExpr ")" ; *)
| LessThan (e1 e2 : ArithExpr)
(* LBNF: GreaterEqual.   BoolExpr   ::= "(" ">=" ArithExpr ArithExpr ")" ; *)
| GreaterEqual (e1 e2 : ArithExpr)
(* LBNF: LessEqual.      BoolExpr   ::= "(" "<=" ArithExpr ArithExpr ")" ; *)
| LessEqual (e1 e2 : ArithExpr)
(* LBNF: NotEqual.       BoolExpr   ::= "(" "!=" ArithExpr ArithExpr ")" ; *)
| NotEqual (e1 e2 : ArithExpr)
(* LBNF: Equal.          BoolExpr   ::= "(" "==" ArithExpr ArithExpr ")"; *)
| Equal (e1 e2 : ArithExpr)
(* LBNF: And.            BoolExpr   ::= "(" "and" [BoolExpr] ")" ; *)
| And (bs : list BoolExpr)
(* LBNF: Or.             BoolExpr   ::= "(" "or" [BoolExpr] ")" ; *)
| Or (bs : list BoolExpr).

Inductive Assertion : Type :=
(* LBNF: Assert.         Assertion   ::= "(assert" BoolExpr ")" ; *)
| Assert (b : BoolExpr).

Inductive ElementType : Type :=
(* LBNF: DType.          ElementType ::= VariableName ; *)
| DType (t : VariableName).

Inductive OnnxName : Type :=
(* LBNF: NodeName.       OnnxName    ::= OnnxString ; *)
| NodeName (s : OnnxString).

Inductive InputDefinition : Type :=
(* LBNF: InputDef.       InputDefinition  ::= "(declare-input" VariableName ElementType TensorShape ")" ; *)
| InputDef (x : VariableName) (t : ElementType) (shape : TensorShape).

Inductive OutputDefinition : Type :=
(* LBNF: OutputDef.      OutputDefinition ::= "(declare-output" VariableName ElementType TensorShape ")" ; *)
| OutputDef (x : VariableName) (t : ElementType) (shape : TensorShape).

Inductive HiddenDefinition : Type :=
(* LBNF: HiddenDef.      HiddenDefinition ::= "(declare-hidden" VariableName ElementType TensorShape OnnxName ")" ; *)
| HiddenDef (x : VariableName) (t : ElementType) (shape : TensorShape) (node : OnnxName).

Inductive NetworkEquivalence : Type :=
(* LBNF: IsomorphicTo.   NetworkEquivalence ::= "(isomorphic-to" VariableName ")" ; *)
| IsomorphicTo (net : VariableName)
(* LBNF: EqualTo.        NetworkEquivalence ::= "(equal-to" VariableName ")" ; *)
| EqualTo (net : VariableName).

Inductive NetworkDefinition : Type :=
(* LBNF: NetworkDef.     NetworkDefinition ::= "(declare-network" VariableName [NetworkEquivalence] [InputDefinition] [HiddenDefinition] [OutputDefinition] ")" ; *)
| NetworkDef (name : VariableName) (equivs : list NetworkEquivalence)
             (inputs : list InputDefinition) (hidden : list HiddenDefinition)
             (outputs : list OutputDefinition).

Inductive Version : Type :=
(* LBNF: VNNLibVersion.  Version         ::= "(vnnlib-version" VersionToken ")" ; *)
| VNNLibVersion (v : VersionToken).

Inductive Query : Type :=
(* LBNF: VNNLibQuery.    Query           ::= Version [NetworkDefinition] [Assertion] ; *)
| VNNLibQuery (v : Version) (nets : list NetworkDefinition) (asserts : list Assertion).

(* The separator, comment and entrypoints statements have no counterpart here:
   see Parser.vy and LexSpec.v. *)
