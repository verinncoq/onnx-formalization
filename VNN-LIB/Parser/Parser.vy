/* Menhir grammar for VNN-LIB 2.0 queries (input to `menhir --coq`).

   Transcribed by hand from grammar/grammar.cf (VNNLIB-Standard, tag v2.0.0).
   Each production is preceded by its LBNF rule, verbatim, as a comment.
   Semantic actions in { } are Gallina terms that build values of Ast.v.
   Menhir proves pQuery_correct / pQuery_complete with respect to THIS file. */

%{
From Stdlib Require Import List.
Import ListNotations.
From ONNXFormalization.VNNLIB.Parser Require Ast.
%}

/* ---- Terminals ----
   Keywords and symbols: the quoted strings of grammar.cf. They carry no value.
   Note: grammar.cf makes "(assert", "(declare-network", ... single tokens,
   with the opening parenthesis included. */
%token VNNLIB_VERSION    /* "(vnnlib-version" */
%token DECLARE_NETWORK   /* "(declare-network" */
%token DECLARE_INPUT     /* "(declare-input" */
%token DECLARE_HIDDEN    /* "(declare-hidden" */
%token DECLARE_OUTPUT    /* "(declare-output" */
%token EQUAL_TO          /* "(equal-to" */
%token ISOMORPHIC_TO     /* "(isomorphic-to" */
%token ASSERT            /* "(assert" */
%token AND OR            /* "and" "or" */
%token LPAREN RPAREN LBRACK RBRACK COMMA   /* ( ) [ ] , */
%token PLUS MINUS STAR   /* + - * */
%token GT LT GE LE EQ NE /* > < >= <= == != */

/* Token categories (the `token` lines of grammar.cf): they carry their lexeme. */
%token<Ast.VersionToken> VERSION
%token<Ast.Number>       NUMBER
%token<Ast.VariableName> NAME
%token<Ast.OnnxString>   ONNXSTRING

/* End of input; not in grammar.cf, added by us. */
%token EOF

/* ---- Entry point ----
   LBNF: entrypoints Query ;
   pQuery requires the whole input to be one Query (followed by EOF). */
%start<Ast.Query> pQuery

/* The Rocq back end needs the type of every nonterminal. */
%type<Ast.TensorShape>        tensorShape
%type<Ast.ArithExpr>          arithExpr
%type<Ast.BoolExpr>           boolExpr
%type<Ast.Assertion>          assertion
%type<Ast.ElementType>        elementType
%type<Ast.OnnxName>           onnxName
%type<Ast.InputDefinition>    inputDefinition
%type<Ast.OutputDefinition>   outputDefinition
%type<Ast.HiddenDefinition>   hiddenDefinition
%type<Ast.NetworkEquivalence> networkEquivalence
%type<Ast.NetworkDefinition>  networkDefinition
%type<Ast.Version>            version
%type<Ast.Query>              query
%type<list Ast.Number>             list_Number
%type<list Ast.ArithExpr>          list_ArithExpr
%type<list Ast.BoolExpr>           list_BoolExpr
%type<list Ast.Assertion>          list_Assertion
%type<list Ast.InputDefinition>    list_InputDefinition
%type<list Ast.HiddenDefinition>   list_HiddenDefinition
%type<list Ast.OutputDefinition>   list_OutputDefinition
%type<list Ast.NetworkEquivalence> list_NetworkEquivalence
%type<list Ast.NetworkDefinition>  list_NetworkDefinition

%%

pQuery:
| q = query EOF { q }

/* ---- Lists ----
   `separator nonempty C ","` : one or more C, separated by ",".
   `separator nonempty C ""`  : one or more C, nothing in between.
   `separator C ""`           : zero or more C. */

/* LBNF: separator nonempty Number "," ; */
list_Number:
| n = NUMBER                       { [n] }
| n = NUMBER COMMA ns = list_Number { n :: ns }

/* ---- Rules, in the order of grammar.cf ---- */

tensorShape:
/* LBNF: ScalarDims.     TensorShape ::= "[" "]" ; */
| LBRACK RBRACK                    { Ast.ScalarDims }
/* LBNF: TensorDims.     TensorShape ::= "[" [Number] "]" ; */
| LBRACK ns = list_Number RBRACK   { Ast.TensorDims ns }

arithExpr:
/* LBNF: ScalarVarExpr.  ArithExpr   ::= VariableName ; */
| x = NAME                                 { Ast.ScalarVarExpr x }
/* LBNF: TensorVarExpr.  ArithExpr   ::= VariableName "[" [Number] "]" ; */
| x = NAME LBRACK ns = list_Number RBRACK  { Ast.TensorVarExpr x ns }
/* LBNF: ValExpr.        ArithExpr   ::= Number ; */
| n = NUMBER                               { Ast.ValExpr n }
/* LBNF: Negate.         ArithExpr   ::= "(" "-" ArithExpr  ")" ; */
| LPAREN MINUS e = arithExpr RPAREN        { Ast.Negate e }
/* LBNF: Plus.           ArithExpr   ::= "(" "+" [ArithExpr] ")"; */
| LPAREN PLUS es = list_ArithExpr RPAREN   { Ast.Plus es }
/* LBNF: Minus.          ArithExpr   ::= "(" "-" ArithExpr [ArithExpr] ")" ; */
| LPAREN MINUS e = arithExpr es = list_ArithExpr RPAREN { Ast.Minus e es }
/* LBNF: Multiply.       ArithExpr   ::= "(" "*" [ArithExpr] ")" ; */
| LPAREN STAR es = list_ArithExpr RPAREN   { Ast.Multiply es }

/* LBNF: separator nonempty ArithExpr "" ; */
list_ArithExpr:
| e = arithExpr                     { [e] }
| e = arithExpr es = list_ArithExpr { e :: es }

boolExpr:
/* LBNF: GreaterThan.    BoolExpr   ::= "(" ">" ArithExpr ArithExpr ")" ; */
| LPAREN GT e1 = arithExpr e2 = arithExpr RPAREN { Ast.GreaterThan e1 e2 }
/* LBNF: LessThan.       BoolExpr   ::= "(" "<" ArithExpr ArithExpr ")" ; */
| LPAREN LT e1 = arithExpr e2 = arithExpr RPAREN { Ast.LessThan e1 e2 }
/* LBNF: GreaterEqual.   BoolExpr   ::= "(" ">=" ArithExpr ArithExpr ")" ; */
| LPAREN GE e1 = arithExpr e2 = arithExpr RPAREN { Ast.GreaterEqual e1 e2 }
/* LBNF: LessEqual.      BoolExpr   ::= "(" "<=" ArithExpr ArithExpr ")" ; */
| LPAREN LE e1 = arithExpr e2 = arithExpr RPAREN { Ast.LessEqual e1 e2 }
/* LBNF: NotEqual.       BoolExpr   ::= "(" "!=" ArithExpr ArithExpr ")" ; */
| LPAREN NE e1 = arithExpr e2 = arithExpr RPAREN { Ast.NotEqual e1 e2 }
/* LBNF: Equal.          BoolExpr   ::= "(" "==" ArithExpr ArithExpr ")"; */
| LPAREN EQ e1 = arithExpr e2 = arithExpr RPAREN { Ast.Equal e1 e2 }
/* LBNF: And.            BoolExpr   ::= "(" "and" [BoolExpr] ")" ; */
| LPAREN AND bs = list_BoolExpr RPAREN           { Ast.And bs }
/* LBNF: Or.             BoolExpr   ::= "(" "or" [BoolExpr] ")" ; */
| LPAREN OR bs = list_BoolExpr RPAREN            { Ast.Or bs }

/* LBNF: separator nonempty BoolExpr "" ; */
list_BoolExpr:
| b = boolExpr                    { [b] }
| b = boolExpr bs = list_BoolExpr { b :: bs }

assertion:
/* LBNF: Assert.         Assertion   ::= "(assert" BoolExpr ")" ; */
| ASSERT b = boolExpr RPAREN { Ast.Assert b }

/* LBNF: separator nonempty Assertion "" ; */
list_Assertion:
| a = assertion                     { [a] }
| a = assertion as_ = list_Assertion { a :: as_ }

elementType:
/* LBNF: DType.          ElementType ::= VariableName ; */
| t = NAME { Ast.DType t }

onnxName:
/* LBNF: NodeName.       OnnxName    ::= OnnxString ; */
| s = ONNXSTRING { Ast.NodeName s }

inputDefinition:
/* LBNF: InputDef.       InputDefinition  ::= "(declare-input" VariableName ElementType TensorShape ")" ; */
| DECLARE_INPUT x = NAME t = elementType s = tensorShape RPAREN { Ast.InputDef x t s }

outputDefinition:
/* LBNF: OutputDef.      OutputDefinition ::= "(declare-output" VariableName ElementType TensorShape ")" ; */
| DECLARE_OUTPUT x = NAME t = elementType s = tensorShape RPAREN { Ast.OutputDef x t s }

hiddenDefinition:
/* LBNF: HiddenDef.      HiddenDefinition ::= "(declare-hidden" VariableName ElementType TensorShape OnnxName ")" ; */
| DECLARE_HIDDEN x = NAME t = elementType s = tensorShape o = onnxName RPAREN { Ast.HiddenDef x t s o }

/* LBNF: separator nonempty InputDefinition "" ; */
list_InputDefinition:
| d = inputDefinition                           { [d] }
| d = inputDefinition ds = list_InputDefinition { d :: ds }

/* LBNF: separator HiddenDefinition "" ; */
list_HiddenDefinition:
| /* empty */                                     { [] }
| d = hiddenDefinition ds = list_HiddenDefinition { d :: ds }

/* LBNF: separator nonempty OutputDefinition "" ; */
list_OutputDefinition:
| d = outputDefinition                            { [d] }
| d = outputDefinition ds = list_OutputDefinition { d :: ds }

networkEquivalence:
/* LBNF: IsomorphicTo.   NetworkEquivalence ::= "(isomorphic-to" VariableName ")" ; */
| ISOMORPHIC_TO n = NAME RPAREN { Ast.IsomorphicTo n }
/* LBNF: EqualTo.        NetworkEquivalence ::= "(equal-to" VariableName ")" ; */
| EQUAL_TO n = NAME RPAREN      { Ast.EqualTo n }

/* LBNF: separator NetworkEquivalence "" ; */
list_NetworkEquivalence:
| /* empty */                                         { [] }
| e = networkEquivalence es = list_NetworkEquivalence { e :: es }

networkDefinition:
/* LBNF: NetworkDef.     NetworkDefinition ::= "(declare-network" VariableName [NetworkEquivalence] [InputDefinition] [HiddenDefinition] [OutputDefinition] ")" ; */
| DECLARE_NETWORK n = NAME es = list_NetworkEquivalence is = list_InputDefinition
                  hs = list_HiddenDefinition os = list_OutputDefinition RPAREN
  { Ast.NetworkDef n es is hs os }

/* LBNF: separator nonempty NetworkDefinition "" ; */
list_NetworkDefinition:
| d = networkDefinition                             { [d] }
| d = networkDefinition ds = list_NetworkDefinition { d :: ds }

version:
/* LBNF: VNNLibVersion.  Version         ::= "(vnnlib-version" VersionToken ")" ; */
| VNNLIB_VERSION v = VERSION RPAREN { Ast.VNNLibVersion v }

query:
/* LBNF: VNNLibQuery.    Query           ::= Version [NetworkDefinition] [Assertion] ; */
| v = version ns = list_NetworkDefinition as_ = list_Assertion { Ast.VNNLibQuery v ns as_ }

/* LBNF: comment ";" ;          -> LexSpec.v (line comments) */
