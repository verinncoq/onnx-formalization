From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.
Open Scope string_scope.
From Stdlib Require Import Lists.List. Import ListNotations.


From ONNXFormalization.External Require Export string_tree.
From ONNXFormalization.External Require Export inb.
From ONNXFormalization.External Require Export eqb_la.
From ONNXFormalization.External Require Export theorems.

(*
Helper for the parser. Builds the syntax tree, appending to 'built_tree'
should be initialized with depth=0 and after_colon=false
*)
Fixpoint parse_recursive (built_tree: tree) (todo_list: list string) (depth: nat) : tree :=
  match todo_list with
  | [] => built_tree (*nothing more todo, tree will be returned*)
  | active_token::todo_list' =>
    match active_token with

    | "{" => (*append nothing but go one depth down*) 
      parse_recursive built_tree todo_list' (depth+1)

    | "}" => (*append nothing but go two depths up*) 
      parse_recursive built_tree todo_list' (depth-2)

    | "enum" => (*append active_token and go one depth down*)
      parse_recursive (append_at_end built_tree depth (list_ascii_of_string active_token)) todo_list' (depth+1)
    | "message" => (*append active_token and go one depth down*)
      parse_recursive (append_at_end built_tree depth (list_ascii_of_string active_token)) todo_list' (depth+1)
    | "oneof" => (*append active_token and go one depth down*)
      parse_recursive (append_at_end built_tree depth (list_ascii_of_string active_token)) todo_list' (depth+1)

    | _  => (*append active_token and stay in depth*)
      parse_recursive (append_at_end built_tree depth (list_ascii_of_string active_token)) todo_list' depth
    end
  end.

(*Parsing function. Takes a list of tokens and return a syntax tree*)
Definition parse (l: list string) : tree := parse_recursive (subtree (list_ascii_of_string "message") [subtree (list_ascii_of_string "main") []]) l 1.

(*
Definition test := ["message"%string; "TensorShapeProto"%string;
       "{"%string; "message"%string; "Dimension"%string;
       "{"%string; "oneof"%string; "value"%string;
       "{"%string; "int64"%string; "dim_value"%string;
       "="%string; "1"%string; ";"%string;
       "string"%string; "dim_param"%string; "="%string;
       "2"%string; ";"%string; "}"%string; ";"%string;
       "optional"%string; "string"%string;
       "denotation"%string; "="%string; "3"%string;
       ";"%string; "}"%string; ";"%string;
       "repeated"%string; "Dimension"%string;
       "dim"%string; "="%string; "1"%string; ";"%string;
       "}"%string]
     : list string.

Compute toStringtree (parse test).*)