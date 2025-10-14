From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
Open Scope string_scope.

From CoqE2EAI Require Export preprocessor.
From CoqE2EAI Require Export tokenizer_protobuf.
From CoqE2EAI Require Export parser_protobuf.
From CoqE2EAI Require Export IR_converter_protobuf.
From CoqE2EAI Require Export sorter.
From CoqE2EAI Require Export model_converter.
From CoqE2EAI Require Export function_converter.

(*Convert a string representing a file into the IR*)
Definition protobuf_converter_to_IR (max_depth: nat) (s: string) : error_option (list Structure) :=
  match convert_to_IR max_depth (parse (tokenize (remove_comments s))) with
  | Success main_structure => match main_structure with
    | message "main" before after => sort_structures before
    | _ => Error "Error: main node must be of type message named <main>!"
    end
  | Error e => Error e
  end.

Definition protobuf_model_converter (max_depth: nat) (s: string) : string :=
  match protobuf_converter_to_IR max_depth s with
  | Success IR => model_converter IR
  | Error e => e
  end.

Definition protobuf_function_converter (max_depth: nat) (s: string) : string :=
  match protobuf_converter_to_IR max_depth s with
  | Success IR => function_converter IR
  | Error e => e
  end.

From CoqE2EAI Require Export proto.


Redirect "model" Compute protobuf_model_converter 2000 proto.
Redirect "convertion_functions" Compute protobuf_function_converter 2000 proto.