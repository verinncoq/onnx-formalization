From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
Open Scope string_scope.

From ONNXFormalization.ProtobufConverter Require Export preprocessor.
From ONNXFormalization.ProtobufConverter Require Export tokenizer_protobuf.
From ONNXFormalization.ProtobufConverter Require Export parser_protobuf.
From ONNXFormalization.ProtobufConverter Require Export IR_converter_protobuf.
From ONNXFormalization.ProtobufConverter Require Export sorter.
From ONNXFormalization.ProtobufConverter Require Export model_converter.
From ONNXFormalization.ProtobufConverter Require Export function_converter.

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