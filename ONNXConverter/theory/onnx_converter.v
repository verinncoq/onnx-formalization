From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Bool.
Open Scope string_scope.

From ONNXFormalization.External Require Export tokenizer.
From ONNXFormalization.External Require Export parser.
From ONNXFormalization.External Require Export filter.
From ONNXFormalization.External Require Export stringifyNNSequential.

From ONNXFormalization.ONNXConverter Require Export bytes_decoder.
From ONNXFormalization.ONNXConverter Require Export conversion_functions.
From ONNXFormalization.ONNXConverter Require Export onnx_model_to_premodel.


Notation "f |> g" := (error_option_compose f g) (at level 85).

(*define the modelProto_converter*)
Definition modelProto_converter := convert_ModelProto.

(*convert from onnx to verification model*)
Definition onnx_converter (s: string) : string :=
  let conversion := 
    ((fun raw_onnx => bytes_decoder (list_ascii_of_string raw_onnx)) |>
    (fun onnx => filter (parser.parse (tokenizer.tokenize onnx))) |>
    (fun token_tree => modelProto_converter token_tree) |>
    (fun ir => onnx_model_to_premodel_converter ir)) in
  match conversion s with
  | Success premodel => stringifyNNPremodelList premodel
  | Error description => description
  end.

(*convert from onnx to onnx model*)
Definition onnx_converter_to_onnx_model (s: string) : error_option ModelProto :=
  let conversion := 
    ((fun raw_onnx => bytes_decoder (list_ascii_of_string raw_onnx)) |>
    (fun token_tree => modelProto_converter (parser.parse (tokenizer.tokenize token_tree)))) in
  conversion s.

(*for debugging, convert from onnx to syntaxtree*)
Definition onnx_tree_converter (s: string) : error_option tree :=
  let conversion := 
    ((fun raw_onnx => bytes_decoder (list_ascii_of_string raw_onnx)) |>
    (fun onnx => Success (parser.parse (tokenizer.tokenize onnx)))) in
  conversion s.

