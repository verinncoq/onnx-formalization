From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.

From ONNXFormalization.External Require Import add_linefeed.
From CoqE2EAI Require Export onnx_converter.
From CoqE2EAI Require Export onnx_evaluator.

(*Wrappers and helpers*)

(*
This is a helper function.
If all elements of the input list are Some, the result is Some, with all the values of the elements.
If not, the result is None.
*)
Fixpoint list_option_to_option_list {T: Type} (l: list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | h::t => match h, list_option_to_option_list t with
    | Some h', Some t' => Some (h'::t')
    | _, _ => None
    end
  end.

(*
This is a helper function.
If all elements of the input list are Success, the result is Success, with all the values of the elements.
If not, the result is Error, with the first Error found.
*)
Fixpoint list_error_option_to_error_option_list {T: Type} (l: list (error_option T)) : error_option (list T) :=
  match l with
  | [] => Success []
  | h::t => match h, list_error_option_to_error_option_list t with
    | Success h', Success t' => Success (h'::t')
    | Error e, _ => Error e
    | _, Error e => Error e
    end
  end.

(*Constructs a tensor with a name and values, given a dimensionality. The type is float32.*)
Definition float_tensor (name: string) (floats: list float32) (dims: list int64) : TensorProto :=
  TensorProto_constructor dims (int32_of_Z 1%Z) None floats [] [] [] (Some name) None None [] None [] [] [].

(*modified signature of float_tensor*)
Definition float_tensor_wrapper (triple: string * (list float32) * (list int64)) : TensorProto :=
  let name := fst (fst triple) in
  let floats := snd (fst triple) in
  let dims := snd triple in
  float_tensor name floats dims.

(*Converts a string tensor to a float tensor by converting values and dims*)
Definition string_tensor_to_float_tensor (triple: string * (list string) * (list string)) : error_option (string * (list float32) * (list int64)) :=
  let name := fst (fst triple) in
  let floats := snd (fst triple) in
  let dims := snd triple in
  match list_option_to_option_list (map float32_of_string (map list_ascii_of_string floats)) with
  | Some f =>
    match list_option_to_option_list (map int64_of_string (map list_ascii_of_string dims)) with
    | Some d => Success (name, f, d)
    | None => Error "Could not convert string to int"
    end
  | None => Error "Could not convert string to float"
  end.

(*converts shape given as (nat * nat) to dims given as list string*)
Definition dims_of_shape (shape: nat * nat) : list string :=
  [writeN 100 (N.of_nat (fst shape)); writeN 100 (N.of_nat (snd shape))].

(*
Wraps the onnx_evaluator to be a function from (model * inputs) -> outputs.
Both values and dims are strings.
*)
Definition onnx_evaluator_wrapper (model: ModelProto) (input: list (string * list string * list string)) : error_option (list (list string * list string)) :=
  let float_tensors_error := map string_tensor_to_float_tensor input in
  match list_error_option_to_error_option_list float_tensors_error with
  | Success float_tensors =>
    let input_tensors := map float_tensor_wrapper float_tensors in
    let evaluate := onnx_evaluator model input_tensors in
    match evaluate with
    | Success o => match list_error_option_to_error_option_list (map matrix_float32_of_tensor o) with
      | Success matrices => 
        let values := map convert_to_row_major (map string_matrix_of_matrix_float32 matrices) in
        let dims := map shape matrices in
        Success (combine values (map dims_of_shape dims))
      | Error e => Error e
      end
    | Error e => Error e
    end
  | Error e => Error e
  end.

(*Converts the model found at model_name to Rocq and Evaluates the model on the input.*)
Definition evaluate (model_name: string) (input: list (string * (list string) * (list string))) : error_option (list (list string * list string)) :=
  match onnx_converter_to_onnx_model model_name with
  | Success model => onnx_evaluator_wrapper model input
  | Error e => Error e
  end.

(*Converts a list of string to a string that represents the list and is readable by python.*)
Fixpoint list_string_to_python_list (l: list string) : string :=
  match l with
  | [] => ""
  | [h] => h
  | h::t => h ++ ", "
    ++ (list_string_to_python_list t)
  end.

(*Converts both lists to a tuple which can be read by python easily*)
Definition onnx_evaluator_wrapper_reformatter_helper (t: (list string * list string)) : string :=
  "(["
  ++ (list_string_to_python_list (fst t)) 
  ++ "], ["
  ++ (list_string_to_python_list (snd t)) 
  ++ "])".

(*formats the output so it can be read by python easily*)
Definition onnx_evaluator_wrapper_reformatter (t: error_option (list (list string * list string))) : error_option string :=
  match t with
  | Success out => 
    let eval := (map onnx_evaluator_wrapper_reformatter_helper out) in
    Success (append "[" (append (list_string_to_python_list eval) (add_linefeed "]")))
  | Error e => Error e
  end.