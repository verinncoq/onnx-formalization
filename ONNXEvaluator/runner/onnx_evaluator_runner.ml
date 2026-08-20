(* ONNX Evaluator Runner
 *
 * Decodes binary ONNX to text proto and evaluates it using extracted Rocq functions.
 * Inputs are provided via stdin in a simple text format.
 * Output is in Python-evaluable list format.
 *) 

(* Decode binary ONNX to text proto using protoc *)
let decode_binary_to_text_proto (protobuf_schema : string) (input_file : string) : string option =
  try
    if not (Sys.file_exists protobuf_schema) then begin
      Printf.eprintf "Error: ONNX schema not found at: %s\n" protobuf_schema;
      None
    end else
    let cmd = Printf.sprintf "protoc --decode=onnx.ModelProto %s < %s" protobuf_schema input_file in
    let ic = Unix.open_process_in cmd in
    let text_proto = In_channel.input_all ic in
    close_in ic;
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> Some text_proto
    | _ ->
      Printf.eprintf "Warning: protoc failed to decode %s. Is protoc installed?\n" input_file;
      Printf.eprintf "Install it with: opam install conf-protoc\n";
      Printf.eprintf "Or manually: sudo apt-get install protobuf-compiler\n";
      None
  with e ->
    Printf.eprintf "Warning: Failed to decode binary ONNX file: %s\n" (Printexc.to_string e);
    None

(* Parse inputs from stdin.
   Format: One line per evaluation, each evaluation is a list of inputs.
   Each input: name|value1,value2,...|dim1,dim2,...
   Inputs in one evaluation are separated by ';;'
   Example: input1|0.1,0.2,0.3|1,28,28;;input2|0.4,0.5|1,10
   
   Note: The extracted evaluate function expects ((string * string list) * string list) list
   which is ((name, values), dims). Coq's right-associative A*B*C becomes OCaml's left-associative (A*B)*C.
 *)
let parse_inputs_from_stdin () : ((string * string list) * string list) list list =
  let lines = ref [] in
  (try
    while true do
      let line = input_line stdin in
      lines := line :: !lines
    done
  with End_of_file -> ());
  
  List.rev !lines |> List.map (fun line ->
    if line = "" then [] else
    let input_strs = String.split_on_char ';' line in
    input_strs |> List.map (fun input_str ->
      let parts = String.split_on_char '|' input_str in
      match parts with
      | [name; values_str; dims_str] ->
        let values = String.split_on_char ',' values_str |> List.filter (fun s -> s <> "") in
        let dims = String.split_on_char ',' dims_str |> List.filter (fun s -> s <> "") in
        ((name, values), dims)
      | _ -> failwith (Printf.sprintf "Invalid input format: %s" input_str)
    )
  )

let format_string_list str_list =
  "[" ^ String.concat ", " (List.map (fun s -> Printf.sprintf "\"%s\"" s) str_list) ^ "]"

let format_output_list output_list =
  "[" ^ String.concat ", " (List.map (fun (vals, dims) ->
    Printf.sprintf "(%s, %s)" (format_string_list vals) (format_string_list dims)
  ) output_list) ^ "]"

let format_error_option = function
  | Rocq_onnx_evaluator.Success result -> format_output_list result
  | Rocq_onnx_evaluator.Error msg -> Printf.sprintf "\"Error: %s\"" msg

let () =

  if Array.length Sys.argv < 3 then begin
    Printf.printf "Usage: %s <input.onnx> <onnx.proto>\n%!" Sys.argv.(0);
    exit 1
  end;

  let input_file = Sys.argv.(1) in
  let protobuf_schema = Sys.argv.(2) in

  (* Decode binary ONNX to text proto *)
  let text_proto =
    match decode_binary_to_text_proto protobuf_schema input_file with
    | Some decoded -> decoded
    | None -> exit 1
  in

  (* Read and parse inputs from stdin *)
  let all_inputs = parse_inputs_from_stdin () in
  
  (* Call evaluate for each input set *)
  let results =
    List.map (fun inputs ->
      Rocq_onnx_evaluator.evaluate text_proto inputs
    ) all_inputs
  in

  (* Output results to stdout in Python-evaluable format *)
  let all_results_str = String.concat ", " (List.map format_error_option results) in
  Printf.printf "[%s]\n%!" all_results_str
