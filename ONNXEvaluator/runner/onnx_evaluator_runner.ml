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

(* OCaml implementations to avoid Rocq string handling stack overflows *)

(* Convert int32 to Rocq positive *)
let int32_to_positive (bits: int32) : Rocq_onnx_evaluator.positive =
  let open Rocq_onnx_evaluator in
  let rec loop bits =
    if bits = 0l then XH
    else if bits = 1l then XH
    else if Int32.logand bits 1l = 0l then 
      XO (loop (Int32.shift_right_logical bits 1))
    else 
      XI (loop (Int32.shift_right_logical bits 1))
  in
  if bits = 0l then XH
  else loop bits

(* OCaml implementation of float32_of_string *)
let ocaml_float32_of_string (s: string) : Rocq_onnx_evaluator.float32 option = 
  try
    let f = float_of_string s in
    (* Raw single-precision bit pattern, used as-is: int32_to_positive reads
       all 32 bits via logical shifts. The previous "unsigned" adjustment
       cleared bit 31 and dropped the sign of every negative float. The
       all-zero pattern (+0.0) maps to Z0, since positive cannot represent 0. *)
    let bits = Int32.bits_of_float f in
    let z =
      if bits = 0l then Rocq_onnx_evaluator.Z0
      else Rocq_onnx_evaluator.Zpos (int32_to_positive bits)
    in
    Some (Rocq_onnx_evaluator.b32_of_bits z)
  with _ -> None

(* OCaml implementation of int64_of_string *)
let ocaml_int64_of_string (s: string) : Rocq_onnx_evaluator.int64 option = 
  try
    let i = Int64.of_string s in
    (* Convert to Rocq int64 (nested tuple of 8 bytes, big-endian) *)
    let get_byte shift = 
      let shifted = Int64.shift_right_logical i shift in
      let masked = Int64.logand shifted 0xFFL in
      Char.chr (Int64.to_int masked)
    in
    let b0 = get_byte 56 in  (* MSB *)
    let b1 = get_byte 48 in
    let b2 = get_byte 40 in
    let b3 = get_byte 32 in
    let b4 = get_byte 24 in
    let b5 = get_byte 16 in
    let b6 = get_byte 8 in
    let b7 = get_byte 0 in   (* LSB *)
    Some (((((((b0, b1), b2), b3), b4), b5), b6), b7)
  with _ -> None

(* Convert string inputs to TensorProto using OCaml implementations *)
let convert_string_inputs_to_tensors (inputs: ((string * string list) * string list) list) : 
    Rocq_onnx_evaluator.tensorProto list =
  List.map (fun ((name, value_strs), dim_strs) ->
    (* Convert string values to float32 using OCaml implementation *)
    let floats = 
      List.map (fun s -> 
        match ocaml_float32_of_string s with
        | Some f -> f
        | None -> failwith (Printf.sprintf "Cannot convert '%s' to float32" s)
      ) value_strs
    in
    (* Convert string dims to int64 using OCaml implementation *)
    let dims = 
      List.map (fun s -> 
        match ocaml_int64_of_string s with
        | Some i -> i
        | None -> failwith (Printf.sprintf "Cannot convert '%s' to int64" s)
      ) dim_strs
    in
    (* Create tensor using Rocq's float_tensor *)
    Rocq_onnx_evaluator.float_tensor ("\"" ^ name ^ "\"") floats dims
  ) inputs

(* Convert nat to string *)
let nat_to_string (n: Rocq_onnx_evaluator.nat) : string =
  let rec nat_to_int = function
    | Rocq_onnx_evaluator.O -> 0
    | Rocq_onnx_evaluator.S n' -> 1 + nat_to_int n'
  in
  string_of_int (nat_to_int n)

(* Convert output tensors to string format *)
let convert_output_tensors (tensors: Rocq_onnx_evaluator.tensorProto list) : 
    ((string list * string list) list) Rocq_onnx_evaluator.error_option =
  let rec list_error_option_to_error_option_list = function
    | [] -> Rocq_onnx_evaluator.Success []
    | h :: t ->
        match h, list_error_option_to_error_option_list t with
        | Rocq_onnx_evaluator.Success h', Rocq_onnx_evaluator.Success t' ->
            Rocq_onnx_evaluator.Success (h' :: t')
        | Rocq_onnx_evaluator.Error e, _ -> Rocq_onnx_evaluator.Error e
        | _, Rocq_onnx_evaluator.Error e -> Rocq_onnx_evaluator.Error e
  in
  
  let convert_tensor tensor : (string list * string list) Rocq_onnx_evaluator.error_option =
    match Rocq_onnx_evaluator.matrix_float32_of_tensor tensor with
    | Rocq_onnx_evaluator.Success matrix ->
        let string_matrix = Rocq_onnx_evaluator.string_matrix_of_matrix_float32 matrix in
        let values = Rocq_onnx_evaluator.convert_to_row_major string_matrix in
        let (height, width) = Rocq_onnx_evaluator.shape matrix in
        let dims = [nat_to_string height; nat_to_string width] in
        Rocq_onnx_evaluator.Success (values, dims)
    | Rocq_onnx_evaluator.Error e -> Rocq_onnx_evaluator.Error e
  in
  list_error_option_to_error_option_list (List.map convert_tensor tensors)

(* Direct evaluation using onnx_evaluator *)
let evaluate_direct (text_proto: string) (inputs: ((string * string list) * string list) list) : 
    ((string list * string list) list) Rocq_onnx_evaluator.error_option =
  match Rocq_onnx_evaluator.onnx_converter_to_onnx_model text_proto with
  | Rocq_onnx_evaluator.Success model ->
      let input_tensors = convert_string_inputs_to_tensors inputs in
      begin
        match Rocq_onnx_evaluator.onnx_evaluator model input_tensors with
        | Rocq_onnx_evaluator.Success output_tensors -> convert_output_tensors output_tensors
        | Rocq_onnx_evaluator.Error e -> Rocq_onnx_evaluator.Error e
      end
  | Rocq_onnx_evaluator.Error e -> Rocq_onnx_evaluator.Error e

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
  
  (* Call evaluate_direct for each input set *)
  let results =
    List.map (fun inputs ->
      evaluate_direct text_proto inputs
    ) all_inputs
  in

  (* Output results to stdout in Python-evaluable format *)
  let all_results_str = String.concat ", " (List.map format_error_option results) in
  Printf.printf "[%s]\n%!" all_results_str
