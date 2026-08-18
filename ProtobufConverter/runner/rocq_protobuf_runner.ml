(* Protobuf to Rocq converter *)
(* Reads a .proto file and generates Rocq model and conversion functions *)

(* Helper function to convert OCaml int to Rocq_protobuf.nat *)
let rec int_to_nat = function
  | 0 -> Rocq_protobuf.O
  | n -> Rocq_protobuf.S (int_to_nat (n - 1))

let () =
  let input_filename = Sys.argv.(1) in
  let output_model = "model.v" in
  let output_functions = "conversion_functions.v" in
  
  (* Read the input .proto file *)
  let ic = open_in input_filename in
  let proto_content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  
  (* Convert using the extracted functions with nat depth *)
  let depth = int_to_nat 2000 in
  let model_code = Rocq_protobuf.protobuf_model_converter depth proto_content in
  let function_code = Rocq_protobuf.protobuf_function_converter depth proto_content in
  
  (* Write model.v *)
  let oc = open_out output_model in
  output_string oc model_code;
  close_out oc;
  
  (* Write conversion_functions.v *)
  let oc = open_out output_functions in
  output_string oc function_code;
  close_out oc;
  
  Printf.printf "Successfully converted %s to Rocq files:\n" input_filename;
  Printf.printf "  - %s\n" output_model;
  Printf.printf "  - %s\n" output_functions
