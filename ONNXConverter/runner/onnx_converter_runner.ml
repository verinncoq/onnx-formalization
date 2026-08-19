(* ONNX to Rocq verification model runner
 *
 * Reads ONNX model in text proto or binary format and converts it to Rocq verification model.
 * Binary ONNX files are automatically decoded to text proto format.
 *)

(* Try to decode binary ONNX to text proto using protoc *)
let decode_binary_to_text_proto (protobuf_schema : string) (input_file : string) : string option =
  try
    (* Check if the provided schema file exists *)
    if not (Sys.file_exists protobuf_schema) then begin
      Printf.eprintf "Error: ONNX schema not found at: %s\n" protobuf_schema;
      None
    end else
    (* Run: protoc --decode=onnx.ModelProto <schema> < input_file *)
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

let () =
  if Array.length Sys.argv < 4 then begin
    Printf.printf "Usage: %s <input.onnx> <output.v> <onnx.proto>\n%!" Sys.argv.(0);
    exit 1
  end;

  let input_file = Sys.argv.(1) in
  let output_file = Sys.argv.(2) in
  let protobuf_schema = Sys.argv.(3) in

  (* Decode binary ONNX to text proto *)
  let text_proto =
    match decode_binary_to_text_proto protobuf_schema input_file with
    | Some decoded -> decoded
    | None -> exit 1
  in

  (* Call the existing onnx_converter function *)
  let result = Rocq_onnx_converter.onnx_converter text_proto in

  (* Write the result to the output file *)
  let oc = open_out output_file in
  Printf.fprintf oc "%s" result;
  close_out oc