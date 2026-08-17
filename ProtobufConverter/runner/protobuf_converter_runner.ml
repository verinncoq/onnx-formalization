(** Protobuf converter runner - converts .proto files to Coq .v files *)

(** This module provides direct conversion from protobuf to Rocq/Coq using
    extracted OCaml functions. It produces model.v and conversion_functions.v. *)

(** Convert OCaml int to Datatypes.nat *)
let int_to_nat n =
  let rec loop i acc =
    if i <= 0 then acc
    else loop (i - 1) (Datatypes.S acc)
  in
  loop n Datatypes.O

(** Convert OCaml bool to Datatypes.bool *)
let bool_to_datatypes_bool = function
  | true -> Datatypes.Coq_true
  | false -> Datatypes.Coq_false

(** Convert OCaml char to Ascii.ascii *)
let char_to_ascii c =
  let i = Char.code c in
  Ascii.Ascii (
    bool_to_datatypes_bool ((i land 128) <> 0),
    bool_to_datatypes_bool ((i land 64) <> 0),
    bool_to_datatypes_bool ((i land 32) <> 0),
    bool_to_datatypes_bool ((i land 16) <> 0),
    bool_to_datatypes_bool ((i land 8) <> 0),
    bool_to_datatypes_bool ((i land 4) <> 0),
    bool_to_datatypes_bool ((i land 2) <> 0),
    bool_to_datatypes_bool ((i land 1) <> 0)
  )

(** Convert Datatypes.bool to OCaml bool *)
let datatypes_bool_to_bool = function
  | Datatypes.Coq_true -> true
  | Datatypes.Coq_false -> false

(** Convert Ascii.ascii to OCaml char *)
let ascii_to_char a =
  match a with
  | Ascii.Ascii (b7, b6, b5, b4, b3, b2, b1, b0) ->
      Char.chr (
        (if datatypes_bool_to_bool b7 then 128 else 0) +
        (if datatypes_bool_to_bool b6 then 64 else 0) +
        (if datatypes_bool_to_bool b5 then 32 else 0) +
        (if datatypes_bool_to_bool b4 then 16 else 0) +
        (if datatypes_bool_to_bool b3 then 8 else 0) +
        (if datatypes_bool_to_bool b2 then 4 else 0) +
        (if datatypes_bool_to_bool b1 then 2 else 0) +
        (if datatypes_bool_to_bool b0 then 1 else 0)
      )

(** Convert OCaml string to Rocq String.string by direct iteration *)
let string_to_rocq_string s =
  let len = Stdlib.String.length s in
  let rec loop i =
    if i >= len then String.EmptyString
    else String.String (char_to_ascii (Stdlib.String.get s i), loop (i + 1))
  in
  loop 0

(** Convert Rocq String.string to OCaml string by direct iteration *)
let rocq_string_to_string rs =
  let buffer = Buffer.create 256 in
  let rec loop = function
    | String.EmptyString -> ()
    | String.String (a, rest) -> Buffer.add_char buffer (ascii_to_char a); loop rest
  in
  loop rs;
  Buffer.contents buffer

(** [current_timestamp()] returns current UTC time as formatted string. *) 
let current_timestamp () =
  let now = Unix.gmtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d"
    (now.Unix.tm_year + 1900) (now.Unix.tm_mon + 1) now.Unix.tm_mday
    now.Unix.tm_hour now.Unix.tm_min now.Unix.tm_sec

(** [file_exists path] checks if file exists. *) 
let file_exists path =
  try Sys.file_exists path with Sys_error _ -> false

(** [read_file path] reads entire file content. *) 
let read_file path =
  let ch = open_in path in
  let size = in_channel_length ch in
  let content = Bytes.create size in
  really_input ch content 0 size;
  close_in ch;
  Bytes.to_string content

(** [write_file path content] writes content to file, creating directories if needed  
let write_file path content =
  let dir = Filename.dirname path in
  if dir <> "" && dir <> "." && not (Sys.file_exists dir) then
    Unix.mkdir dir 0o755;
  let ch = open_out path in
  output_string ch content;
  close_out ch

(** Direct conversion: reads .proto, converts using extracted OCaml functions,
    and writes model.v and conversion_functions.v
