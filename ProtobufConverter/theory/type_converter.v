From Stdlib Require Import Strings.String.
Open Scope string_scope.

(*source 1: https://github.com/onnx/onnx/blob/main/docs/IR.md*)
(*source 2 (not covered completely): https://protobuf.dev/programming-guides/proto2/#scalar*)


(*
Assigns types in .proto files with types in roqc models.
Input is the name of the type in the .proto file, output is:
1. a bool if the type is a standard type (if false, the type must be a nested message, enum or one_of)
2. the name of the assigned type T
3. the type converting function. It must have the following signature: list ascii => option T (Inputs are always strings (list ascii) because it's a parsed file)
*)
Definition type_converter (s: string) : bool * string * string :=
  if eqb s "double" then (true, "float64", "float64_of_string")(*implemented*)
  else if eqb s "float" then (true, "float32", "float32_of_string")(*implemented*)
  (*signed int*)
  else if eqb s "int32" then (true, "int32", "int32_of_string")(*implemented*)
  else if eqb s "int64" then (true, "int64", "int64_of_string")(*implemented*)
  else if eqb s "sint32" then (true, "int32", "int32_of_string")(*implemented*)
  else if eqb s "sint64" then (true, "int64", "int64_of_string")(*implemented*)
  else if eqb s "sfixed32" then (true, "int32", "int32_of_string")(*implemented*)
  else if eqb s "sfixed64" then (true, "int64", "int64_of_string")(*implemented*)
  (*unsigned int*)
  else if eqb s "uint32" then (true, "uint32", "uint32_of_string")(*implemented*)
  else if eqb s "uint64" then (true, "uint64", "uint64_of_string")(*implemented*)
  else if eqb s "fixed32" then (true, "uint32", "uint32_of_string")(*implemented*)
  else if eqb s "fixed64" then (true, "uint64", "uint64_of_string")(*implemented*)
  (*string*)
  else if eqb s "string" then (true, "string", "(fun x => Some (string_of_list_ascii x))")(*roqc implementation*)
  (*bool*)
  else if eqb s "bool" then (true, "bool", "(fun x => match (string_of_list_ascii x) with | ""true"" => Some true | ""false"" => Some false | _ => None end)")(*roqc implementation*)
  (*bytes*)
  else if eqb s "bytes" then (true, "bytes", "bytes_of_string")(*implemented*)
  (*other types stay the same, for made-up types like message, enum and one_of*)
  else (false, s, "convert_" ++ s).

(*returns true if the type is a standard (basic) type*)
Definition is_basic_type (s: string) : bool := fst (fst (type_converter s)).

(*returns the name of the assigned type*)
Definition convert_type (s: string) : string := snd (fst (type_converter s)).

(*returns the type converting function (see above for explanation)*)
Definition get_string_converter (s: string) : string := snd (type_converter s).