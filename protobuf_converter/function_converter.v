From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.


From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export type_converter.
From CoqE2EAI Require Export IR_converter_protobuf.
From CoqE2EAI Require Export model_converter.


(*HANDLERS*)


(*applies a function f to an option type object, if the object is "Some". If the functions fails, error is returned*)
Definition option_option_handler {T output: Type} (f: T -> option output) (input: option T) (error: string) : error_option (option output) :=
  match input with
  | Some t => match f t with
    | Some o => Success (Some o)
    | None => Error error
    end
  | None => Success None
  end.

(*applies a function f to an option type object, if the object is "Some". If the functions fails, it's error is returned*)
Definition error_option_option_handler {T output: Type} (f: T -> error_option output) (input: option T) : error_option (option output) :=
  match input with
  | Some t => match f t with
    | Success o => Success (Some o)
    | Error e => Error e
    end
  | None => Success None
  end.

(*
Converts a list option to option list. If all objects in the input are Some, output is also Some.
If not, output is None.
Needs to be initialized with an empty buffer.
*)
Fixpoint list_option_to_option_list {T: Type} (l: list (option T)) (buffer: list T) : option (list T) :=
  match l with
  | [] => Some (rev buffer)
  | h::t => match h with 
    | Some x => list_option_to_option_list t (x::buffer)
    | None => None
    end
  end. 

(*
Converts a list error_option to error_option list. If all objects in the input are Success, output is also Success.
If not, output is Error, with first Error message found.
Needs to be initialized with an empty buffer.
*)
Fixpoint list_error_option_to_error_option_list {T: Type} (l: list (error_option T)) (buffer: list T) : error_option (list T) :=
  match l with
  | [] => Success (rev buffer) 
  | h::t => match h with 
    | Success x => list_error_option_to_error_option_list t (x::buffer)
    | Error e => Error e
    end
  end.

(*
Converts an option element to an error_option element.
Some -> Success
None -> Error e (with e being the argument <error>)
*)
Definition option_to_error_option {T: Type} (input: option T) (error: string) : error_option T :=
  match input with
  | Some s => Success s
  | None => Error error
  end.


(*applies a function f to all object of a list. If the functions fails, error is returned*)
Definition option_list_handler {T output: Type} (f: T -> option output) (input: list (option T)) (error: string) : error_option (list output) :=
  match list_option_to_option_list input [] with
  | Some l => let option_list := map f l in
      match (list_option_to_option_list option_list []) with
      | Some l => Success l
      | None => Error error
      end
  | None => Error error
  end.

(*applies a function f to all object of a list. If the functions fails, error is returned*)
Definition error_option_list_handler {T output: Type} (f: T -> error_option output) (input: list T) : error_option (list output) :=
  let option_list := map f input in list_error_option_to_error_option_list option_list [].


(*RENAMING*)

(*If s is a reserved keyword of rocq, or a used variable name, it is renamed slightly*)
Definition rename_reserved_keyword (s: string) : string :=
  match s =? "end" with
  | true => "_end"
  | false => match s =? "t" with
    | true => "_t"
    | false => match s =? "la" with
      | true => "_la"
      | false => s
      end
    end
  end.

(*Undo the renaming*)
Definition undo_rename_reserved_keyword (s: string) : string :=
  match s =? "_end" with
  | true => "end"
  | false => match s =? "_t" with
    | true => "t"
    | false => match s =? "_la" with
      | true => "la"
      | false => s
      end
    end
  end.


Definition rename_reserved_keyword_typelabelpair (p: TypeLabelPair) : TypeLabelPair :=
  match p with
  | typelabelpair type label => typelabelpair type (rename_reserved_keyword label)
  end.

Definition rename_reserved_keyword_typelabelpair_list (l: list TypeLabelPair) : list TypeLabelPair :=
  map rename_reserved_keyword_typelabelpair l.

Definition rename_reserved_keyword_field (f: Field) : Field :=
  match f with
  | optional p => optional (rename_reserved_keyword_typelabelpair p)
  | repeated p => repeated (rename_reserved_keyword_typelabelpair p)
  end.

Definition rename_reserved_keyword_field_list (l: list Field) : list Field :=
  map rename_reserved_keyword_field l.

(*CONVERTERS*)

(*return the labels of the fields in a list of fields, concatenated in a string, separated by newlines*)
Fixpoint message_constructor_arguments (l: list Field) : string :=
  match l with
  | [] => ""
  | h::t => let name := match h with
    | optional (typelabelpair type label) => match label with | "" => "e" | l => l end (*in case of an empty label, this must belong to an enum*)
    | repeated (typelabelpair type label) => match label with | "" => "e" | l => l end (*in case of an empty label, this must belong to an enum*)
    end in
    add_linefeed name ++ message_constructor_arguments t
  end.

(*
Converts the field elements of a message into a function (without it's header, which is generated by the message itself).
The function has two parts: 
  let-and-match      all arguments required for the message constructor are gathered, converted from string into type,
                     and error-handled (that they have type error_option)
  pattern-match      all arguments are checked for Success, if so, object gets constructed, if not, first Error message gets returned
l1 and l2 must be the same list
First, l1 is iterated, creating the let-and-match part. Then, l2 is iterated, creating the pattern-match part.
*)
Fixpoint field_to_convertion_function (l1 l2: list Field) (name: string) : string :=
  match l1 with
  | [] => 
    (*pattern-match*)
    "Success (" ++ name ++ add_linefeed "_constructor" ++ 
    message_constructor_arguments l2 ++ add_linefeed ")"
  | f::tail => let let_and_match := match f with
    (*let-and-match*)

    | optional (typelabelpair type label) =>
	  let label_replacement := match label with | "" => "e" | l => l end in (*in case of an empty label, this must belong to an enum*)
	  let label := match label with | "" => "" | l => """" ++ (undo_rename_reserved_keyword label) ++ """" end in (*in case of an empty label, this must belong to an enum*)
      match is_basic_type type with 
      | true =>
        "let " ++ label_replacement ++ "_option := option_option_handler " ++ get_string_converter type ++
        " (grab_value (map list_ascii_of_string [" ++ label ++ "]) t) ""failed to convert " ++ label_replacement ++ " to correct type (" ++ type ++ add_linefeed ")"" in" ++
        "match " ++ label_replacement ++ add_linefeed "_option with" ++ "| Success " ++ label_replacement ++ add_linefeed " =>"
      | false =>
        "let " ++ label_replacement ++ "_option := error_option_option_handler " ++ get_string_converter type ++
        " (grab (map list_ascii_of_string [" ++ label ++ add_linefeed "]) t) in" ++
        "match " ++ label_replacement ++ add_linefeed "_option with" ++ "| Success " ++ label_replacement ++ add_linefeed " =>"
      end

    | repeated (typelabelpair type label) =>
	  let label_replacement := match label with | "" => "e" | l => l end in (*in case of an empty label, this must belong to an enum*)
	  let label := match label with | "" => "" | l => """" ++ (undo_rename_reserved_keyword label) ++ """" end in (*in case of an empty label, this must belong to an enum*)
      match is_basic_type type with 
      | true =>
        "let " ++ label_replacement ++ "_option := option_list_handler " ++ get_string_converter type ++
        " (map getFirstChildValue (grabAll [] " ++ label ++ " t)) ""failed to convert " ++ label_replacement ++ " to correct type (" ++ type ++ add_linefeed ")"" in" ++
        "match " ++ label_replacement ++ add_linefeed "_option with" ++ "| Success " ++ label_replacement ++ add_linefeed " =>"
      | false =>
        "let " ++ label_replacement ++ "_option := error_option_list_handler " ++ get_string_converter type ++
        " (grabAll [] " ++ label ++ add_linefeed " t) in" ++
        "match " ++ label_replacement ++ add_linefeed "_option with" ++ "| Success " ++ label_replacement ++ add_linefeed " =>"
      end

    end in let_and_match ++ field_to_convertion_function tail l2 name ++
    add_linefeed "| Error e => Error e" ++ add_linefeed "end"
  end.

(*
Converts the list elements of a oneof into a function's part (the whole function is generated further down).
The functions tries to grab the oneof elements, one by one.
The first value which can be grabbed successfully is tried to converted into it's type.
*)
Definition one_of_list_element_to_convertion_function (name: string) (pair: TypeLabelPair) : string :=
match pair with
| typelabelpair type label =>
  match is_basic_type type with
  | true =>
    "match (grab_value (map list_ascii_of_string [""" ++ (undo_rename_reserved_keyword label) ++ add_linefeed """]) t) with" ++
    "| Some la => match " ++ get_string_converter type ++ add_linefeed " la with" ++
    "| Some found => Success (" ++ label ++ "_" ++ name ++ add_linefeed " found)" ++
    "| None => Error ""failed to convert " ++ label ++ " to correct type (" ++ type ++ add_linefeed ")""" ++
    add_linefeed "end" ++
    add_linefeed "| None =>"
  | false =>
    "match (grab (map list_ascii_of_string [""" ++ (undo_rename_reserved_keyword label) ++ add_linefeed """]) t) with" ++
    "| Some la => match " ++ get_string_converter type ++ add_linefeed " la with" ++
    "| Success found => Success (" ++ label ++ "_" ++ name ++ add_linefeed " found)" ++
    add_linefeed "| Error e => Error e" ++
    add_linefeed "end" ++
    add_linefeed "| None =>"
  end
end.

(*
Creates a function to convert a oneof element. Wraps the function created in <one_of_list_element_to_convertion_function>.
Adds a functions header as well as an error check, if not a single value can be grabbed.
*)
Definition one_of_to_convertion_function (name: string) (l: list TypeLabelPair) : string :=
  "Definition convert_" ++ name ++ " (t: tree) : error_option " ++ name ++ add_linefeed " :=" ++
  (fold_left append (map (one_of_list_element_to_convertion_function name) l) "") ++
  add_linefeed "Error ""not a single one_of element found""" ++
  (fold_left append (map (fun x => add_linefeed "end") l) "") ++
  add_linefeed ".".

(*
When converting an enum, the grabbed value must be exactly the <label>, and gets written to <type>, without arguments
Here, the cases are created when the exact <label> is found.
*)
Definition enum_list_element_to_convertion_function (t: TypeLabelPair) :=
  match t with
  | typelabelpair type label => "| """ ++ label ++ """ => Success " ++ add_linefeed type
  end.

(*
Creates a function to convert a enum element. Wraps the function created in <enum_list_element_to_convertion_function>.
In this function, the first child of the tree is checked if it has the value from any keyword.
If so, the matching constructor is returned, without arguments.
If not, an error is returned.
*)
Definition enum_to_convertion_function (name: string) (l: list TypeLabelPair) : string :=
  "Definition convert_" ++ name ++ " (t: tree) : error_option " ++ name ++ add_linefeed " :=" ++
  add_linefeed "match getFirstChildValue t with" ++
  add_linefeed "| Some e => match string_of_list_ascii e with" ++
  fold_left append (map enum_list_element_to_convertion_function l) "" ++
  add_linefeed "| _ => Error ""Enum value is not an enum of specified type""" ++
  add_linefeed "end" ++
  add_linefeed "| None => Error ""No enum value found""" ++
  add_linefeed "end" ++
  add_linefeed ".".


(*
Creates a function to convert a structure element.
If the structure is an enum or oneof, their functions get called.
If the structure is a message, it created this functions head
and calls the <field_to_convertion_function> function.
*)
Fixpoint structure_to_convertion_function (s: Structure) : string :=
  match s with
  | enum name list => enum_to_convertion_function name (rename_reserved_keyword_typelabelpair_list list)
  | oneof name list => one_of_to_convertion_function name (rename_reserved_keyword_typelabelpair_list list)
  | message name before after => let after := rename_reserved_keyword_field_list after in
    (fold_left append (map structure_to_convertion_function before) "") ++ 
    "Definition convert_" ++ name ++ " (t: tree) : error_option " ++ name ++ add_linefeed " :=" ++
    field_to_convertion_function after after name ++ add_linefeed "."
  end.

(*necessary imports*)
Definition pre := "
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export grab.
From CoqE2EAI Require Export string_to_number.
From CoqE2EAI Require Export model.
From CoqE2EAI Require Export float.
From CoqE2EAI Require Export int.
From CoqE2EAI Require Export bytes.
From CoqE2EAI Require Export function_converter.

".

(*maps the <structure_to_convertion_function> on the list and appends the necessary imports*)
Definition function_converter (IR: list Structure) : string :=
  pre ++ fold_left append (map structure_to_convertion_function IR) (add_linefeed "").
