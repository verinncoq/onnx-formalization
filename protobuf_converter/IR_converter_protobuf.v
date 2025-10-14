From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export string_tree.
From CoqE2EAI Require Export error_option.

(*for testing*)
From CoqE2EAI Require Export preprocessor.
From CoqE2EAI Require Export tokenizer_protobuf.
From CoqE2EAI Require Export parser_protobuf.
From CoqE2EAI Require Export type_converter.

(*combines a type and a label (both given as a string)*)
Inductive TypeLabelPair :=
  | typelabelpair: string (*type*) -> string (*label*)-> TypeLabelPair
  .

(*one half of the protobuf model in rocq: field element with the cardinality as a constructor*)
Inductive Field :=
  | optional: TypeLabelPair -> Field
  | repeated: TypeLabelPair -> Field
  .

(*
One half of the protobuf model in rocq.
Enum: name and list of enum keys
One_of: name and list of elements without cardinality
Message: name, list of structures (nested messages, oneofs and enums), list of fields
*)
Inductive Structure :=
  | enum: string -> list TypeLabelPair -> Structure
  | oneof: string -> list TypeLabelPair -> Structure
  | message: string -> list Structure -> list Field -> Structure
  .


(*helpers*)

(*takes a list and checks of all elements are Success, if so, list is returnes as Success
If not, the first Error is returned*)
Fixpoint flatten_error_option {T: Type} (l: list (error_option T)) : error_option (list T) :=
  match l with
  | [] => Success []
  | h :: t => match h with
              | Success h' => match flatten_error_option t with
                             | Success t' => Success (h' :: t')
                             | Error e => Error e
                             end
              | Error e => Error e
              end
  end.

(*takes a list of lists and combines them to a single list*)
Fixpoint flatten_list {T: Type} (l: list (list T)) : list T :=
  match l with
  | [] => []
  | h :: t => h ++ flatten_list t
  end.



(* Converter functions *)


(*takes a list of trees that are children of a enum node's name*)
(*converts it to list of TypeLabelPairs, taking only the first name until a semicolon is found*)
Fixpoint convert_enum_children (c: list tree) (convert: bool) : list TypeLabelPair :=
  match c with
  | [] => []
  | tree::c' =>
    let name := match tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
    match name with
    | ";" => convert_enum_children c' true (*scan again*)
    | _ => match convert with
           | true => (typelabelpair name name) :: (convert_enum_children c' false)
           | false => convert_enum_children c' false
           end
    end
  end.

(*takes a list of trees that are children of a oneof node's name*)
(*converts it to list of TypeLabelPairs, following the rules of the protobuf syntax*)
Fixpoint convert_oneof_children (c: list tree) (convert: bool) : list (error_option TypeLabelPair) :=
  match c with
  | [] => []
  | tree::c' =>
    let name := match tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
    match name with
    | ";" => convert_oneof_children c' true (*scan again*)
    | _ => match convert with
      | true => match c' with
        | [] => [Error "found a type, but not a label"]
        | label_tree::c'' => let label := match label_tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
          Success (typelabelpair name label) :: (convert_oneof_children c' false)
        end
        | false => convert_oneof_children c' false
      end
    end
  end.

(*adds the message name at the end of the type of the pair*)
Definition add_message_name_typelabelpair_type (message_name: string) (t: TypeLabelPair) : TypeLabelPair :=
  match t with
  | typelabelpair type label => match is_basic_type type with
    | true => t (*type name does not change*)
    | false => typelabelpair (type ++ "_" ++ message_name) label
    end
  end.


Definition add_message_name_typelabelpair_label (message_name: string) (t: TypeLabelPair) : TypeLabelPair :=
  match t with
  | typelabelpair type label => typelabelpair type (label ++ "_" ++ message_name)
  end.

(*determines wether a certain element s is part of a list l*)
Fixpoint Inb (l: list string)(s: string) : bool :=
  match l with
  | [] => false
  | b :: m => 
    if (eqb b s) then true
    else Inb m s
  end.

(*renames all types of TypeLabelPairs (default, optional and repeated) in the list "after"*)
Fixpoint edit_after_names (message_name: string) (before_names: list string) (after: list Field) : list Field :=
  match after with
  | [] => []
  | h::t => match h with
    | optional (typelabelpair type label) => match Inb before_names type with
      | true => optional (typelabelpair (type ++ "_" ++ message_name) label) :: (edit_after_names message_name before_names t)
      | false => h :: (edit_after_names message_name before_names t)
      end
    | repeated (typelabelpair type label) => match Inb before_names type with
      | true => repeated (typelabelpair (type ++ "_" ++ message_name) label) :: (edit_after_names message_name before_names t)
      | false => h :: (edit_after_names message_name before_names t)
      end
    end
  end.

Definition structure_name (s: Structure) : string :=
  match s with
  | enum name _ => name
  | oneof name _ => name
  | message name _ _ => name
  end.

(*Input: before and after list of a message element
  Output: after list of the message element, but all fields that use a type declared by a enum, one_of or message in the list before have been renamed too*)
Definition add_message_name_field (message_name: string) (before: list Structure) (after: list Field) : list Field :=
  let names := (map structure_name before) in edit_after_names message_name names after.


(*adds the message name at the end of the name of the structure and all associated names*)
Fixpoint add_message_name_structure (message_name: string) (s: Structure) : Structure :=
  match s with
  | enum name pairs => enum (name ++ "_" ++ message_name) (map (add_message_name_typelabelpair_type message_name) pairs)
  | oneof name pairs => oneof (name ++ "_" ++ message_name) (map (add_message_name_typelabelpair_type message_name) pairs)
  | message name before after =>
    message (name ++ "_" ++ message_name) (map (add_message_name_structure message_name) before) (add_message_name_field message_name before after)
  end.

Open Scope list_scope.

Definition app_at_first {T1 T2: Type} (elem: T1) (prod: list T1 * list T2) : (list T1 * list T2) :=
  let first := fst prod in
  let second := snd prod in
  ([elem] ++ first, second).

Definition app_at_second {T1 T2: Type} (elem: T2) (prod: list T1 * list T2) : (list T1 * list T2) :=
  let first := fst prod in
  let second := snd prod in
  (first, [elem] ++ second).

Open Scope string_scope.

(*
Takes a list of trees that are children of a message node's name.
Converts it to two lists: a list of Structures and a list of Fields.
It iterates thought the input and performs different actions, depending on the keyword found.
*)
Fixpoint convert_message_children (c: list tree) (convert: bool) (max_depth: nat) : list (error_option Structure) * list (error_option Field) :=
  match max_depth with
  | O => ([Error "max_depth reached"], [])
  | S n =>  match c with
    | [] => ([], [])
    | tree::c' =>
      let name := match tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
      match name with
      | ";" => convert_message_children c' true n (*scan again*)
      | "enum" => match tree with
        | leaf _ => ([Error "enum must not be empty tree"],[])
        | subtree _ [] => ([Error "enum must not be empty tree"],[])
        | subtree _ (enum_name_tree::[]) => match enum_name_tree with
          | leaf _ => ([Error "enum can not have empty label set"],[])
          | subtree _ [] => ([Error "enum can not have empty label set"],[])
          | subtree enum_name enum_labels => app_at_first
            (Success (enum (string_of_list_ascii enum_name) (convert_enum_children enum_labels true)))
            (convert_message_children c' true n)
          end
        | subtree _ _ => ([Error "enum must have exactly one child"],[])
        end
      | "oneof" => match tree with
        | leaf _ => ([Error "oneof must not be empty tree"],[])
        | subtree _ [] => ([Error "oneof must not be empty tree"],[])
        | subtree _ (oneof_name_tree::[]) => match oneof_name_tree with
          | leaf _ => ([Error "oneof can not have empty label set"],[])
          | subtree _ [] => ([Error "oneof can not have empty label set"],[])
          | subtree oneof_name oneof_labels => match flatten_error_option (convert_oneof_children oneof_labels true) with
            | Error e => ([Error e],[])
            | Success oneof_children => let recursive := convert_message_children c' true n in
              let first_appended := 
                app_at_first
                (Success (oneof (string_of_list_ascii oneof_name) oneof_children))
                recursive
              in
              app_at_second (Success (optional (typelabelpair (string_of_list_ascii oneof_name) (string_of_list_ascii [])))) first_appended
            end
          end
        | subtree _ _ => ([Error "oneof must have exactly one child"],[])
        end
      | "message" => match tree with
        | leaf _ => ([Error "message must not be empty tree"],[])
        | subtree _ [] => ([Error "message must not be empty tree"],[])
        | subtree _ (message_name_tree::[]) => match message_name_tree with
          | leaf _ => ([Error "message can not have empty field list"],[])
          | subtree _ [] => ([Error "message can not have empty field list"],[])
          | subtree message_name structures_and_fields => let message_children := convert_message_children structures_and_fields true n in
            let before_option := fst message_children in
            let after_option  := snd message_children in
            match flatten_error_option before_option with
            | Error e => ([Error e],[])
            | Success before => match flatten_error_option after_option with
              | Error e => ([Error e],[])
              | Success after =>
                app_at_first
                (Success (message
                  (string_of_list_ascii message_name)
                  (map (add_message_name_structure (string_of_list_ascii message_name)) before)
                  (add_message_name_field (string_of_list_ascii message_name) before after)

                ))
                (convert_message_children c' true n)
              end
            end
          end
        | subtree _ _ => ([Error "message must have exactly one child"],[])
        end
      | _ => match convert with
        | true => let field_cardinality := name in
          match c' with
          | [] => ([Error ("After a field cardinality (optional, repeated) must be a valid type: "++name)],[])
          | _::[] => ([Error ("After a field cardinality (optional, repeated) must be a valid name: "++name)],[])
          | field_type_tree :: field_name_tree :: c'' => 
            let field_type := match field_type_tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
            let field_name := match field_name_tree with | leaf s => (string_of_list_ascii s) | subtree s _ => (string_of_list_ascii s) end in
            match field_cardinality with
            | "reserved" => convert_message_children c'' false n (*reserved is not handled by rocq*)
            | "optional" => app_at_second (Success (optional (typelabelpair field_type field_name))) (convert_message_children c'' false n)
            | "repeated" => app_at_second (Success (repeated (typelabelpair field_type field_name))) (convert_message_children c'' false n)
            | other => ([Error ("A field cardinality must be reserved, optional or repeated, " ++ other ++ " was given.")],[])
            end
          end
        | false => convert_message_children c' false n
        end
      end
    end
  end.

(*
Converts a tree, beginning with the message's name, into a message element.
The parameter <max_depth> should be large enough, if not, error is returned.
*)
Definition convert_message (t: tree) (max_depth: nat) : error_option Structure :=
  match t with
  | leaf name => Success (message (string_of_list_ascii name) [] [])
  | subtree name [] => Success (message (string_of_list_ascii name) [] [])
  | subtree name list => let message_children := convert_message_children list true max_depth in
    let before_option := fst message_children in
    let after_option  := snd message_children in
    match flatten_error_option before_option with
    | Success before => match flatten_error_option after_option with
      | Success after => Success (message (string_of_list_ascii name) before after)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.

(*
Converts a syntax tree which represents a whole file into IR
The first node must be a message, with exactly one child: main. Children of the main node represent the input file.
This function checks, if the tree is formed that way. If so, it converts the main message to a structure.
The parameter <max_depth> should be large enough, if not, error is returned
*)
Definition convert_to_IR (max_depth: nat) (t: tree) : error_option Structure :=
  match t with
  | leaf _ => Error "Main node not found. Well defined syntaxtree must begin with a message named <main>!"
  | subtree _ [] => Error "Main node not found. Well defined syntaxtree must begin with a message named <main>!"
  | subtree n children => let name := (string_of_list_ascii n) in
    match name with
    | "message" =>
      match children with
      | [] => Error "Main node not found. Well defined syntaxtree must begin with a message named <main>!"
      | h::[] => (*when seeing message node, first child should be the name, which must be <main>*)
        match h with
        | leaf _ => Error "Main node should never be a leaf node."
        | subtree _ [] => Error "Main node should never be a leaf node."
        | subtree n' children' => let name' := (string_of_list_ascii n') in
          match name' with
          | "main" => convert_message h max_depth
          | _ => Error "Main node not found. Well defined syntaxtree must begin with a message named <main>!"
          end
        end
      | _ => Error "More than one children in first message node"
      end
    | e => Error ("Found Keyword" ++ e ++ ". Well defined syntaxtree must begin with a message named <main>!")
    end
  end.
