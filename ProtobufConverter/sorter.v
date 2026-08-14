From Stdlib Require Import String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import NArith.BinNat.

From ONNXFormalization.ProtobufConverter Require Export IR_converter_protobuf.
From ONNXFormalization.ProtobufConverter Require Export type_converter.
From ONNXFormalization.ProtobufConverter Require Export model_converter.

(*determines wether a certain element s is part of a list l*)
Fixpoint Inb (l: list string)(s: string) : bool :=
  match l with
  | [] => false
  | b :: m => 
    if (eqb b s) then true
    else Inb m s
  end.

(*for a given list Structure, it returnes all the names of structures defined in it, excluding nested ones*)
Fixpoint defined_message_names (defined: list Structure) : list string :=
  match defined with
  | [] => []
  | h::t => match h with
	| enum name _ => name :: defined_message_names t
	| oneof name _ => name :: defined_message_names t
    | message name _ _ => name :: defined_message_names t
    end
  end.

(*returns all the types inside of a list of TypeLabelPairs*)
Fixpoint type_label_pair_list_to_type_list (l: list TypeLabelPair) : list string :=
  match l with
  | [] => []
  | (typelabelpair type _)::t => type :: type_label_pair_list_to_type_list t
  end.

(*takes a list of lists and combines them to a single list*)
Fixpoint list_list_to_list {T: Type} (l: list (list T)) : list T :=
  match l with
  | [] => []
  | h::t => h ++ (list_list_to_list t)
  end.

(*returns the type of the field*)
Definition field_type (f: Field) : string :=
  match f with
  | optional (typelabelpair type _) => type
  | repeated (typelabelpair type _) => type
  end.

(*
Returns a list of names from all the messages than need to be defined before the Structur s gets defined.
If s is enum, no message needs to be defined before.
If s is oneof, all the fields that don't use standard types (basic_type) use other message types -> they need to be defined before.
If s is message, all the nested elements in list structure need to be checked recursively if the use any messages element.
  Also, all the fields in list field that don't use standard types (basic_type) use other message types -> they need to be defined before.
*)
Fixpoint needed_message_names_structure (s: Structure) : list string :=
  match s with
  | enum _ _ => []
  | oneof _ list => filter (fun x => negb (is_basic_type x)) (type_label_pair_list_to_type_list list)
  | message _ before after => list_list_to_list (map needed_message_names_structure before) ++ filter (fun x => negb (is_basic_type x)) (map field_type after)
  end.

(*returns all the names of messages, that are defined in this structure s, for example names of nested messages*)
Fixpoint self_defining_message_names (s: Structure) : list string :=
  match s with
  | enum name _ => [name]
  | oneof name _ => [name]
  | message name before after => [name] ++ list_list_to_list (map self_defining_message_names before)
  end.

(*Concats a list of strings into a single string, seperating them by commas, for error string creation*)
Fixpoint list_string_to_string_beautiful (l: list string) : string :=
  match l with
  | [] => ""
  | h :: [] => h
  | h :: t => h ++ ", " ++ list_string_to_string_beautiful t
  end.

(*Converts a field element into a readable string, for error string creation*)
Definition field_to_string (f: Field) : string :=
  let needed_names := filter (fun x => negb (is_basic_type x)) [field_type f] in
  let depends := list_string_to_string_beautiful needed_names in
  match f with
  | optional (typelabelpair type label) => add_linefeed (add_linefeed ("optional element with type: " ++ type ++ " and label: " ++ label ++ " (depends on: " ++ depends ++")"))
  | repeated (typelabelpair type label) => add_linefeed (add_linefeed ("repeated element with type: " ++ type ++ " and label: " ++ label ++ " (depends on: " ++ depends ++")"))
  end.

(*Converts a structure element into a readable string, for error string creation*)
Definition structure_to_string (s: Structure) : string :=
  let needed_names_without_self_defining_message_names := filter (fun x => negb (is_basic_type x)) (needed_message_names_structure s) in
  let needed_names := filter (fun x => negb (Inb (self_defining_message_names s) x)) needed_names_without_self_defining_message_names in
  let depends := list_string_to_string_beautiful needed_names in
  match s with
  | enum name _ => add_linefeed (add_linefeed ("enum element with name: " ++ name ++ " (depends on: " ++ depends ++")"))
  | oneof name _ => add_linefeed (add_linefeed ("oneof element with name: " ++ name ++ " (depends on: " ++ depends ++")"))
  | message name _ _ => add_linefeed (add_linefeed ("message element with name: " ++ name ++ " (depends on: " ++ depends ++")"))
  end.

(*
Sorts the structure given in <input>, puts the sorted ones in <output>
If there is a circular dependency, function cannot stop. To make it always stop, the parameter depth is there.
If it reaches zero, an Error is given, with a comprehensive text, which elements where unable to sort and on which other elements they depend on.

The functions checks the first element depending on it's constructor.
If all the elements it depends on are already defined (part of the output list or defined list),
it gets also appended at the output list. If not, it remains in the input list, but at the very end.
When the whole list is worked though, it is likely that the elements it depends on have been defined in the meantime.

The constructors are:
enum:    Can always be defined, because all of it's constructors use no arguments.
oneof:   All it's fields are filtered for fields than don't use standard data types.
         If their types are defined either in the output list or the defined list,
         the element can be put into the output list, too.
message: First, all types needed for this element are computed.
         Then, the list is filtered, removing all the types that are defined in the message by itself
         (for example names of nested messages or oneof's).
         If their types are defined either in the output list or the defined list, this elements can be defined.
         Before it happens, the inner structures (defined in the list Structure argument) need to be sorted also.
         This call this functions recursively, putting everything that has been defined already in the argument <defined>.
*)
Fixpoint sort_structures_recursive (depth: nat) (input output: list Structure) (defined: list string) : error_option (list Structure) :=
  match depth with
  | 0 => match input with 
    | [] => Success output
    | _ => Error (add_linefeed (add_linefeed "Unable to sort list. There must be a circular dependency. The following Elements where unable to sort:") ++ fold_left append (map structure_to_string input) "")
    end
  | S n => match input with
    | [] => Success output
    | h::t => match h with
      | enum _ _ => sort_structures_recursive n t (output ++ [h]) defined (*enum can always be defined*)
      | oneof _ list =>
        let type_list := filter (fun x => negb (is_basic_type x)) (type_label_pair_list_to_type_list list) in 
        match forallb (Inb ((defined_message_names output) ++ defined)) type_list with
        | true => sort_structures_recursive n t (output ++ [h]) defined (*all types of the one_of list has been declared before*)
        | false => sort_structures_recursive n (t ++ [h]) output defined (*at least one type of the one_of list has not been declared before*)
        end
      | message name before after => let needed_names_without_self_defining_message_names :=
        filter (fun x => negb (is_basic_type x)) (needed_message_names_structure h) in
        let needed_names := filter (fun x => negb (Inb (self_defining_message_names h) x)) needed_names_without_self_defining_message_names in
        match forallb (Inb ((defined_message_names output) ++ defined)) needed_names with
        | true => (*all types of the message type has been declared before, sort inner structures*)
          match sort_structures_recursive n before [] ((defined_message_names output) ++ defined) with
          | Success new_before => let new_message := message name new_before after in
            sort_structures_recursive n t (output ++ [new_message]) defined
          | Error e => Error e
          end
        | false => sort_structures_recursive n (t ++ [h]) output defined (*at least one type of the message type has not been declared before*)
        end
      end
    end
  end.

From Stdlib Require Import Nat.

(*returns the length of the longest_list_structure*)
Fixpoint longest_list_structure (s: Structure) : nat :=
  match s with
  | enum _ _ => 0
  | oneof _ _ => 0
  | message _ l _ => max (length l) (fold_left max (map longest_list_structure l) 0)
  end.

(*returns the depth of a Structure*)
Fixpoint depth (s: Structure) : nat :=
  match s with
  | enum _ _ => 0
  | oneof _ _ => 0
  | message _ l _ => 1 + (fold_left max (map depth l) 0)
  end.

(*calls sort_structures_recursive, with initializing arguments*)
Definition sort_structures (input: list Structure) : error_option (list Structure) :=
  let n_max := longest_list_structure (message "" input []) in
  let d_max := fold_left max (map depth input) 0 in
  let depth := (square n_max) * (d_max + 1) in
  sort_structures_recursive depth input [] [].

