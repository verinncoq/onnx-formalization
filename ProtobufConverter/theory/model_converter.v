From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.
Open Scope string_scope.
From Stdlib Require Import Lists.List. Import ListNotations.

From ONNXFormalization.External Require Export add_linefeed.
From ONNXFormalization.External Require Export string_tree.
From ONNXFormalization.External Require Export error_option.

From ONNXFormalization.ProtobufConverter Require Export IR_converter_protobuf.

(*Converts the label of an enum-Structure, having the type as a constructor's name*)
Definition convert_enum_label (label: TypeLabelPair) : string := 
  match label with
  | typelabelpair type label => "| " ++ add_linefeed type
  end.

(*converts the list argument of an enum-Structure into constructors*)
Definition convert_enum_labels (labels: list TypeLabelPair) : string := fold_left append (map convert_enum_label labels) "".

(*Converts the label of an oneof-Structure into a constructor with one argument (with <type> as it's type)*)
Definition convert_oneof_label (name: string) (t: TypeLabelPair) : string :=
  let type := match t with | typelabelpair type label => type end in
  let label := match t with | typelabelpair type label => label end in
  "| " ++ label ++ "_" ++ name ++ ": " ++ (convert_type type) ++ " -> " ++ add_linefeed name.

(*converts the list argument of an oneof-Structure into constructors with one argument (with <type> as it's type)*)
Definition convert_oneof_labels (name: string) (labels: list TypeLabelPair) : string :=
  fold_left append (map (convert_oneof_label name) labels) "".

(*Converts a field into an argument (with (cardinality <type>) as it's type)*)
Definition convert_field (field: Field) : string :=
  match field with
  | optional (typelabelpair type label) => "option " ++ (convert_type type) ++ " (*" ++ label  ++ "*) -> "
  | repeated (typelabelpair type label) => "list " ++ (convert_type type) ++ " (*" ++ label ++ "*) -> "
  end.

(*
Converts a Structure, depending on it's constructor:
enum     Inductive Type with <name> as name, constructors for this type are converted in convert_enum_labels.
oneof    Inductive Type with <name> as name, constructors for this type are converted in convert_oneof_labels.
message  Maps this functions recursively on all the Structures in the <list structure> argument.
         Then creates inductive Type with <name> as name, constructors for this type are converted in convert_field.
*)
Fixpoint convert_structure (structure: Structure) : string :=
  match structure with
  | enum name labels => 
    add_linefeed"" ++
    "Inductive " ++ name ++ add_linefeed " :=" ++
    convert_enum_labels labels ++
    add_linefeed "."
  | oneof name labels =>
    add_linefeed"" ++
    "Inductive " ++ name ++ add_linefeed " :=" ++
    convert_oneof_labels name labels ++
    add_linefeed "."
  | message name before after =>
      add_linefeed (fold_left append (map convert_structure before) "") ++
      "Inductive " ++ name ++ add_linefeed " :=" ++ (add_linefeed ("| " ++ name ++ "_constructor: ")) ++
      fold_left append (map add_linefeed (map convert_field after)) "" ++
      name ++ add_linefeed "."
  end.

(*Applies convert_structure on all structures, adding all the necessary imports*)
Definition model_converter (l: list Structure) : string :=
  add_linefeed "(* This file was generated automatically by ProtobufConverter *)" ++
  add_linefeed "" ++
  add_linefeed "From Stdlib Require Import Strings.String." ++
  add_linefeed "From Stdlib Require Import Lists.List. Import ListNotations." ++
  add_linefeed "From ONNXFormalization.ProtobufDatatypes Require Export float." ++
  add_linefeed "From ONNXFormalization.ProtobufDatatypes Require Export int." ++
  add_linefeed "From ONNXFormalization.ProtobufDatatypes Require Export bytes." ++
  add_linefeed "" ++
  fold_left append (map convert_structure l) ""
  .

