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

Definition convert_field (name : string) (field : Field) : string :=
  match field with
  | optional (typelabelpair type label) => (if label =? "" then name ++ "_" ++ type else name ++ "_" ++ label) ++ " : option " ++ (convert_type type) ++ ";"
  | repeated (typelabelpair type label) => (if label =? "" then name ++ "_" ++ type else name ++ "_" ++ label) ++ " : list " ++ (convert_type type) ++ ";"
  end.

(* Definition convert_field (field: Field) : string := *)
(*   match field with *)
(*   | optional (typelabelpair type label) => "option " ++ (convert_type type) ++ " (*" ++ label  ++ "*) -> " *)
(*   | repeated (typelabelpair type label) => "list " ++ (convert_type type) ++ " (*" ++ label ++ "*) -> " *)
(*   end. *)

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
        (* "Inductive " ++ name ++ add_linefeed " :=" ++ (add_linefeed ("| " ++ name ++ "_constructor: ")) ++ *)

        "Record " ++ name ++ add_linefeed " := " ++ (add_linefeed (name ++ "_constructor {")) ++
      fold_left append (map add_linefeed (map (convert_field name) after)) "" ++
      add_linefeed "}."
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

Definition test : list Structure :=
[enum "Version"
            [typelabelpair "_START_VERSION" "_START_VERSION";
             typelabelpair "IR_VERSION_2017_10_10" "IR_VERSION_2017_10_10";
             typelabelpair "IR_VERSION_2017_10_30" "IR_VERSION_2017_10_30";
             typelabelpair "IR_VERSION_2017_11_3" "IR_VERSION_2017_11_3";
             typelabelpair "IR_VERSION_2019_1_22" "IR_VERSION_2019_1_22";
             typelabelpair "IR_VERSION_2019_3_18" "IR_VERSION_2019_3_18";
             typelabelpair "IR_VERSION_2019_9_19" "IR_VERSION_2019_9_19";
             typelabelpair "IR_VERSION_2020_5_8" "IR_VERSION_2020_5_8";
             typelabelpair "IR_VERSION_2021_7_30" "IR_VERSION_2021_7_30";
             typelabelpair "IR_VERSION_2023_5_5" "IR_VERSION_2023_5_5";
             typelabelpair "IR_VERSION_2024_3_25" "IR_VERSION_2024_3_25";
             typelabelpair "IR_VERSION" "IR_VERSION"];
          message "IntIntListEntryProto" []
            [optional (typelabelpair "int64" "key");
             repeated (typelabelpair "int64" "value")];
          message "SimpleShardedDimProto"
            [oneof "dim_SimpleShardedDimProto"
               [typelabelpair "int64" "dim_value"; typelabelpair "string" "dim_param"]]
            [optional (typelabelpair "dim_SimpleShardedDimProto" "");
             optional (typelabelpair "int64" "num_shards")];
          message "DeviceConfigurationProto" []
            [optional (typelabelpair "string" "name");
             optional (typelabelpair "int32" "num_devices");
             repeated (typelabelpair "string" "device")];
          message "StringStringEntryProto" []
            [optional (typelabelpair "string" "key");
             optional (typelabelpair "string" "value")];
          message "TensorAnnotation" []
            [optional (typelabelpair "string" "tensor_name");
             repeated
               (typelabelpair "StringStringEntryProto" "quant_parameter_tensor_names")];
          message "TensorProto"
            [enum "DataType_TensorProto"
               [typelabelpair "UNDEFINED_TensorProto" "UNDEFINED";
                typelabelpair "FLOAT_TensorProto" "FLOAT";
                typelabelpair "UINT8_TensorProto" "UINT8";
                typelabelpair "INT8_TensorProto" "INT8";
                typelabelpair "UINT16_TensorProto" "UINT16";
                typelabelpair "INT16_TensorProto" "INT16";
                typelabelpair "INT32_TensorProto" "INT32";
                typelabelpair "INT64_TensorProto" "INT64";
                typelabelpair "STRING_TensorProto" "STRING";
                typelabelpair "BOOL_TensorProto" "BOOL";
                typelabelpair "FLOAT16_TensorProto" "FLOAT16";
                typelabelpair "DOUBLE_TensorProto" "DOUBLE";
                typelabelpair "UINT32_TensorProto" "UINT32";
                typelabelpair "UINT64_TensorProto" "UINT64";
                typelabelpair "COMPLEX64_TensorProto" "COMPLEX64";
                typelabelpair "COMPLEX128_TensorProto" "COMPLEX128";
                typelabelpair "BFLOAT16_TensorProto" "BFLOAT16";
                typelabelpair "FLOAT8E4M3FN_TensorProto" "FLOAT8E4M3FN";
                typelabelpair "FLOAT8E4M3FNUZ_TensorProto" "FLOAT8E4M3FNUZ";
                typelabelpair "FLOAT8E5M2_TensorProto" "FLOAT8E5M2";
                typelabelpair "FLOAT8E5M2FNUZ_TensorProto" "FLOAT8E5M2FNUZ";
                typelabelpair "UINT4_TensorProto" "UINT4";
                typelabelpair "INT4_TensorProto" "INT4";
                typelabelpair "FLOAT4E2M1_TensorProto" "FLOAT4E2M1"];
             message "Segment_TensorProto" []
               [optional (typelabelpair "int64" "begin");
                optional (typelabelpair "int64" "end")];
             enum "DataLocation_TensorProto"
               [typelabelpair "DEFAULT_TensorProto" "DEFAULT";
                typelabelpair "EXTERNAL_TensorProto" "EXTERNAL"]]
            [repeated (typelabelpair "int64" "dims");
             optional (typelabelpair "int32" "data_type");
             optional (typelabelpair "Segment_TensorProto" "segment");
             repeated (typelabelpair "float" "float_data");
             repeated (typelabelpair "int32" "int32_data");
             repeated (typelabelpair "bytes" "string_data");
             repeated (typelabelpair "int64" "int64_data");
             optional (typelabelpair "string" "name");
             optional (typelabelpair "string" "doc_string");
             optional (typelabelpair "bytes" "raw_data");
             repeated (typelabelpair "StringStringEntryProto" "external_data");
             optional (typelabelpair "DataLocation_TensorProto" "data_location");
             repeated (typelabelpair "double" "double_data");
             repeated (typelabelpair "uint64" "uint64_data");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props")];
          message "SparseTensorProto" []
            [optional (typelabelpair "TensorProto" "values");
             optional (typelabelpair "TensorProto" "indices");
             repeated (typelabelpair "int64" "dims")];
          message "TensorShapeProto"
            [message "Dimension_TensorShapeProto"
               [oneof "value_Dimension_TensorShapeProto"
                  [typelabelpair "int64" "dim_value";
                   typelabelpair "string" "dim_param"]]
               [optional (typelabelpair "value_Dimension_TensorShapeProto" "");
                optional (typelabelpair "string" "denotation")]]
            [repeated (typelabelpair "Dimension_TensorShapeProto" "dim")];
          message "TypeProto"
            [message "Tensor_TypeProto" []
               [optional (typelabelpair "int32" "elem_type");
                optional (typelabelpair "TensorShapeProto" "shape")];
             message "Sequence_TypeProto" []
               [optional (typelabelpair "string" "elem_type")];
             message "Map_TypeProto" []
               [optional (typelabelpair "int32" "key_type");
                optional (typelabelpair "string" "value_type")];
             message "Optional_TypeProto" []
               [optional (typelabelpair "string" "elem_type")];
             message "SparseTensor_TypeProto" []
               [optional (typelabelpair "int32" "elem_type");
                optional (typelabelpair "TensorShapeProto" "shape")];
             oneof "value_TypeProto"
               [typelabelpair "Tensor_TypeProto" "tensor_type";
                typelabelpair "Sequence_TypeProto" "sequence_type";
                typelabelpair "Map_TypeProto" "map_type";
                typelabelpair "Optional_TypeProto" "optional_type";
                typelabelpair "SparseTensor_TypeProto" "sparse_tensor_type"]]
            [optional (typelabelpair "value_TypeProto" "");
             optional (typelabelpair "string" "denotation")];
          message "OperatorSetIdProto" []
            [optional (typelabelpair "string" "domain");
             optional (typelabelpair "int64" "version")];
          enum "OperatorStatus"
            [typelabelpair "EXPERIMENTAL" "EXPERIMENTAL";
             typelabelpair "STABLE" "STABLE"];
          message "AttributeProto"
            [enum "AttributeType_AttributeProto"
               [typelabelpair "UNDEFINED_AttributeProto" "UNDEFINED";
                typelabelpair "FLOAT_AttributeProto" "FLOAT";
                typelabelpair "INT_AttributeProto" "INT";
                typelabelpair "STRING_AttributeProto" "STRING";
                typelabelpair "TENSOR_AttributeProto" "TENSOR";
                typelabelpair "GRAPH_AttributeProto" "GRAPH";
                typelabelpair "SPARSE_TENSOR_AttributeProto" "SPARSE_TENSOR";
                typelabelpair "TYPE_PROTO_AttributeProto" "TYPE_PROTO";
                typelabelpair "FLOATS_AttributeProto" "FLOATS";
                typelabelpair "INTS_AttributeProto" "INTS";
                typelabelpair "STRINGS_AttributeProto" "STRINGS";
                typelabelpair "TENSORS_AttributeProto" "TENSORS";
                typelabelpair "GRAPHS_AttributeProto" "GRAPHS";
                typelabelpair "SPARSE_TENSORS_AttributeProto" "SPARSE_TENSORS";
                typelabelpair "TYPE_PROTOS_AttributeProto" "TYPE_PROTOS"]]
            [optional (typelabelpair "string" "name");
             optional (typelabelpair "string" "ref_attr_name");
             optional (typelabelpair "string" "doc_string");
             optional (typelabelpair "AttributeType_AttributeProto" "type");
             optional (typelabelpair "float" "f");
             optional (typelabelpair "int64" "i");
             optional (typelabelpair "bytes" "s");
             optional (typelabelpair "TensorProto" "t");
             optional (typelabelpair "SparseTensorProto" "sparse_tensor");
             optional (typelabelpair "TypeProto" "tp");
             repeated (typelabelpair "float" "floats");
             repeated (typelabelpair "int64" "ints");
             repeated (typelabelpair "bytes" "strings");
             repeated (typelabelpair "TensorProto" "tensors");
             repeated (typelabelpair "SparseTensorProto" "sparse_tensors");
             repeated (typelabelpair "TypeProto" "type_protos")];
          message "ValueInfoProto" []
            [optional (typelabelpair "string" "name");
             optional (typelabelpair "TypeProto" "type");
             optional (typelabelpair "string" "doc_string");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props")];
          message "ShardedDimProto" []
            [optional (typelabelpair "int64" "axis");
             repeated (typelabelpair "SimpleShardedDimProto" "simple_sharding")];
          message "ShardingSpecProto" []
            [optional (typelabelpair "string" "tensor_name");
             repeated (typelabelpair "int64" "device");
             repeated
               (typelabelpair "IntIntListEntryProto" "index_to_device_group_map");
             repeated (typelabelpair "ShardedDimProto" "sharded_dim")];
          message "NodeDeviceConfigurationProto" []
            [optional (typelabelpair "string" "configuration_id");
             repeated (typelabelpair "ShardingSpecProto" "sharding_spec");
             optional (typelabelpair "int32" "pipeline_stage")];
          message "NodeProto" []
            [repeated (typelabelpair "string" "input");
             repeated (typelabelpair "string" "output");
             optional (typelabelpair "string" "name");
             optional (typelabelpair "string" "op_type");
             optional (typelabelpair "string" "domain");
             optional (typelabelpair "string" "overload");
             repeated (typelabelpair "AttributeProto" "attribute");
             optional (typelabelpair "string" "doc_string");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props");
             repeated
               (typelabelpair "NodeDeviceConfigurationProto" "device_configurations")];
          message "GraphProto" []
            [repeated (typelabelpair "NodeProto" "node");
             optional (typelabelpair "string" "name");
             repeated (typelabelpair "TensorProto" "initializer");
             repeated (typelabelpair "SparseTensorProto" "sparse_initializer");
             optional (typelabelpair "string" "doc_string");
             repeated (typelabelpair "ValueInfoProto" "input");
             repeated (typelabelpair "ValueInfoProto" "output");
             repeated (typelabelpair "ValueInfoProto" "value_info");
             repeated (typelabelpair "TensorAnnotation" "quantization_annotation");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props")];
          message "FunctionProto" []
            [optional (typelabelpair "string" "name");
             repeated (typelabelpair "string" "input");
             repeated (typelabelpair "string" "output");
             repeated (typelabelpair "string" "attribute");
             repeated (typelabelpair "AttributeProto" "attribute_proto");
             repeated (typelabelpair "NodeProto" "node");
             optional (typelabelpair "string" "doc_string");
             repeated (typelabelpair "OperatorSetIdProto" "opset_import");
             optional (typelabelpair "string" "domain");
             optional (typelabelpair "string" "overload");
             repeated (typelabelpair "ValueInfoProto" "value_info");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props")];
          message "TrainingInfoProto" []
            [optional (typelabelpair "GraphProto" "initialization");
             optional (typelabelpair "GraphProto" "algorithm");
             repeated (typelabelpair "StringStringEntryProto" "initialization_binding");
             repeated (typelabelpair "StringStringEntryProto" "update_binding")];
          message "ModelProto" []
            [optional (typelabelpair "int64" "ir_version");
             repeated (typelabelpair "OperatorSetIdProto" "opset_import");
             optional (typelabelpair "string" "producer_name");
             optional (typelabelpair "string" "producer_version");
             optional (typelabelpair "string" "domain");
             optional (typelabelpair "int64" "model_version");
             optional (typelabelpair "string" "doc_string");
             optional (typelabelpair "GraphProto" "graph");
             repeated (typelabelpair "StringStringEntryProto" "metadata_props");
             repeated (typelabelpair "TrainingInfoProto" "training_info");
             repeated (typelabelpair "FunctionProto" "functions");
             repeated (typelabelpair "DeviceConfigurationProto" "configuration")]].

Compute (model_converter test).
