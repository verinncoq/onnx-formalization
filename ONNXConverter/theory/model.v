(* This file was generated automatically by ProtobufConverter *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.


Inductive Version :=
| _START_VERSION
| IR_VERSION_2017_10_10
| IR_VERSION_2017_10_30
| IR_VERSION_2017_11_3
| IR_VERSION_2019_1_22
| IR_VERSION_2019_3_18
| IR_VERSION_2019_9_19
| IR_VERSION_2020_5_8
| IR_VERSION_2021_7_30
| IR_VERSION_2023_5_5
| IR_VERSION_2024_3_25
| IR_VERSION
.

Record IntIntListEntryProto := 
IntIntListEntryProto_constructor {
IntIntListEntryProto_key : option int64;
IntIntListEntryProto_value : list int64;
}.

Inductive dim_SimpleShardedDimProto :=
| dim_value_dim_SimpleShardedDimProto: int64 -> dim_SimpleShardedDimProto
| dim_param_dim_SimpleShardedDimProto: string -> dim_SimpleShardedDimProto
.

Record SimpleShardedDimProto := 
SimpleShardedDimProto_constructor {
SimpleShardedDimProto_dim_SimpleShardedDimProto : option dim_SimpleShardedDimProto;
SimpleShardedDimProto_num_shards : option int64;
}.

Record DeviceConfigurationProto := 
DeviceConfigurationProto_constructor {
DeviceConfigurationProto_name : option string;
DeviceConfigurationProto_num_devices : option int32;
DeviceConfigurationProto_device : list string;
}.

Record StringStringEntryProto := 
StringStringEntryProto_constructor {
StringStringEntryProto_key : option string;
StringStringEntryProto_value : option string;
}.

Record TensorAnnotation := 
TensorAnnotation_constructor {
TensorAnnotation_tensor_name : option string;
TensorAnnotation_quant_parameter_tensor_names : list StringStringEntryProto;
}.

Inductive DataType_TensorProto :=
| UNDEFINED_TensorProto
| FLOAT_TensorProto
| UINT8_TensorProto
| INT8_TensorProto
| UINT16_TensorProto
| INT16_TensorProto
| INT32_TensorProto
| INT64_TensorProto
| STRING_TensorProto
| BOOL_TensorProto
| FLOAT16_TensorProto
| DOUBLE_TensorProto
| UINT32_TensorProto
| UINT64_TensorProto
| COMPLEX64_TensorProto
| COMPLEX128_TensorProto
| BFLOAT16_TensorProto
| FLOAT8E4M3FN_TensorProto
| FLOAT8E4M3FNUZ_TensorProto
| FLOAT8E5M2_TensorProto
| FLOAT8E5M2FNUZ_TensorProto
| UINT4_TensorProto
| INT4_TensorProto
| FLOAT4E2M1_TensorProto
.

Record Segment_TensorProto := 
Segment_TensorProto_constructor {
Segment_TensorProto_begin : option int64;
Segment_TensorProto_end : option int64;
}.

Inductive DataLocation_TensorProto :=
| DEFAULT_TensorProto
| EXTERNAL_TensorProto
.

Record TensorProto := 
TensorProto_constructor {
TensorProto_dims : list int64;
TensorProto_data_type : option int32;
TensorProto_segment : option Segment_TensorProto;
TensorProto_float_data : list float32;
TensorProto_int32_data : list int32;
TensorProto_string_data : list bytes;
TensorProto_int64_data : list int64;
TensorProto_name : option string;
TensorProto_doc_string : option string;
TensorProto_raw_data : option bytes;
TensorProto_external_data : list StringStringEntryProto;
TensorProto_data_location : option DataLocation_TensorProto;
TensorProto_double_data : list float64;
TensorProto_uint64_data : list uint64;
TensorProto_metadata_props : list StringStringEntryProto;
}.

Record SparseTensorProto := 
SparseTensorProto_constructor {
SparseTensorProto_values : option TensorProto;
SparseTensorProto_indices : option TensorProto;
SparseTensorProto_dims : list int64;
}.

Inductive value_Dimension_TensorShapeProto :=
| dim_value_value_Dimension_TensorShapeProto: int64 -> value_Dimension_TensorShapeProto
| dim_param_value_Dimension_TensorShapeProto: string -> value_Dimension_TensorShapeProto
.

Record Dimension_TensorShapeProto := 
Dimension_TensorShapeProto_constructor {
Dimension_TensorShapeProto_value_Dimension_TensorShapeProto : option value_Dimension_TensorShapeProto;
Dimension_TensorShapeProto_denotation : option string;
}.

Record TensorShapeProto := 
TensorShapeProto_constructor {
TensorShapeProto_dim : list Dimension_TensorShapeProto;
}.

Record Tensor_TypeProto := 
Tensor_TypeProto_constructor {
Tensor_TypeProto_elem_type : option int32;
Tensor_TypeProto_shape : option TensorShapeProto;
}.

Record Sequence_TypeProto := 
Sequence_TypeProto_constructor {
Sequence_TypeProto_elem_type : option string;
}.

Record Map_TypeProto := 
Map_TypeProto_constructor {
Map_TypeProto_key_type : option int32;
Map_TypeProto_value_type : option string;
}.

Record Optional_TypeProto := 
Optional_TypeProto_constructor {
Optional_TypeProto_elem_type : option string;
}.

Record SparseTensor_TypeProto := 
SparseTensor_TypeProto_constructor {
SparseTensor_TypeProto_elem_type : option int32;
SparseTensor_TypeProto_shape : option TensorShapeProto;
}.

Inductive value_TypeProto :=
| tensor_type_value_TypeProto: Tensor_TypeProto -> value_TypeProto
| sequence_type_value_TypeProto: Sequence_TypeProto -> value_TypeProto
| map_type_value_TypeProto: Map_TypeProto -> value_TypeProto
| optional_type_value_TypeProto: Optional_TypeProto -> value_TypeProto
| sparse_tensor_type_value_TypeProto: SparseTensor_TypeProto -> value_TypeProto
.

Record TypeProto := 
TypeProto_constructor {
TypeProto_value_TypeProto : option value_TypeProto;
TypeProto_denotation : option string;
}.

Record OperatorSetIdProto := 
OperatorSetIdProto_constructor {
OperatorSetIdProto_domain : option string;
OperatorSetIdProto_version : option int64;
}.

Inductive OperatorStatus :=
| EXPERIMENTAL
| STABLE
.

Inductive AttributeType_AttributeProto :=
| UNDEFINED_AttributeProto
| FLOAT_AttributeProto
| INT_AttributeProto
| STRING_AttributeProto
| TENSOR_AttributeProto
| GRAPH_AttributeProto
| SPARSE_TENSOR_AttributeProto
| TYPE_PROTO_AttributeProto
| FLOATS_AttributeProto
| INTS_AttributeProto
| STRINGS_AttributeProto
| TENSORS_AttributeProto
| GRAPHS_AttributeProto
| SPARSE_TENSORS_AttributeProto
| TYPE_PROTOS_AttributeProto
.

Record AttributeProto := 
AttributeProto_constructor {
AttributeProto_name : option string;
AttributeProto_ref_attr_name : option string;
AttributeProto_doc_string : option string;
AttributeProto_type : option AttributeType_AttributeProto;
AttributeProto_f : option float32;
AttributeProto_i : option int64;
AttributeProto_s : option bytes;
AttributeProto_t : option TensorProto;
AttributeProto_sparse_tensor : option SparseTensorProto;
AttributeProto_tp : option TypeProto;
AttributeProto_floats : list float32;
AttributeProto_ints : list int64;
AttributeProto_strings : list bytes;
AttributeProto_tensors : list TensorProto;
AttributeProto_sparse_tensors : list SparseTensorProto;
AttributeProto_type_protos : list TypeProto;
}.

Record ValueInfoProto := 
ValueInfoProto_constructor {
ValueInfoProto_name : option string;
ValueInfoProto_type : option TypeProto;
ValueInfoProto_doc_string : option string;
ValueInfoProto_metadata_props : list StringStringEntryProto;
}.

Record ShardedDimProto := 
ShardedDimProto_constructor {
ShardedDimProto_axis : option int64;
ShardedDimProto_simple_sharding : list SimpleShardedDimProto;
}.

Record ShardingSpecProto := 
ShardingSpecProto_constructor {
ShardingSpecProto_tensor_name : option string;
ShardingSpecProto_device : list int64;
ShardingSpecProto_index_to_device_group_map : list IntIntListEntryProto;
ShardingSpecProto_sharded_dim : list ShardedDimProto;
}.

Record NodeDeviceConfigurationProto := 
NodeDeviceConfigurationProto_constructor {
NodeDeviceConfigurationProto_configuration_id : option string;
NodeDeviceConfigurationProto_sharding_spec : list ShardingSpecProto;
NodeDeviceConfigurationProto_pipeline_stage : option int32;
}.

Record NodeProto := 
NodeProto_constructor {
NodeProto_input : list string;
NodeProto_output : list string;
NodeProto_name : option string;
NodeProto_op_type : option string;
NodeProto_domain : option string;
NodeProto_overload : option string;
NodeProto_attribute : list AttributeProto;
NodeProto_doc_string : option string;
NodeProto_metadata_props : list StringStringEntryProto;
NodeProto_device_configurations : list NodeDeviceConfigurationProto;
}.

Record GraphProto := 
GraphProto_constructor {
GraphProto_node : list NodeProto;
GraphProto_name : option string;
GraphProto_initializer : list TensorProto;
GraphProto_sparse_initializer : list SparseTensorProto;
GraphProto_doc_string : option string;
GraphProto_input : list ValueInfoProto;
GraphProto_output : list ValueInfoProto;
GraphProto_value_info : list ValueInfoProto;
GraphProto_quantization_annotation : list TensorAnnotation;
GraphProto_metadata_props : list StringStringEntryProto;
}.

Record FunctionProto := 
FunctionProto_constructor {
FunctionProto_name : option string;
FunctionProto_input : list string;
FunctionProto_output : list string;
FunctionProto_attribute : list string;
FunctionProto_attribute_proto : list AttributeProto;
FunctionProto_node : list NodeProto;
FunctionProto_doc_string : option string;
FunctionProto_opset_import : list OperatorSetIdProto;
FunctionProto_domain : option string;
FunctionProto_overload : option string;
FunctionProto_value_info : list ValueInfoProto;
FunctionProto_metadata_props : list StringStringEntryProto;
}.

Record TrainingInfoProto := 
TrainingInfoProto_constructor {
TrainingInfoProto_initialization : option GraphProto;
TrainingInfoProto_algorithm : option GraphProto;
TrainingInfoProto_initialization_binding : list StringStringEntryProto;
TrainingInfoProto_update_binding : list StringStringEntryProto;
}.

Record ModelProto := 
ModelProto_constructor {
ModelProto_ir_version : option int64;
ModelProto_opset_import : list OperatorSetIdProto;
ModelProto_producer_name : option string;
ModelProto_producer_version : option string;
ModelProto_domain : option string;
ModelProto_model_version : option int64;
ModelProto_doc_string : option string;
ModelProto_graph : option GraphProto;
ModelProto_metadata_props : list StringStringEntryProto;
ModelProto_training_info : list TrainingInfoProto;
ModelProto_functions : list FunctionProto;
ModelProto_configuration : list DeviceConfigurationProto;
}.
