(*this file was generated automatically by ./scripts/redirect_formatter.py on 2025-10-16 05:27:21 UTC*)

(*This file was generated automatically*)

From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From CoqE2EAI Require Export float.
From CoqE2EAI Require Export int.
From CoqE2EAI Require Export bytes.


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

Inductive IntIntListEntryProto :=
| IntIntListEntryProto_constructor: 
option int64 (*key*) -> 
list int64 (*value*) -> 
IntIntListEntryProto.

Inductive dim_SimpleShardedDimProto :=
| dim_value_dim_SimpleShardedDimProto: int64 -> dim_SimpleShardedDimProto
| dim_param_dim_SimpleShardedDimProto: string -> dim_SimpleShardedDimProto
.

Inductive SimpleShardedDimProto :=
| SimpleShardedDimProto_constructor: 
option dim_SimpleShardedDimProto (**) -> 
option int64 (*num_shards*) -> 
SimpleShardedDimProto.

Inductive DeviceConfigurationProto :=
| DeviceConfigurationProto_constructor: 
option string (*name*) -> 
option int32 (*num_devices*) -> 
list string (*device*) -> 
DeviceConfigurationProto.

Inductive StringStringEntryProto :=
| StringStringEntryProto_constructor: 
option string (*key*) -> 
option string (*value*) -> 
StringStringEntryProto.

Inductive TensorAnnotation :=
| TensorAnnotation_constructor: 
option string (*tensor_name*) -> 
list StringStringEntryProto (*quant_parameter_tensor_names*) -> 
TensorAnnotation.

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

Inductive Segment_TensorProto :=
| Segment_TensorProto_constructor: 
option int64 (*begin*) -> 
option int64 (*end*) -> 
Segment_TensorProto.

Inductive DataLocation_TensorProto :=
| DEFAULT_TensorProto
| EXTERNAL_TensorProto
.

Inductive TensorProto :=
| TensorProto_constructor: 
list int64 (*dims*) -> 
option int32 (*data_type*) -> 
option Segment_TensorProto (*segment*) -> 
list float32 (*float_data*) -> 
list int32 (*int32_data*) -> 
list bytes (*string_data*) -> 
list int64 (*int64_data*) -> 
option string (*name*) -> 
option string (*doc_string*) -> 
option bytes (*raw_data*) -> 
list StringStringEntryProto (*external_data*) -> 
option DataLocation_TensorProto (*data_location*) -> 
list float64 (*double_data*) -> 
list uint64 (*uint64_data*) -> 
list StringStringEntryProto (*metadata_props*) -> 
TensorProto.

Inductive SparseTensorProto :=
| SparseTensorProto_constructor: 
option TensorProto (*values*) -> 
option TensorProto (*indices*) -> 
list int64 (*dims*) -> 
SparseTensorProto.

Inductive value_Dimension_TensorShapeProto :=
| dim_value_value_Dimension_TensorShapeProto: int64 -> value_Dimension_TensorShapeProto
| dim_param_value_Dimension_TensorShapeProto: string -> value_Dimension_TensorShapeProto
.

Inductive Dimension_TensorShapeProto :=
| Dimension_TensorShapeProto_constructor: 
option value_Dimension_TensorShapeProto (**) -> 
option string (*denotation*) -> 
Dimension_TensorShapeProto.

Inductive TensorShapeProto :=
| TensorShapeProto_constructor: 
list Dimension_TensorShapeProto (*dim*) -> 
TensorShapeProto.

Inductive Tensor_TypeProto :=
| Tensor_TypeProto_constructor: 
option int32 (*elem_type*) -> 
option TensorShapeProto (*shape*) -> 
Tensor_TypeProto.

Inductive Sequence_TypeProto :=
| Sequence_TypeProto_constructor: 
option string (*elem_type*) -> 
Sequence_TypeProto.

Inductive Map_TypeProto :=
| Map_TypeProto_constructor: 
option int32 (*key_type*) -> 
option string (*value_type*) -> 
Map_TypeProto.

Inductive Optional_TypeProto :=
| Optional_TypeProto_constructor: 
option string (*elem_type*) -> 
Optional_TypeProto.

Inductive SparseTensor_TypeProto :=
| SparseTensor_TypeProto_constructor: 
option int32 (*elem_type*) -> 
option TensorShapeProto (*shape*) -> 
SparseTensor_TypeProto.

Inductive value_TypeProto :=
| tensor_type_value_TypeProto: Tensor_TypeProto -> value_TypeProto
| sequence_type_value_TypeProto: Sequence_TypeProto -> value_TypeProto
| map_type_value_TypeProto: Map_TypeProto -> value_TypeProto
| optional_type_value_TypeProto: Optional_TypeProto -> value_TypeProto
| sparse_tensor_type_value_TypeProto: SparseTensor_TypeProto -> value_TypeProto
.

Inductive TypeProto :=
| TypeProto_constructor: 
option value_TypeProto (**) -> 
option string (*denotation*) -> 
TypeProto.

Inductive OperatorSetIdProto :=
| OperatorSetIdProto_constructor: 
option string (*domain*) -> 
option int64 (*version*) -> 
OperatorSetIdProto.

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

Inductive AttributeProto :=
| AttributeProto_constructor: 
option string (*name*) -> 
option string (*ref_attr_name*) -> 
option string (*doc_string*) -> 
option AttributeType_AttributeProto (*type*) -> 
option float32 (*f*) -> 
option int64 (*i*) -> 
option bytes (*s*) -> 
option TensorProto (*t*) -> 
option SparseTensorProto (*sparse_tensor*) -> 
option TypeProto (*tp*) -> 
list float32 (*floats*) -> 
list int64 (*ints*) -> 
list bytes (*strings*) -> 
list TensorProto (*tensors*) -> 
list SparseTensorProto (*sparse_tensors*) -> 
list TypeProto (*type_protos*) -> 
AttributeProto.

Inductive ValueInfoProto :=
| ValueInfoProto_constructor: 
option string (*name*) -> 
option TypeProto (*type*) -> 
option string (*doc_string*) -> 
list StringStringEntryProto (*metadata_props*) -> 
ValueInfoProto.

Inductive ShardedDimProto :=
| ShardedDimProto_constructor: 
option int64 (*axis*) -> 
list SimpleShardedDimProto (*simple_sharding*) -> 
ShardedDimProto.

Inductive ShardingSpecProto :=
| ShardingSpecProto_constructor: 
option string (*tensor_name*) -> 
list int64 (*device*) -> 
list IntIntListEntryProto (*index_to_device_group_map*) -> 
list ShardedDimProto (*sharded_dim*) -> 
ShardingSpecProto.

Inductive NodeDeviceConfigurationProto :=
| NodeDeviceConfigurationProto_constructor: 
option string (*configuration_id*) -> 
list ShardingSpecProto (*sharding_spec*) -> 
option int32 (*pipeline_stage*) -> 
NodeDeviceConfigurationProto.

Inductive NodeProto :=
| NodeProto_constructor: 
list string (*input*) -> 
list string (*output*) -> 
option string (*name*) -> 
option string (*op_type*) -> 
option string (*domain*) -> 
option string (*overload*) -> 
list AttributeProto (*attribute*) -> 
option string (*doc_string*) -> 
list StringStringEntryProto (*metadata_props*) -> 
list NodeDeviceConfigurationProto (*device_configurations*) -> 
NodeProto.

Inductive GraphProto :=
| GraphProto_constructor: 
list NodeProto (*node*) -> 
option string (*name*) -> 
list TensorProto (*initializer*) -> 
list SparseTensorProto (*sparse_initializer*) -> 
option string (*doc_string*) -> 
list ValueInfoProto (*input*) -> 
list ValueInfoProto (*output*) -> 
list ValueInfoProto (*value_info*) -> 
list TensorAnnotation (*quantization_annotation*) -> 
list StringStringEntryProto (*metadata_props*) -> 
GraphProto.

Inductive FunctionProto :=
| FunctionProto_constructor: 
option string (*name*) -> 
list string (*input*) -> 
list string (*output*) -> 
list string (*attribute*) -> 
list AttributeProto (*attribute_proto*) -> 
list NodeProto (*node*) -> 
option string (*doc_string*) -> 
list OperatorSetIdProto (*opset_import*) -> 
option string (*domain*) -> 
option string (*overload*) -> 
list ValueInfoProto (*value_info*) -> 
list StringStringEntryProto (*metadata_props*) -> 
FunctionProto.

Inductive TrainingInfoProto :=
| TrainingInfoProto_constructor: 
option GraphProto (*initialization*) -> 
option GraphProto (*algorithm*) -> 
list StringStringEntryProto (*initialization_binding*) -> 
list StringStringEntryProto (*update_binding*) -> 
TrainingInfoProto.

Inductive ModelProto :=
| ModelProto_constructor: 
option int64 (*ir_version*) -> 
list OperatorSetIdProto (*opset_import*) -> 
option string (*producer_name*) -> 
option string (*producer_version*) -> 
option string (*domain*) -> 
option int64 (*model_version*) -> 
option string (*doc_string*) -> 
option GraphProto (*graph*) -> 
list StringStringEntryProto (*metadata_props*) -> 
list TrainingInfoProto (*training_info*) -> 
list FunctionProto (*functions*) -> 
list DeviceConfigurationProto (*configuration*) -> 
ModelProto.
