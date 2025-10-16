(*this file was generated automatically by ./scripts/redirect_formatter.py on 2025-10-16 05:27:21 UTC*)


From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export grab.
From CoqE2EAI Require Export string_to_number.
From CoqE2EAI Require Export model.
From CoqE2EAI Require Export float.
From CoqE2EAI Require Export int.
From CoqE2EAI Require Export bytes.
From CoqE2EAI Require Export function_converter.


Definition convert_Version (t: tree) : error_option Version :=
match getFirstChildValue t with
| Some e => match string_of_list_ascii e with
| "_START_VERSION" => Success _START_VERSION
| "IR_VERSION_2017_10_10" => Success IR_VERSION_2017_10_10
| "IR_VERSION_2017_10_30" => Success IR_VERSION_2017_10_30
| "IR_VERSION_2017_11_3" => Success IR_VERSION_2017_11_3
| "IR_VERSION_2019_1_22" => Success IR_VERSION_2019_1_22
| "IR_VERSION_2019_3_18" => Success IR_VERSION_2019_3_18
| "IR_VERSION_2019_9_19" => Success IR_VERSION_2019_9_19
| "IR_VERSION_2020_5_8" => Success IR_VERSION_2020_5_8
| "IR_VERSION_2021_7_30" => Success IR_VERSION_2021_7_30
| "IR_VERSION_2023_5_5" => Success IR_VERSION_2023_5_5
| "IR_VERSION_2024_3_25" => Success IR_VERSION_2024_3_25
| "IR_VERSION" => Success IR_VERSION
| _ => Error "Enum value is not an enum of specified type"
end
| None => Error "No enum value found"
end
.
Definition convert_IntIntListEntryProto (t: tree) : error_option IntIntListEntryProto :=
let key_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["key"]) t) "failed to convert key to correct type (int64)" in
match key_option with
| Success key =>
let value_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "value" t)) "failed to convert value to correct type (int64)" in
match value_option with
| Success value =>
Success (IntIntListEntryProto_constructor
key
value
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_dim_SimpleShardedDimProto (t: tree) : error_option dim_SimpleShardedDimProto :=
match (grab_value (map list_ascii_of_string ["dim_value"]) t) with
| Some la => match int64_of_string la with
| Some found => Success (dim_value_dim_SimpleShardedDimProto found)
| None => Error "failed to convert dim_value to correct type (int64)"
end
| None =>
match (grab_value (map list_ascii_of_string ["dim_param"]) t) with
| Some la => match (fun x => Some (string_of_list_ascii x)) la with
| Some found => Success (dim_param_dim_SimpleShardedDimProto found)
| None => Error "failed to convert dim_param to correct type (string)"
end
| None =>
Error "not a single one_of element found"
end
end
.
Definition convert_SimpleShardedDimProto (t: tree) : error_option SimpleShardedDimProto :=
let e_option := error_option_option_handler convert_dim_SimpleShardedDimProto (grab (map list_ascii_of_string []) t) in
match e_option with
| Success e =>
let num_shards_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["num_shards"]) t) "failed to convert num_shards to correct type (int64)" in
match num_shards_option with
| Success num_shards =>
Success (SimpleShardedDimProto_constructor
e
num_shards
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_DeviceConfigurationProto (t: tree) : error_option DeviceConfigurationProto :=
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let num_devices_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["num_devices"]) t) "failed to convert num_devices to correct type (int32)" in
match num_devices_option with
| Success num_devices =>
let device_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "device" t)) "failed to convert device to correct type (string)" in
match device_option with
| Success device =>
Success (DeviceConfigurationProto_constructor
name
num_devices
device
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_StringStringEntryProto (t: tree) : error_option StringStringEntryProto :=
let key_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["key"]) t) "failed to convert key to correct type (string)" in
match key_option with
| Success key =>
let value_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["value"]) t) "failed to convert value to correct type (string)" in
match value_option with
| Success value =>
Success (StringStringEntryProto_constructor
key
value
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_TensorAnnotation (t: tree) : error_option TensorAnnotation :=
let tensor_name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["tensor_name"]) t) "failed to convert tensor_name to correct type (string)" in
match tensor_name_option with
| Success tensor_name =>
let quant_parameter_tensor_names_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "quant_parameter_tensor_names" t) in
match quant_parameter_tensor_names_option with
| Success quant_parameter_tensor_names =>
Success (TensorAnnotation_constructor
tensor_name
quant_parameter_tensor_names
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_DataType_TensorProto (t: tree) : error_option DataType_TensorProto :=
match getFirstChildValue t with
| Some e => match string_of_list_ascii e with
| "UNDEFINED" => Success UNDEFINED_TensorProto
| "FLOAT" => Success FLOAT_TensorProto
| "UINT8" => Success UINT8_TensorProto
| "INT8" => Success INT8_TensorProto
| "UINT16" => Success UINT16_TensorProto
| "INT16" => Success INT16_TensorProto
| "INT32" => Success INT32_TensorProto
| "INT64" => Success INT64_TensorProto
| "STRING" => Success STRING_TensorProto
| "BOOL" => Success BOOL_TensorProto
| "FLOAT16" => Success FLOAT16_TensorProto
| "DOUBLE" => Success DOUBLE_TensorProto
| "UINT32" => Success UINT32_TensorProto
| "UINT64" => Success UINT64_TensorProto
| "COMPLEX64" => Success COMPLEX64_TensorProto
| "COMPLEX128" => Success COMPLEX128_TensorProto
| "BFLOAT16" => Success BFLOAT16_TensorProto
| "FLOAT8E4M3FN" => Success FLOAT8E4M3FN_TensorProto
| "FLOAT8E4M3FNUZ" => Success FLOAT8E4M3FNUZ_TensorProto
| "FLOAT8E5M2" => Success FLOAT8E5M2_TensorProto
| "FLOAT8E5M2FNUZ" => Success FLOAT8E5M2FNUZ_TensorProto
| "UINT4" => Success UINT4_TensorProto
| "INT4" => Success INT4_TensorProto
| "FLOAT4E2M1" => Success FLOAT4E2M1_TensorProto
| _ => Error "Enum value is not an enum of specified type"
end
| None => Error "No enum value found"
end
.
Definition convert_Segment_TensorProto (t: tree) : error_option Segment_TensorProto :=
let begin_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["begin"]) t) "failed to convert begin to correct type (int64)" in
match begin_option with
| Success begin =>
let _end_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["end"]) t) "failed to convert _end to correct type (int64)" in
match _end_option with
| Success _end =>
Success (Segment_TensorProto_constructor
begin
_end
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_DataLocation_TensorProto (t: tree) : error_option DataLocation_TensorProto :=
match getFirstChildValue t with
| Some e => match string_of_list_ascii e with
| "DEFAULT" => Success DEFAULT_TensorProto
| "EXTERNAL" => Success EXTERNAL_TensorProto
| _ => Error "Enum value is not an enum of specified type"
end
| None => Error "No enum value found"
end
.
Definition convert_TensorProto (t: tree) : error_option TensorProto :=
let dims_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "dims" t)) "failed to convert dims to correct type (int64)" in
match dims_option with
| Success dims =>
let data_type_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["data_type"]) t) "failed to convert data_type to correct type (int32)" in
match data_type_option with
| Success data_type =>
let segment_option := error_option_option_handler convert_Segment_TensorProto (grab (map list_ascii_of_string ["segment"]) t) in
match segment_option with
| Success segment =>
let float_data_option := option_list_handler float32_of_string (map getFirstChildValue (grabAll [] "float_data" t)) "failed to convert float_data to correct type (float)" in
match float_data_option with
| Success float_data =>
let int32_data_option := option_list_handler int32_of_string (map getFirstChildValue (grabAll [] "int32_data" t)) "failed to convert int32_data to correct type (int32)" in
match int32_data_option with
| Success int32_data =>
let string_data_option := option_list_handler bytes_of_string (map getFirstChildValue (grabAll [] "string_data" t)) "failed to convert string_data to correct type (bytes)" in
match string_data_option with
| Success string_data =>
let int64_data_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "int64_data" t)) "failed to convert int64_data to correct type (int64)" in
match int64_data_option with
| Success int64_data =>
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let raw_data_option := option_option_handler bytes_of_string (grab_value (map list_ascii_of_string ["raw_data"]) t) "failed to convert raw_data to correct type (bytes)" in
match raw_data_option with
| Success raw_data =>
let external_data_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "external_data" t) in
match external_data_option with
| Success external_data =>
let data_location_option := error_option_option_handler convert_DataLocation_TensorProto (grab (map list_ascii_of_string ["data_location"]) t) in
match data_location_option with
| Success data_location =>
let double_data_option := option_list_handler float64_of_string (map getFirstChildValue (grabAll [] "double_data" t)) "failed to convert double_data to correct type (double)" in
match double_data_option with
| Success double_data =>
let uint64_data_option := option_list_handler uint64_of_string (map getFirstChildValue (grabAll [] "uint64_data" t)) "failed to convert uint64_data to correct type (uint64)" in
match uint64_data_option with
| Success uint64_data =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
Success (TensorProto_constructor
dims
data_type
segment
float_data
int32_data
string_data
int64_data
name
doc_string
raw_data
external_data
data_location
double_data
uint64_data
metadata_props
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_SparseTensorProto (t: tree) : error_option SparseTensorProto :=
let values_option := error_option_option_handler convert_TensorProto (grab (map list_ascii_of_string ["values"]) t) in
match values_option with
| Success values =>
let indices_option := error_option_option_handler convert_TensorProto (grab (map list_ascii_of_string ["indices"]) t) in
match indices_option with
| Success indices =>
let dims_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "dims" t)) "failed to convert dims to correct type (int64)" in
match dims_option with
| Success dims =>
Success (SparseTensorProto_constructor
values
indices
dims
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_value_Dimension_TensorShapeProto (t: tree) : error_option value_Dimension_TensorShapeProto :=
match (grab_value (map list_ascii_of_string ["dim_value"]) t) with
| Some la => match int64_of_string la with
| Some found => Success (dim_value_value_Dimension_TensorShapeProto found)
| None => Error "failed to convert dim_value to correct type (int64)"
end
| None =>
match (grab_value (map list_ascii_of_string ["dim_param"]) t) with
| Some la => match (fun x => Some (string_of_list_ascii x)) la with
| Some found => Success (dim_param_value_Dimension_TensorShapeProto found)
| None => Error "failed to convert dim_param to correct type (string)"
end
| None =>
Error "not a single one_of element found"
end
end
.
Definition convert_Dimension_TensorShapeProto (t: tree) : error_option Dimension_TensorShapeProto :=
let e_option := error_option_option_handler convert_value_Dimension_TensorShapeProto (grab (map list_ascii_of_string []) t) in
match e_option with
| Success e =>
let denotation_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["denotation"]) t) "failed to convert denotation to correct type (string)" in
match denotation_option with
| Success denotation =>
Success (Dimension_TensorShapeProto_constructor
e
denotation
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_TensorShapeProto (t: tree) : error_option TensorShapeProto :=
let dim_option := error_option_list_handler convert_Dimension_TensorShapeProto (grabAll [] "dim" t) in
match dim_option with
| Success dim =>
Success (TensorShapeProto_constructor
dim
)
| Error e => Error e
end
.
Definition convert_Tensor_TypeProto (t: tree) : error_option Tensor_TypeProto :=
let elem_type_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["elem_type"]) t) "failed to convert elem_type to correct type (int32)" in
match elem_type_option with
| Success elem_type =>
let shape_option := error_option_option_handler convert_TensorShapeProto (grab (map list_ascii_of_string ["shape"]) t) in
match shape_option with
| Success shape =>
Success (Tensor_TypeProto_constructor
elem_type
shape
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_Sequence_TypeProto (t: tree) : error_option Sequence_TypeProto :=
let elem_type_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["elem_type"]) t) "failed to convert elem_type to correct type (string)" in
match elem_type_option with
| Success elem_type =>
Success (Sequence_TypeProto_constructor
elem_type
)
| Error e => Error e
end
.
Definition convert_Map_TypeProto (t: tree) : error_option Map_TypeProto :=
let key_type_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["key_type"]) t) "failed to convert key_type to correct type (int32)" in
match key_type_option with
| Success key_type =>
let value_type_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["value_type"]) t) "failed to convert value_type to correct type (string)" in
match value_type_option with
| Success value_type =>
Success (Map_TypeProto_constructor
key_type
value_type
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_Optional_TypeProto (t: tree) : error_option Optional_TypeProto :=
let elem_type_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["elem_type"]) t) "failed to convert elem_type to correct type (string)" in
match elem_type_option with
| Success elem_type =>
Success (Optional_TypeProto_constructor
elem_type
)
| Error e => Error e
end
.
Definition convert_SparseTensor_TypeProto (t: tree) : error_option SparseTensor_TypeProto :=
let elem_type_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["elem_type"]) t) "failed to convert elem_type to correct type (int32)" in
match elem_type_option with
| Success elem_type =>
let shape_option := error_option_option_handler convert_TensorShapeProto (grab (map list_ascii_of_string ["shape"]) t) in
match shape_option with
| Success shape =>
Success (SparseTensor_TypeProto_constructor
elem_type
shape
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_value_TypeProto (t: tree) : error_option value_TypeProto :=
match (grab (map list_ascii_of_string ["tensor_type"]) t) with
| Some la => match convert_Tensor_TypeProto la with
| Success found => Success (tensor_type_value_TypeProto found)
| Error e => Error e
end
| None =>
match (grab (map list_ascii_of_string ["sequence_type"]) t) with
| Some la => match convert_Sequence_TypeProto la with
| Success found => Success (sequence_type_value_TypeProto found)
| Error e => Error e
end
| None =>
match (grab (map list_ascii_of_string ["map_type"]) t) with
| Some la => match convert_Map_TypeProto la with
| Success found => Success (map_type_value_TypeProto found)
| Error e => Error e
end
| None =>
match (grab (map list_ascii_of_string ["optional_type"]) t) with
| Some la => match convert_Optional_TypeProto la with
| Success found => Success (optional_type_value_TypeProto found)
| Error e => Error e
end
| None =>
match (grab (map list_ascii_of_string ["sparse_tensor_type"]) t) with
| Some la => match convert_SparseTensor_TypeProto la with
| Success found => Success (sparse_tensor_type_value_TypeProto found)
| Error e => Error e
end
| None =>
Error "not a single one_of element found"
end
end
end
end
end
.
Definition convert_TypeProto (t: tree) : error_option TypeProto :=
let e_option := error_option_option_handler convert_value_TypeProto (grab (map list_ascii_of_string []) t) in
match e_option with
| Success e =>
let denotation_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["denotation"]) t) "failed to convert denotation to correct type (string)" in
match denotation_option with
| Success denotation =>
Success (TypeProto_constructor
e
denotation
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_OperatorSetIdProto (t: tree) : error_option OperatorSetIdProto :=
let domain_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["domain"]) t) "failed to convert domain to correct type (string)" in
match domain_option with
| Success domain =>
let version_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["version"]) t) "failed to convert version to correct type (int64)" in
match version_option with
| Success version =>
Success (OperatorSetIdProto_constructor
domain
version
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_OperatorStatus (t: tree) : error_option OperatorStatus :=
match getFirstChildValue t with
| Some e => match string_of_list_ascii e with
| "EXPERIMENTAL" => Success EXPERIMENTAL
| "STABLE" => Success STABLE
| _ => Error "Enum value is not an enum of specified type"
end
| None => Error "No enum value found"
end
.
Definition convert_AttributeType_AttributeProto (t: tree) : error_option AttributeType_AttributeProto :=
match getFirstChildValue t with
| Some e => match string_of_list_ascii e with
| "UNDEFINED" => Success UNDEFINED_AttributeProto
| "FLOAT" => Success FLOAT_AttributeProto
| "INT" => Success INT_AttributeProto
| "STRING" => Success STRING_AttributeProto
| "TENSOR" => Success TENSOR_AttributeProto
| "GRAPH" => Success GRAPH_AttributeProto
| "SPARSE_TENSOR" => Success SPARSE_TENSOR_AttributeProto
| "TYPE_PROTO" => Success TYPE_PROTO_AttributeProto
| "FLOATS" => Success FLOATS_AttributeProto
| "INTS" => Success INTS_AttributeProto
| "STRINGS" => Success STRINGS_AttributeProto
| "TENSORS" => Success TENSORS_AttributeProto
| "GRAPHS" => Success GRAPHS_AttributeProto
| "SPARSE_TENSORS" => Success SPARSE_TENSORS_AttributeProto
| "TYPE_PROTOS" => Success TYPE_PROTOS_AttributeProto
| _ => Error "Enum value is not an enum of specified type"
end
| None => Error "No enum value found"
end
.
Definition convert_AttributeProto (t: tree) : error_option AttributeProto :=
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let ref_attr_name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["ref_attr_name"]) t) "failed to convert ref_attr_name to correct type (string)" in
match ref_attr_name_option with
| Success ref_attr_name =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let type_option := error_option_option_handler convert_AttributeType_AttributeProto (grab (map list_ascii_of_string ["type"]) t) in
match type_option with
| Success type =>
let f_option := option_option_handler float32_of_string (grab_value (map list_ascii_of_string ["f"]) t) "failed to convert f to correct type (float)" in
match f_option with
| Success f =>
let i_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["i"]) t) "failed to convert i to correct type (int64)" in
match i_option with
| Success i =>
let s_option := option_option_handler bytes_of_string (grab_value (map list_ascii_of_string ["s"]) t) "failed to convert s to correct type (bytes)" in
match s_option with
| Success s =>
let _t_option := error_option_option_handler convert_TensorProto (grab (map list_ascii_of_string ["t"]) t) in
match _t_option with
| Success _t =>
let sparse_tensor_option := error_option_option_handler convert_SparseTensorProto (grab (map list_ascii_of_string ["sparse_tensor"]) t) in
match sparse_tensor_option with
| Success sparse_tensor =>
let tp_option := error_option_option_handler convert_TypeProto (grab (map list_ascii_of_string ["tp"]) t) in
match tp_option with
| Success tp =>
let floats_option := option_list_handler float32_of_string (map getFirstChildValue (grabAll [] "floats" t)) "failed to convert floats to correct type (float)" in
match floats_option with
| Success floats =>
let ints_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "ints" t)) "failed to convert ints to correct type (int64)" in
match ints_option with
| Success ints =>
let strings_option := option_list_handler bytes_of_string (map getFirstChildValue (grabAll [] "strings" t)) "failed to convert strings to correct type (bytes)" in
match strings_option with
| Success strings =>
let tensors_option := error_option_list_handler convert_TensorProto (grabAll [] "tensors" t) in
match tensors_option with
| Success tensors =>
let sparse_tensors_option := error_option_list_handler convert_SparseTensorProto (grabAll [] "sparse_tensors" t) in
match sparse_tensors_option with
| Success sparse_tensors =>
let type_protos_option := error_option_list_handler convert_TypeProto (grabAll [] "type_protos" t) in
match type_protos_option with
| Success type_protos =>
Success (AttributeProto_constructor
name
ref_attr_name
doc_string
type
f
i
s
_t
sparse_tensor
tp
floats
ints
strings
tensors
sparse_tensors
type_protos
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_ValueInfoProto (t: tree) : error_option ValueInfoProto :=
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let type_option := error_option_option_handler convert_TypeProto (grab (map list_ascii_of_string ["type"]) t) in
match type_option with
| Success type =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
Success (ValueInfoProto_constructor
name
type
doc_string
metadata_props
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_ShardedDimProto (t: tree) : error_option ShardedDimProto :=
let axis_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["axis"]) t) "failed to convert axis to correct type (int64)" in
match axis_option with
| Success axis =>
let simple_sharding_option := error_option_list_handler convert_SimpleShardedDimProto (grabAll [] "simple_sharding" t) in
match simple_sharding_option with
| Success simple_sharding =>
Success (ShardedDimProto_constructor
axis
simple_sharding
)
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_ShardingSpecProto (t: tree) : error_option ShardingSpecProto :=
let tensor_name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["tensor_name"]) t) "failed to convert tensor_name to correct type (string)" in
match tensor_name_option with
| Success tensor_name =>
let device_option := option_list_handler int64_of_string (map getFirstChildValue (grabAll [] "device" t)) "failed to convert device to correct type (int64)" in
match device_option with
| Success device =>
let index_to_device_group_map_option := error_option_list_handler convert_IntIntListEntryProto (grabAll [] "index_to_device_group_map" t) in
match index_to_device_group_map_option with
| Success index_to_device_group_map =>
let sharded_dim_option := error_option_list_handler convert_ShardedDimProto (grabAll [] "sharded_dim" t) in
match sharded_dim_option with
| Success sharded_dim =>
Success (ShardingSpecProto_constructor
tensor_name
device
index_to_device_group_map
sharded_dim
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_NodeDeviceConfigurationProto (t: tree) : error_option NodeDeviceConfigurationProto :=
let configuration_id_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["configuration_id"]) t) "failed to convert configuration_id to correct type (string)" in
match configuration_id_option with
| Success configuration_id =>
let sharding_spec_option := error_option_list_handler convert_ShardingSpecProto (grabAll [] "sharding_spec" t) in
match sharding_spec_option with
| Success sharding_spec =>
let pipeline_stage_option := option_option_handler int32_of_string (grab_value (map list_ascii_of_string ["pipeline_stage"]) t) "failed to convert pipeline_stage to correct type (int32)" in
match pipeline_stage_option with
| Success pipeline_stage =>
Success (NodeDeviceConfigurationProto_constructor
configuration_id
sharding_spec
pipeline_stage
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_NodeProto (t: tree) : error_option NodeProto :=
let input_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "input" t)) "failed to convert input to correct type (string)" in
match input_option with
| Success input =>
let output_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "output" t)) "failed to convert output to correct type (string)" in
match output_option with
| Success output =>
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let op_type_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["op_type"]) t) "failed to convert op_type to correct type (string)" in
match op_type_option with
| Success op_type =>
let domain_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["domain"]) t) "failed to convert domain to correct type (string)" in
match domain_option with
| Success domain =>
let overload_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["overload"]) t) "failed to convert overload to correct type (string)" in
match overload_option with
| Success overload =>
let attribute_option := error_option_list_handler convert_AttributeProto (grabAll [] "attribute" t) in
match attribute_option with
| Success attribute =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
let device_configurations_option := error_option_list_handler convert_NodeDeviceConfigurationProto (grabAll [] "device_configurations" t) in
match device_configurations_option with
| Success device_configurations =>
Success (NodeProto_constructor
input
output
name
op_type
domain
overload
attribute
doc_string
metadata_props
device_configurations
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_GraphProto (t: tree) : error_option GraphProto :=
let node_option := error_option_list_handler convert_NodeProto (grabAll [] "node" t) in
match node_option with
| Success node =>
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let initializer_option := error_option_list_handler convert_TensorProto (grabAll [] "initializer" t) in
match initializer_option with
| Success initializer =>
let sparse_initializer_option := error_option_list_handler convert_SparseTensorProto (grabAll [] "sparse_initializer" t) in
match sparse_initializer_option with
| Success sparse_initializer =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let input_option := error_option_list_handler convert_ValueInfoProto (grabAll [] "input" t) in
match input_option with
| Success input =>
let output_option := error_option_list_handler convert_ValueInfoProto (grabAll [] "output" t) in
match output_option with
| Success output =>
let value_info_option := error_option_list_handler convert_ValueInfoProto (grabAll [] "value_info" t) in
match value_info_option with
| Success value_info =>
let quantization_annotation_option := error_option_list_handler convert_TensorAnnotation (grabAll [] "quantization_annotation" t) in
match quantization_annotation_option with
| Success quantization_annotation =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
Success (GraphProto_constructor
node
name
initializer
sparse_initializer
doc_string
input
output
value_info
quantization_annotation
metadata_props
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_FunctionProto (t: tree) : error_option FunctionProto :=
let name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["name"]) t) "failed to convert name to correct type (string)" in
match name_option with
| Success name =>
let input_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "input" t)) "failed to convert input to correct type (string)" in
match input_option with
| Success input =>
let output_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "output" t)) "failed to convert output to correct type (string)" in
match output_option with
| Success output =>
let attribute_option := option_list_handler (fun x => Some (string_of_list_ascii x)) (map getFirstChildValue (grabAll [] "attribute" t)) "failed to convert attribute to correct type (string)" in
match attribute_option with
| Success attribute =>
let attribute_proto_option := error_option_list_handler convert_AttributeProto (grabAll [] "attribute_proto" t) in
match attribute_proto_option with
| Success attribute_proto =>
let node_option := error_option_list_handler convert_NodeProto (grabAll [] "node" t) in
match node_option with
| Success node =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let opset_import_option := error_option_list_handler convert_OperatorSetIdProto (grabAll [] "opset_import" t) in
match opset_import_option with
| Success opset_import =>
let domain_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["domain"]) t) "failed to convert domain to correct type (string)" in
match domain_option with
| Success domain =>
let overload_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["overload"]) t) "failed to convert overload to correct type (string)" in
match overload_option with
| Success overload =>
let value_info_option := error_option_list_handler convert_ValueInfoProto (grabAll [] "value_info" t) in
match value_info_option with
| Success value_info =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
Success (FunctionProto_constructor
name
input
output
attribute
attribute_proto
node
doc_string
opset_import
domain
overload
value_info
metadata_props
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_TrainingInfoProto (t: tree) : error_option TrainingInfoProto :=
let initialization_option := error_option_option_handler convert_GraphProto (grab (map list_ascii_of_string ["initialization"]) t) in
match initialization_option with
| Success initialization =>
let algorithm_option := error_option_option_handler convert_GraphProto (grab (map list_ascii_of_string ["algorithm"]) t) in
match algorithm_option with
| Success algorithm =>
let initialization_binding_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "initialization_binding" t) in
match initialization_binding_option with
| Success initialization_binding =>
let update_binding_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "update_binding" t) in
match update_binding_option with
| Success update_binding =>
Success (TrainingInfoProto_constructor
initialization
algorithm
initialization_binding
update_binding
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
Definition convert_ModelProto (t: tree) : error_option ModelProto :=
let ir_version_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["ir_version"]) t) "failed to convert ir_version to correct type (int64)" in
match ir_version_option with
| Success ir_version =>
let opset_import_option := error_option_list_handler convert_OperatorSetIdProto (grabAll [] "opset_import" t) in
match opset_import_option with
| Success opset_import =>
let producer_name_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["producer_name"]) t) "failed to convert producer_name to correct type (string)" in
match producer_name_option with
| Success producer_name =>
let producer_version_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["producer_version"]) t) "failed to convert producer_version to correct type (string)" in
match producer_version_option with
| Success producer_version =>
let domain_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["domain"]) t) "failed to convert domain to correct type (string)" in
match domain_option with
| Success domain =>
let model_version_option := option_option_handler int64_of_string (grab_value (map list_ascii_of_string ["model_version"]) t) "failed to convert model_version to correct type (int64)" in
match model_version_option with
| Success model_version =>
let doc_string_option := option_option_handler (fun x => Some (string_of_list_ascii x)) (grab_value (map list_ascii_of_string ["doc_string"]) t) "failed to convert doc_string to correct type (string)" in
match doc_string_option with
| Success doc_string =>
let graph_option := error_option_option_handler convert_GraphProto (grab (map list_ascii_of_string ["graph"]) t) in
match graph_option with
| Success graph =>
let metadata_props_option := error_option_list_handler convert_StringStringEntryProto (grabAll [] "metadata_props" t) in
match metadata_props_option with
| Success metadata_props =>
let training_info_option := error_option_list_handler convert_TrainingInfoProto (grabAll [] "training_info" t) in
match training_info_option with
| Success training_info =>
let functions_option := error_option_list_handler convert_FunctionProto (grabAll [] "functions" t) in
match functions_option with
| Success functions =>
let configuration_option := error_option_list_handler convert_DeviceConfigurationProto (grabAll [] "configuration" t) in
match configuration_option with
| Success configuration =>
Success (ModelProto_constructor
ir_version
opset_import
producer_name
producer_version
domain
model_version
doc_string
graph
metadata_props
training_info
functions
configuration
)
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
| Error e => Error e
end
.
