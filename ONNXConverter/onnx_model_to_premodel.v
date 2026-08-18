From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.

From ONNXFormalization.External Require Export grab.
From ONNXFormalization.External Require Export convert_matrix.
From ONNXFormalization.External Require Export intermediate_representation.

From ONNXFormalization.ONNXConverter Require Export model.
From ONNXFormalization.ONNXConverter Require Export convertion_functions.
From ONNXFormalization.ONNXConverter Require Export bytes_converter.


(*container type for nodes, tensors, inputs and outputs*)
Inductive vertex :=
| node: NodeProto -> vertex
| tensor: TensorProto -> vertex
| input: ValueInfoProto -> vertex
| output: ValueInfoProto -> vertex.

Open Scope string_scope.

(*converts a dimension inside a Dimension_TensorShapeProto to int64*)
Definition Dimension_TensorShapeProto_to_int64 (d: Dimension_TensorShapeProto) : error_option int64 :=
  match d with
  | Dimension_TensorShapeProto_constructor value_Dimension_option _ => match value_Dimension_option with
    | Some value_Dimension => match value_Dimension with
      | dim_value_value_Dimension_TensorShapeProto z => Success z
      | dim_param_value_Dimension_TensorShapeProto _ => Error "dim_param not supported"
    end
    | None => Error "value_Dimension must be given"
    end
  end.

(*determines wether an int64 is not one*)
Definition not_one (i: int64) : bool := 
  match Z_of_int64 i with
  | 1%Z => false
  | _ => true
  end.

(*
Converts a ValueInfoProto (used for in- ad output vertices) into a NNPremodel node (NNPremodel_Output).
It works only for scalars (gets converted to vector with shape 1) and vectors,
because NNPremodel_Output only supports vectors.
Inside the TypeProto of the ValueInfoProto, only the tensor_type is supported.
*)
Definition convert_ValueInfoProto_to_NNPremodel_Output (v: ValueInfoProto) : error_option NNPremodel :=
  match v with
  | ValueInfoProto_constructor name_option type_option _ _ => match type_option with
    | Some type => match name_option with
      | Some name => match type with
        | TypeProto_constructor value_option _ => match value_option with
          | Some value1 => match value1 with
            | tensor_type_value_TypeProto tensor_typeproto => match tensor_typeproto with
              | Tensor_TypeProto_constructor _ shape_option => match shape_option with
                | Some shape => match shape with
                  | TensorShapeProto_constructor l =>
                    let unfiltered_option := list_error_option_to_error_option_list (map Dimension_TensorShapeProto_to_int64 l) in
                    match unfiltered_option with
                    | Success unfiltered => let filtered := Lists.List.filter not_one unfiltered in
                      match filtered with
                      | [] => (*output dim is 1*) Success (NNPremodel_Output name 1)
                      | h::[] => (*output dim is h*) match (Z_of_int64 h) with
                        | Z0 => Error "dim cannot be 0"
                        | Zpos p => Success (NNPremodel_Output name (Pos.to_nat p))
                        | Zneg _ => Error "dim cannot be negative"
                        end
                      | _ => (*output dim is unspecified*) Error "more than one output dimension other than 1 found"
                      end
                    | Error e => Error e
                    end
                  end
                | None => Error "no shape found in tensor"
                end
              end
            | _ => Error ("value type not supported (currently only tensor_type is supported) (in " ++ name ++ ")")
            end
          | None => Error "no value found in typeproto"
          end
        end
      | None => Error "no name found in valueInfo"
      end
    | None => Error "no type found in valueInfo"
    end
  end.

(*determines wether a list is empty*)
Definition emptyList {T: Type} (l: list T) : bool := Nat.eqb (length l) 0.

(*determines wether an option is None*)
Definition emptyOption {T: Type} (o: option T) : bool := match o with | Some _ => false | None => true end.

(*
Returns NNPremodel_initializer_vector or NNPremodel_initializer_matrix, depending on the dims list.
The data must be already in string form.
Uses get_value_vector_list_optionZero and get_value_matrix_list_optionZero from existing converter.
*)
Definition convert_data_to_NNPremodel (name: string) (dims: list int64) (data: list string) : error_option NNPremodel :=
  match dims with
  | [] => Error "Scalar values not defined in output model"
  | dim_int::[] =>
    let function := get_value_vector_list_optionZero data in
    match Z_of_int64 dim_int with
    | Z0 => Error "Dim cannot be 0"
    | Zpos p => Success (NNPremodel_initializer_vector name (N.to_nat (Npos p)) function)
    | Zneg _ => Error "Dim cannot be negative"
    end
  | dim1_int::dim2_int::[] =>
    match Z_of_int64 dim1_int with
    | Z0 => Error "Dim1 cannot be 0"
    | Zpos p1 => match Z_of_int64 dim2_int with
      | Z0 => Error "Dim2 cannot be 0"
      | Zpos p2 => let function := get_value_matrix_list_optionZero (N.to_nat (Npos p2)) data in
        Success (NNPremodel_initializer_matrix name (N.to_nat (Npos p1)) (N.to_nat (Npos p2)) function)
      | Zneg _ => Error "Dim2 cannot be negative"
      end
    | Zneg _ => Error "Dim1 cannot be negative"
    end
  | _ => Error "Tensor values greater than matrices not defined in output model"
  end.

(*
Converts a TensorProto into a NNPremodel_initializer_vector or NNPremodel_initializer_matrix,
using the function defined above.
It works if the TensorProto's type is either float32, int32 or int64.
It checks if exactly one _data list is non-empty.
This can be the float_data, int32_data or int64_data list is filled, depending on the datatype,
or the raw_data list, for all datatypes.
Then, the data gets converted to string.
In the end, the function convert_data_to_NNPremodel defined above generated the output.
*)
Definition convert_TensorProto_to_NNPremodel (t: TensorProto) : error_option NNPremodel :=
  match t with
  | TensorProto_constructor dims type_option _ float32 int32 _ int64 name_option _ raw_data _ _ float64 uint64 _ =>
    match name_option with
    | Some name =>
      match type_option with
      | Some type => match Z_of_int32 type with
        | 1%Z => (*float*)
          match emptyList float32 with
          | false => match emptyList uint64 && emptyList float64 && emptyOption raw_data && emptyList int64 && emptyList int32 with
            | true => convert_data_to_NNPremodel name dims (map string_of_float32 float32)
            | false => Error "more than one '_data' field filled in Tensor"
            end
          | true => match raw_data with
            | Some raw_data' => match emptyList uint64 && emptyList float64 && emptyList int64 && emptyList int32 && emptyList float32 with
              | true => match float32_string_of_bytes raw_data' with
                | Success data => convert_data_to_NNPremodel name dims data
                | Error e => Error e
                end
              | false => Error "more than one '_data' field filled in Tensor"
              end
            | None => Error "No matching datatype given in Tensor"
            end
          end
        | 6%Z => (*int32*)
          match emptyList int32 with
          | false => match emptyList uint64 && emptyList float64 && emptyOption raw_data && emptyList int64 && emptyList float32 with
            | true => convert_data_to_NNPremodel name dims (map string_of_int32 int32)
            | false => Error "more than one '_data' field filled in Tensor"
            end
          | true => match raw_data with
            | Some raw_data' => match emptyList uint64 && emptyList float64 && emptyList int64 && emptyList int32 && emptyList float32 with
              | true => match int32_string_of_bytes raw_data' with
                | Success data => convert_data_to_NNPremodel name dims data
                | Error e => Error e
                end
              | false => Error "more than one '_data' field filled in Tensor"
              end
            | None => Error "No matching datatype given in Tensor"
            end
          end
        | 7%Z => (*int64*)
          match emptyList int64 with
          | false => match emptyList uint64 && emptyList float64 && emptyOption raw_data && emptyList int32 && emptyList float32 with
            | true => convert_data_to_NNPremodel name dims (map string_of_int64 int64)
            | false => Error "more than one '_data' field filled in Tensor"
            end
          | true => match raw_data with
            | Some raw_data' => match emptyList uint64 && emptyList float64 && emptyList int64 && emptyList int32 && emptyList float32 with
              | true => match int64_string_of_bytes raw_data' with
                | Success data => convert_data_to_NNPremodel name dims data
                | Error e => Error e
                end
              | false => Error "more than one '_data' field filled in Tensor"
              end
            | None => Error "No matching datatype given in Tensor"
            end
          end
        | 9%Z => (*bool*)
          Error "bool is not supported in verification model"
        | _ => Error "Found unsupported datatype in Tensor"
        end
      | None => Error "Field data_type in TensorProto must be given"
      end
    | None => Error "Field name in TensorProto must be given"
    end
  end.

(*returns a NNPremodel_ReLu if both input lists have exactly one input*)
Definition convert_NodeProto_Relu_to_NNPremodel (outputs inputs: list string) : error_option NNPremodel :=
  match outputs with
  | out::[] => match inputs with
    | inp::[] => Success (NNPremodel_ReLu inp out) 
    | _ => Error "Relu node must have exaclty one input"
    end
  | _ => Error "Relu node must have exaclty one output"
  end.

(*determines wether an attribute is named <name>*)
Definition attribute_has_name (name: string) (attribute: AttributeProto) : bool :=
  match attribute with
  | AttributeProto_constructor name_option _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    match name_option with
    | Some name' => String.eqb name' name
    | None => false
    end
  end.

(*
Searches the <attributes> list for an attribute named <name>.
If found, it checks if it has a float32 value, and returns it if so.
*)
Definition get_float_attribute (attributes: list AttributeProto) (name: string) : error_option float32 :=
  match List.filter (attribute_has_name name) attributes with
  | [] => Error ("not a single attribute with necessery name <" ++ name ++ "> found")
  | found::[] => match found with
    | AttributeProto_constructor _ _ _ _ float_option _ _ _ _ _ _ _ _ _ _ _ =>
      match float_option with
      | Some float => Success float
      | None => Error "found attribute has no float given"
      end
    end
  | _ => Error ("more than one attributes with necessery name <" ++ name ++ "> found")
  end.

(*
Searches the <attributes> list for an attribute named <name>.
If found, it checks if it has a int64 value, and returns it if so.
*)
Definition get_int_attribute (attributes: list AttributeProto) (name: string) : error_option int64 :=
  match List.filter (attribute_has_name name) attributes with
  | [] => Error ("not a single attribute with necessery name <" ++ name ++ "> found")
  | found::[] => match found with
    | AttributeProto_constructor _ _ _ _ _ int_option _ _ _ _ _ _ _ _ _ _=>
      match int_option with
      | Some int => Success int
      | None => Error "int attribute has no int given"
      end
    end
  | _ => Error ("more than one attributes with necessery name <" ++ name ++ "> found")
  end.

(*default values for gemm*)
From Flocq Require Import Bits BinarySingleNaN.
Definition default_one := Binary.binary_normalize 24 128 eq_refl eq_refl mode_NE 1 0 false : float32.
Definition default_zero := (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) : int64.

(*determines wether an float32 is one*)
Definition float32_is_one (f: float32) : bool :=
  match Z_of_float32 f with
  | Some 1%Z => true
  | _ => false
  end.

(*determines wether an int64 is zero*)
Definition int64_is_zero (i: int64) : bool :=
  match i with
  | (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) => true
  | _ => false
  end.

(*
Returns a NNPremodel_Linear if the input list has exactly three inputs and the output list has exaclty one output.
Also, it reads the attributes. If alpha is not 1 or transA is not 0, an error is returned,
because this are the limits of the verification model.
*)
Definition convert_NodeProto_Gemm_to_NNPremodel (outputs inputs: list string) (attributes: list AttributeProto) : error_option NNPremodel :=
  match outputs with
  | out::[] => match inputs with
    | inp::weight::bias::[] =>
      let alpha := match get_float_attribute attributes "alpha" with
      | Success a => a
      | Error _ => default_one
      end in
      let beta := match get_float_attribute attributes "beta" with
      | Success b => b
      | Error _ => default_one
      end in
      let transA := match get_int_attribute attributes "transA" with
      | Success ta => ta
      | Error _ => default_zero
      end in
      let transB := match get_int_attribute attributes "transB" with
      | Success tb => tb
      | Error _ => default_zero
      end in
      match (float32_is_one alpha), (int64_is_zero transA) with
      | true, true => Success (NNPremodel_Linear inp out weight bias (string_of_int64 transB) (string_of_float32 beta))
      | _, _ => Error "Attribute alpha of gemm operation must be 1 or None AND attribute transA of gemm operation be 0 or None"
      end
    | _ => Error "Gemm node must have exaclty three inputs"
    end
  | _ => Error "Gemm node must have exaclty one output"
  end.

(*declaring this makes the proof much more easy*)
Inductive op_type :=
| Relu
| Gemm
| Undefined
.

(*returns the op_type for a string*)
Definition get_op_type (op_type_string: string) : op_type :=
  match op_type_string with
  | """Relu""" => Relu
  | """Gemm""" => Gemm
  | _ => Undefined
  end.

(*checks if the op_type of a nodeProto is either Relu or Gemm, and call the converter defined above*)
Definition convert_NodeProto_to_NNPremodel (n: NodeProto) : error_option NNPremodel :=
  match n with
  | NodeProto_constructor inputs outputs _ op_type_option _ _ attributes _ _ _ =>
    match op_type_option with
    | Some op_type => match get_op_type op_type with
      | Relu => convert_NodeProto_Relu_to_NNPremodel outputs inputs
      | Gemm => convert_NodeProto_Gemm_to_NNPremodel outputs inputs attributes
      | Undefined => Error ("op_type must be either 'Relu' or 'Gemm', not <" ++ op_type ++ ">")
      end
    | None => Error "op_type must be given in node"
    end
  end.

Open Scope list_scope.

(*
Extracts the list of vertices (node, initializer, input and output) out of the model.
Reverts some list for the verification model.
Returns an empty list if no graph is found
*)
Definition model_proto_to_vertex_list (model: ModelProto) : list vertex :=
  match model with
  | ModelProto_constructor _ _ _ _ _ _ _ graph_option _ _ _ _ => match graph_option with
    | Some graph => match graph with
      | GraphProto_constructor nodes _ initializers _ _ inputs outputs _ _ _ =>
        (map (fun x => output x) (rev outputs)) ++
        (map (fun x => input x) inputs) ++
        (map (fun x => tensor x) initializers) ++
        (map (fun x => node x) (rev nodes))
      end
    | None => []
    end
  end.

(*
Converts a vertex (node, initializer, input or output) to a NNPremodel element,
using the functions defined above.
Input vertices generate errors and should therefore be sorted out before calling this function.
*)
Definition convert_vertex_to_NNPremodel (v: vertex) : error_option NNPremodel :=
  match v with
  | node n => convert_NodeProto_to_NNPremodel n
  | tensor t => convert_TensorProto_to_NNPremodel t
  | input i => Error "Input vertices cannot be converted into NNPremodel elements"
  | output o => convert_ValueInfoProto_to_NNPremodel_Output o
  end.

(*determines if a vertex is not an input vertex*)
Definition is_not_input_vertex (v: vertex) : bool :=
  match v with
  | input _ => false
  | _ => true
  end.

(*
Converts a whole model into a list of NNPremodel vertices (premodel).
It extracts the list of vertices, sorts out the input vertices and calls convert_vertex_to_NNPremodel.
*)
Definition onnx_model_to_premodel_converter (model: ModelProto) : error_option (list NNPremodel) :=
  let vertices := model_proto_to_vertex_list model in
  let vertices_without_inputs := filter is_not_input_vertex vertices in
  list_error_option_to_error_option_list (map convert_vertex_to_NNPremodel vertices_without_inputs).
