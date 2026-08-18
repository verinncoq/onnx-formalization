From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. 
Import ListNotations.
From Stdlib Require Import Strings.Byte.

From ONNXFormalization.ONNXConverter Require Export onnx_model_to_premodel.

(*Functions that help proving*)

(*
Returns True if there is at least one string which occurs in both lists
This is the ONNX definition of how two nodes are connected.
However, this is not how the verification model processes it.
For the verification model, two NODEs are connected if and only if both lists (input and output) BEGIN with the same string.
That is why this function remains unused and an alternative function (begins_with_same_string) is used
*)
Fixpoint string_in_both_lists (l1 l2: list string) : Prop :=
  match l1 with
  | [] => False
  | h::t => match Inb l2 h with
    | true => True
    | false => string_in_both_lists t l2
    end
  end.

(*evaluates if two lists begin with the same string*)
Definition begins_with_same_string (l1 l2: list string) : Prop :=
  match l1, l2 with
  | h1::_, h2::_ => h1 = h2
  | _, _ => False
  end.

(*evaluates if a string is at the second or third position of a list*)
Definition at_second_or_third (s: string) (l: list string) : Prop :=
  match l with
  | _::s'::[] => s = s'
  | _::s'::s''::_ => s = s' \/ s = s''
  | _ => False
  end.

(*
Returns True if there is a directed edge going from n1 to n2, according to ONNX Semantics
Returns False otherwise
*)
Definition directed_edge_onnx_model (n1 n2: vertex) : Prop :=
  match n1, n2 with

  | node node1, node node2 =>
    match node1, node2 with
    | NodeProto_constructor _ outputs _ _ _ _ _ _ _ _,
      NodeProto_constructor inputs _ _ _ _ _ _ _ _ _ =>
      begins_with_same_string outputs inputs
    end
  | node node1, tensor tensor2 => False (*There cannot be a directed edge from a node to an initializer*)
  | node node1, input input2 => False (*There cannot be a directed edge from a node to an input*)
  | node node1, output output2 =>
    match node1, output2 with
    | NodeProto_constructor _ outputs _ _ _ _ _ _ _ _,
      ValueInfoProto_constructor name_option _ _ _ =>
      match name_option with
      | Some name => In name outputs
      | None => False
      end
    end

  | tensor tensor1, node node2 =>
    match tensor1, node2 with
    | TensorProto_constructor _ _ _ _ _ _ _ name_option _ _ _ _ _ _ _,
      NodeProto_constructor inputs _ _ _ _ _ _ _ _ _ =>
      match name_option with
      | Some name => (*In name inputs*)
        (*according to ONNX, this should be correct. But the verification model handels it like this*)
        at_second_or_third name inputs
      | None => False
      end
    end
  | tensor tensor1, tensor tensor2 => False (*There cannot be a directed edge from an initializer to an initializer*)
  | tensor tensor1, input input2 =>
    match tensor1, input2 with
    | TensorProto_constructor _ _ _ _ _ _ _ tensor_name_option _ _ _ _ _ _ _,
      ValueInfoProto_constructor input_name_option _ _ _ =>
      match tensor_name_option, input_name_option with
      | Some tensor_name, Some input_name => tensor_name = input_name
      | _, _ => False
      end
    end
  | tensor tensor1, output output2 =>
    match tensor1, output2 with
    | TensorProto_constructor _ _ _ _ _ _ _ tensor_name_option _ _ _ _ _ _ _,
      ValueInfoProto_constructor output_name_option _ _ _ =>
      match tensor_name_option, output_name_option with
      | Some tensor_name, Some output_name => tensor_name = output_name
      | _, _ => False
      end
    end

  | input input1, node node2 =>
    match input1, node2 with
    | ValueInfoProto_constructor name_option _ _ _,
      NodeProto_constructor _ inputs _ _ _ _ _ _ _ _ =>
      match name_option with
      | Some name => In name inputs
      | None => False
      end
    end
  | input input1, tensor tensor2 => False (*There cannot be a directed edge from an input to an initializer*)
  | input input1, input input2 => False (*There cannot be a directed edge from an input to an input*)
  | input input1, output output2 =>
    match input1, output2 with
    | ValueInfoProto_constructor input_name_option _ _ _,
      ValueInfoProto_constructor output_name_option _ _ _ =>
      match input_name_option, output_name_option with
      | Some input_name, Some output_name => input_name = output_name
      | _, _ => False
      end
    end

  | output output1, node node2 => False (*There cannot be a directed edge from an output to a node*)
  | output output1, tensor tensor2 => False (*There cannot be a directed edge from an output to an initializer*)
  | output output1, input input2 => False (*There cannot be a directed edge from an output to an input*)
  | output output1, output output2 => False (*There cannot be a directed edge from an output to an output*)

  end.


(*
Returns True if there is a directed edge going from n1 to n2, according to ONNX Semantics
Returns False otherwise
*)
Definition directed_edge_premodel (n1 n2: NNPremodel) : Prop :=
  match n1, n2 with
  | NNPremodel_initializer_matrix name1 _ _ _, NNPremodel_initializer_matrix _ _ _ _ =>
    False (*There cannot be a directed edge from an initializer to an initializer*)
  | NNPremodel_initializer_matrix name1 _ _ _, NNPremodel_initializer_vector _ _ _ =>
    False (*There cannot be a directed edge from an initializer to an initializer*)
  | NNPremodel_initializer_matrix name1 _ _ _, NNPremodel_Output name2 _ =>
    name1 = name2
  | NNPremodel_initializer_matrix name1 _ _ _, NNPremodel_Linear _ _ weight bias _ _ => 
    name1 = weight \/ name1 = bias
  | NNPremodel_initializer_matrix name1 _ _ _, NNPremodel_ReLu _ _ =>
    False (*There cannot be a directed edge from an initializer to an relu node*)

  | NNPremodel_initializer_vector name1 _ _, NNPremodel_initializer_matrix _ _ _ _ =>
    False (*There cannot be a directed edge from an initializer to an initializer*)
  | NNPremodel_initializer_vector name1 _ _, NNPremodel_initializer_vector _ _ _ =>
    False (*There cannot be a directed edge from an initializer to an initializer*)
  | NNPremodel_initializer_vector name1 _ _, NNPremodel_Output name2 _ =>
    name1 = name2
  | NNPremodel_initializer_vector name1 _ _, NNPremodel_Linear _ _ weight bias _ _ =>
    name1 = weight \/ name1 = bias
  | NNPremodel_initializer_vector name1 _ _, NNPremodel_ReLu _ _ =>
    False (*There cannot be a directed edge from an initializer to an relu node*)

  | NNPremodel_Output name1 _, NNPremodel_initializer_matrix _ _ _ _ =>
    False (*There cannot be a directed edge from an output to an initializer*)
  | NNPremodel_Output name1 _, NNPremodel_initializer_vector _ _ _ =>
    False (*There cannot be a directed edge from an output to an initializer*)
  | NNPremodel_Output name1 _, NNPremodel_Output name2 _ =>
    False (*There cannot be a directed edge from an output to an output*)
  | NNPremodel_Output name1 _, NNPremodel_Linear _ _ weight bias _ _ =>
    False (*There cannot be a directed edge from an output to a node*)
  | NNPremodel_Output name1 _, NNPremodel_ReLu _ _ =>
    False (*There cannot be a directed edge from an output to a node*)

  | NNPremodel_Linear input1 output1 _ _ _ _, NNPremodel_initializer_matrix _ _ _ _ =>
    False (*There cannot be a directed edge from a node to an initializer*)
  | NNPremodel_Linear input1 output1 _ _ _ _, NNPremodel_initializer_vector _ _ _ =>
    False (*There cannot be a directed edge from a node to an initializer*)
  | NNPremodel_Linear input1 output1 _ _ _ _, NNPremodel_Output name2 _ =>
    output1 = name2
  | NNPremodel_Linear input1 output1 _ _ _ _, NNPremodel_Linear input2 output2 _ _ _ _ =>
    output1 = input2
  | NNPremodel_Linear input1 output1 _ _ _ _, NNPremodel_ReLu input2 output2 =>
    output1 = input2

  | NNPremodel_ReLu input1 output1, NNPremodel_initializer_matrix _ _ _ _ =>
    False (*There cannot be a directed edge from a node to an initializer*)
  | NNPremodel_ReLu input1 output1, NNPremodel_initializer_vector _ _ _ =>
    False (*There cannot be a directed edge from a node to an initializer*)
  | NNPremodel_ReLu input1 output1, NNPremodel_Output name2 _ =>
    output1 = name2
  | NNPremodel_ReLu input1 output1, NNPremodel_Linear input2 output2 _ _ _ _ =>
    output1 = input2
  | NNPremodel_ReLu input1 output1, NNPremodel_ReLu input2 output2 =>
    output1 = input2

  end.


Lemma convert_relu_returns_relu: 
  forall (outputs inputs: list string) (nnseq: NNPremodel),
  convert_NodeProto_Relu_to_NNPremodel outputs inputs = Success nnseq ->
  exists inp out,
  nnseq = NNPremodel_ReLu inp out.
Proof. intros. unfold convert_NodeProto_Relu_to_NNPremodel in H. destruct outputs.
  - inversion H.
  - destruct outputs.
    + destruct inputs.
      * inversion H.
      * destruct inputs.
        -- inversion H. eauto.
        -- inversion H.
    + inversion H.
Qed.

Lemma convert_gemm_returns_gemm: 
  forall (outputs inputs: list string) (attributes: list AttributeProto) (nnseq: NNPremodel),
  convert_NodeProto_Gemm_to_NNPremodel outputs inputs attributes = Success nnseq ->
  exists inp out w b a1 a2,
  nnseq = NNPremodel_Linear inp out w b a1 a2.
Proof. intros. unfold convert_NodeProto_Gemm_to_NNPremodel in H. destruct outputs.
  all: try inversion H. destruct outputs. destruct inputs. all: try inversion H.
  destruct inputs. all: try inversion H. destruct inputs. all: try inversion H.
  destruct inputs. all: try inversion H. destruct (get_float_attribute attributes "alpha").
  destruct (float32_is_one f) eqn:F.
  destruct (int64_is_zero (match get_int_attribute attributes "transA" with
                           | Success ta => ta
                           | Error _ => default_zero
                           end)) eqn:I.
    - inversion H. repeat eexists.
    - inversion H.
    - inversion H.
    - destruct (float32_is_one default_one).
      + destruct (int64_is_zero (match get_int_attribute attributes "transA" with
                                 | Success ta => ta
                                 | Error _ => default_zero
                                 end)) eqn:I.
        * inversion H. repeat eexists.
        * inversion H.
      + inversion H.
Qed.

Lemma convert_node_returns_relu_or_gemm: 
  forall (n: NodeProto) (nnseq: NNPremodel),
  convert_NodeProto_to_NNPremodel n = Success nnseq ->
  (exists inp out, nnseq = NNPremodel_ReLu inp out) \/
  (exists inp out w b a1 a2, nnseq = NNPremodel_Linear inp out w b a1 a2).
Proof. intros. unfold convert_NodeProto_to_NNPremodel in H. destruct n. destruct o0.
- destruct (get_op_type s).
  + left. apply convert_relu_returns_relu in H. apply H.
  + right. apply convert_gemm_returns_gemm in H. apply H.
  + inversion H.
- inversion H.
Qed.

Lemma convert_valueInfo_returns_output:
  forall (meta : list StringStringEntryProto) (doc: option string) (name: string) (type: option TypeProto) (nnseq: NNPremodel),
  convert_ValueInfoProto_to_NNPremodel_Output (ValueInfoProto_constructor (Some name) type doc meta) = Success nnseq ->
  exists dim, nnseq = NNPremodel_Output name dim.
Proof. intros. unfold convert_ValueInfoProto_to_NNPremodel_Output in H.
  destruct type. destruct t. destruct o. destruct v.
  destruct o0. destruct t. destruct o. destruct o0. destruct t.
  destruct (list_error_option_to_error_option_list
        (map Dimension_TensorShapeProto_to_int64 l)).
  destruct (filter not_one l0).
  all: inversion H.
  all: eauto.
  destruct l1. destruct (Z_of_int64 i0).
  all: inversion H. eauto. destruct o0. destruct t. 
  destruct (list_error_option_to_error_option_list
         (map Dimension_TensorShapeProto_to_int64 l)).
  destruct (filter not_one l0). inversion H2. eauto. destruct l1. destruct (Z_of_int64 i).
  all: inversion H. eauto. destruct t. destruct o0. destruct t.
  destruct (list_error_option_to_error_option_list
         (map Dimension_TensorShapeProto_to_int64 l)).
  destruct (filter not_one l0). inversion H3. eauto. destruct l1. destruct (Z_of_int64 i).
  all: inversion H. eauto.
  Qed.

Lemma convert_tensor_returns_matrix_or_vector:
  forall
  (l: list StringStringEntryProto)
  (l0: list uint64)
  (l1: list float64)
  (o: option DataLocation_TensorProto)
  (l2: list StringStringEntryProto)
  (o0: option bytes)
  (o1: option string)
  (s7: string)
  (l3: list int64)
  (l4: list bytes)
  (l5: list int32)
  (l6: list float32)
  (o3: option Segment_TensorProto)
  (o4: option int32)
  (l7: list int64)
  (nnseq: NNPremodel),
  convert_TensorProto_to_NNPremodel (TensorProto_constructor l7 o4 o3 l6 l5 l4 l3 (Some s7) o1 o0 l2 o l1 l0 l) =
  Success nnseq ->
  (exists n1 n2 s0, nnseq = NNPremodel_initializer_matrix s7 n1 n2 s0) \/
  (exists n s0, nnseq = NNPremodel_initializer_vector s7 n s0).
Proof. intros. unfold convert_TensorProto_to_NNPremodel in H.
  destruct o4. destruct (Z_of_int32 i). all: inversion H.
  destruct p. destruct p. destruct p. all: inversion H.
  destruct (emptyList l3). destruct o0.
  destruct (emptyList l0 && emptyList l1 && true && emptyList l5 && emptyList l6)%bool.
  destruct (int64_string_of_bytes b). all: inversion H.
  unfold convert_data_to_NNPremodel in H.
  destruct l7. all: inversion H.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H.
  - right. eauto.
  - destruct l7. destruct (Z_of_int64 i0). all: inversion H.
    destruct (Z_of_int64 i1). all: inversion H. left. eauto.
  - destruct ((emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l5 && emptyList l6)%bool).
    unfold convert_data_to_NNPremodel in H.
    destruct l7. all: inversion H. destruct l7. destruct (Z_of_int64 i0). all: inversion H.
    * right. eauto.
    * destruct l7. destruct (Z_of_int64 i0). all: inversion H.
      destruct (Z_of_int64 i1). inversion H6. inversion H8. eauto. inversion H6.
  - destruct p. all: inversion H. destruct p. all: inversion H.
  - destruct p. destruct p. all: inversion H.
    destruct (emptyList l5). destruct o0.
    destruct (emptyList l0 && emptyList l1 && emptyList l3 && true && emptyList l6)%bool.
    destruct (int32_string_of_bytes b). all: inversion H.
    unfold convert_data_to_NNPremodel in H.
    destruct l7. all: inversion H. destruct l7. destruct (Z_of_int64 i0). all: inversion H.
    * right. eauto.
    * destruct l7. destruct (Z_of_int64 i0). all: inversion H.
      destruct (Z_of_int64 i1). inversion H. inversion H. eauto. inversion H.
    * destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l6)%bool.
      unfold convert_data_to_NNPremodel in H.
      destruct l7. all: inversion H. destruct l7. destruct (Z_of_int64 i0). all: inversion H.
      ** right. eauto.
      ** destruct l7. destruct (Z_of_int64 i0). all: inversion H.
         destruct (Z_of_int64 i1). all: inversion H. left. eauto.
  - destruct (emptyList l6). destruct o0.
    destruct (emptyList l0 && emptyList l1 && emptyList l3 && emptyList l5 && true)%bool.
    destruct (float32_string_of_bytes b).
    unfold convert_data_to_NNPremodel in H.
    destruct l7. all: inversion H. destruct l7. destruct (Z_of_int64 i0).
    all: inversion H. right. eauto.
    destruct l7. destruct (Z_of_int64 i0). all: inversion H.
    destruct (Z_of_int64 i1). all: inversion H.
    left. eauto.
    destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l5)%bool.
    unfold convert_data_to_NNPremodel in H.
    destruct l7. all: inversion H. destruct l7. destruct (Z_of_int64 i0).
    all: inversion H. right. eauto.
    destruct l7. destruct (Z_of_int64 i0). all: inversion H.
    destruct (Z_of_int64 i1). all: inversion H.
    left. eauto.
  Qed.

Theorem node_linear_input_link: forall
  (l : list NodeDeviceConfigurationProto)
  (l0 : list StringStringEntryProto)
  (l1 : list AttributeProto)
  (o o0 o1 o2 o3 : option string)
  (l2 l3 : list string)
  (s s0 s1 s2 s3 s4: string),
  (convert_vertex_to_NNPremodel (node (NodeProto_constructor l3 l2 o3 o2 o1 o0 l1 o l0 l)) =
  Success (NNPremodel_Linear s s0 s1 s2 s3 s4)) ->
  l3 = s::s1::s2::[].
Proof. intros. simpl in H. destruct o2.
  * destruct (get_op_type s5).
    + unfold convert_NodeProto_Relu_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. destruct l3. all: try inversion H.
      destruct l3. all: try inversion H.
    + unfold convert_NodeProto_Gemm_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. 
      repeat (destruct l3; try inversion H).
      destruct (float32_is_one
        match get_float_attribute l1 "alpha" with
        | Success a => a
        | Error _ => default_one
        end). destruct (int64_is_zero
          match get_int_attribute l1 "transA" with
          | Success ta => ta
          | Error _ => default_zero
          end). destruct (string_of_int64
            match get_int_attribute l1 "transB" with
            | Success tb => tb
            | Error _ => default_zero
            end). destruct (string_of_float32
                    match get_float_attribute l1 "beta" with
                    | Success b => b
                    | Error _ => default_one
                    end). all: try inversion H1. all: reflexivity.
    + inversion H.
  * inversion H.
  Qed.

Theorem node_relu_input_link: forall
  (l : list NodeDeviceConfigurationProto)
  (l0 : list StringStringEntryProto)
  (l1 : list AttributeProto)
  (o o0 o1 o2 o3 : option string)
  (l2 l3 : list string)
  (s s0: string),
  (convert_vertex_to_NNPremodel (node (NodeProto_constructor l3 l2 o3 o2 o1 o0 l1 o l0 l)) =
  Success (NNPremodel_ReLu s s0)) ->
  l3 = [s].
Proof. intros. simpl in H. destruct o2.
  * destruct (get_op_type s1).
    + unfold convert_NodeProto_Relu_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. destruct l3. all: try inversion H.
      destruct l3. all: try inversion H. eauto.
    + unfold convert_NodeProto_Gemm_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. 
      repeat (destruct l3; try inversion H).
      destruct (float32_is_one
        match get_float_attribute l1 "alpha" with
        | Success a => a
        | Error _ => default_one
        end). destruct (int64_is_zero
          match get_int_attribute l1 "transA" with
          | Success ta => ta
          | Error _ => default_zero
          end). destruct (string_of_int64
            match get_int_attribute l1 "transB" with
            | Success tb => tb
            | Error _ => default_zero
            end). destruct (string_of_float32
                    match get_float_attribute l1 "beta" with
                    | Success b => b
                    | Error _ => default_one
                    end). all: try inversion H1.
    + inversion H.
  * inversion H.
  Qed.

Theorem node_linear_output_link: forall
  (l : list NodeDeviceConfigurationProto)
  (l0 : list StringStringEntryProto)
  (l1 : list AttributeProto)
  (o o0 o1 o2 o3 : option string)
  (l2 l3 : list string)
  (s s0 s1 s2 s3 s4: string),
  (convert_vertex_to_NNPremodel (node (NodeProto_constructor l3 l2 o3 o2 o1 o0 l1 o l0 l)) =
  Success (NNPremodel_Linear s s0 s1 s2 s3 s4)) ->
  l2 = [s0].
Proof. intros. simpl in H. destruct o2.
  * destruct (get_op_type s5).
    + unfold convert_NodeProto_Relu_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. destruct l3. all: try inversion H.
      destruct l3. all: try inversion H.
    + unfold convert_NodeProto_Gemm_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. 
      repeat (destruct l3; try inversion H).
      destruct (float32_is_one
        match get_float_attribute l1 "alpha" with
        | Success a => a
        | Error _ => default_one
        end). destruct (int64_is_zero
          match get_int_attribute l1 "transA" with
          | Success ta => ta
          | Error _ => default_zero
          end). destruct (string_of_int64
            match get_int_attribute l1 "transB" with
            | Success tb => tb
            | Error _ => default_zero
            end). destruct (string_of_float32
                    match get_float_attribute l1 "beta" with
                    | Success b => b
                    | Error _ => default_one
                    end). all: try inversion H1; reflexivity.
    + inversion H.
  * inversion H.
  Qed.

Theorem node_relu_output_link: forall
  (l : list NodeDeviceConfigurationProto)
  (l0 : list StringStringEntryProto)
  (l1 : list AttributeProto)
  (o o0 o1 o2 o3 : option string)
  (l2 l3 : list string)
  (s s0: string),
  (convert_vertex_to_NNPremodel (node (NodeProto_constructor l3 l2 o3 o2 o1 o0 l1 o l0 l)) =
  Success (NNPremodel_ReLu s s0)) ->
  l2 = [s0].
Proof. intros. simpl in H. destruct o2.
  * destruct (get_op_type s1).
    + unfold convert_NodeProto_Relu_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. destruct l3. all: try inversion H.
      destruct l3. all: try inversion H. eauto.
    + unfold convert_NodeProto_Gemm_to_NNPremodel in H. destruct l2. 
      all: try inversion H. destruct l2. all: try inversion H. 
      repeat (destruct l3; try inversion H).
      destruct (float32_is_one
        match get_float_attribute l1 "alpha" with
        | Success a => a
        | Error _ => default_one
        end). destruct (int64_is_zero
          match get_int_attribute l1 "transA" with
          | Success ta => ta
          | Error _ => default_zero
          end). destruct (string_of_int64
            match get_int_attribute l1 "transB" with
            | Success tb => tb
            | Error _ => default_zero
            end). destruct (string_of_float32
                    match get_float_attribute l1 "beta" with
                    | Success b => b
                    | Error _ => default_one
                    end). all: try inversion H1.
    + inversion H.
  * inversion H.
  Qed.


Theorem tensor_matrix_link: forall
  (l: list StringStringEntryProto)
  (l0: list uint64)
  (l1: list float64)
  (o: option DataLocation_TensorProto)
  (l2: list StringStringEntryProto)
  (o0: option bytes)
  (o1: option string)
  (s7 s: string)
  (l3: list int64)
  (l4: list bytes)
  (l5: list int32)
  (l6: list float32)
  (o3: option Segment_TensorProto)
  (o4: option int32)
  (l7: list int64)
  (n n0: nat)
  (s0: (nat -> nat -> string)),
  convert_TensorProto_to_NNPremodel (TensorProto_constructor l7 o4 o3 l6 l5 l4 l3 (Some s7) o1 o0 l2 o l1 l0 l) =
  Success (NNPremodel_initializer_matrix s n n0 s0) ->
  s7 = s.
Proof. intros. simpl in H. 
  destruct o4. destruct (Z_of_int32 i). all: inversion H.
  destruct p. destruct p. destruct p. all: inversion H.
  destruct (emptyList l3). destruct o0.
  destruct (emptyList l0 && emptyList l1 && true && emptyList l5 && emptyList l6)%bool.
  destruct (int64_string_of_bytes b). all: inversion H.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. reflexivity.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l5 && emptyList l6)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H10. reflexivity.
  destruct p. all: inversion H11. destruct p. all: inversion H12.
  destruct p. destruct p. all: inversion H13. destruct (emptyList l5).
  destruct o0. destruct (emptyList l0 && emptyList l1 && emptyList l3 && true && emptyList l6)%bool.
  destruct (int32_string_of_bytes b).
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3. destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. reflexivity.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l6)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3. destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. reflexivity.
  destruct (emptyList l6)%bool. destruct o0.
  destruct (emptyList l0 && emptyList l1 && emptyList l3 && emptyList l5 && true)%bool.
  destruct (float32_string_of_bytes b).
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3. destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. reflexivity.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l5)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3. destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. reflexivity.
  Qed.

Theorem tensor_vector_link: forall
  (l: list StringStringEntryProto)
  (l0: list uint64)
  (l1: list float64)
  (o: option DataLocation_TensorProto)
  (l2: list StringStringEntryProto)
  (o0: option bytes)
  (o1: option string)
  (s7 s: string)
  (l3: list int64)
  (l4: list bytes)
  (l5: list int32)
  (l6: list float32)
  (o3: option Segment_TensorProto)
  (o4: option int32)
  (l7: list int64)
  (n: nat)
  (s0: (nat -> string)),
  convert_TensorProto_to_NNPremodel (TensorProto_constructor l7 o4 o3 l6 l5 l4 l3 (Some s7) o1 o0 l2 o l1 l0 l) =
  Success (NNPremodel_initializer_vector s n s0) ->
  s7 = s.
Proof. intros. simpl in H. 
  destruct o4. destruct (Z_of_int32 i). all: inversion H.
  destruct p. destruct p. destruct p. all: inversion H.
  destruct (emptyList l3). destruct o0.
  destruct (emptyList l0 && emptyList l1 && true && emptyList l5 && emptyList l6)%bool.
  destruct (int64_string_of_bytes b). all: inversion H.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. all: inversion H3.
  destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l5 && emptyList l6)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3.
  destruct (Z_of_int64 i1). all: inversion H3. destruct p. all: inversion H3.
  destruct p. all: inversion H3. destruct p. all: inversion H3.
  destruct p. all: inversion H3.
  destruct (emptyList l5). destruct o0. 
  destruct (emptyList l0 && emptyList l1 && emptyList l3 && true && emptyList l6)%bool.
  destruct (int32_string_of_bytes b).
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. 
  destruct (Z_of_int64 i1). all: inversion H3.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l6)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. 
  destruct (Z_of_int64 i1). all: inversion H3.
  destruct (emptyList l6)%bool. destruct o0.
  destruct (emptyList l0 && emptyList l1 && emptyList l3 && emptyList l5 && true)%bool.
  destruct (float32_string_of_bytes b).
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. 
  destruct (Z_of_int64 i1). all: inversion H3.
  destruct (emptyList l0 && emptyList l1 && emptyOption o0 && emptyList l3 && emptyList l5)%bool.
  unfold convert_data_to_NNPremodel in H3.
  destruct l7. all: inversion H3.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. reflexivity.
  destruct l7. destruct (Z_of_int64 i0). all: inversion H3. 
  destruct (Z_of_int64 i1). all: inversion H3.
  Qed.

Theorem output_link: forall
  (l8: list StringStringEntryProto)
  (o5: option string)
  (o6: option TypeProto)
  (s3 s1: string)
  (n1: nat),
  convert_ValueInfoProto_to_NNPremodel_Output (ValueInfoProto_constructor (Some s3) o6 o5 l8) =
  Success (NNPremodel_Output s1 n1) ->
  s1 = s3.
Proof. intros. simpl in H. destruct o6. destruct t. destruct o. destruct v. destruct t.
  destruct o0. destruct o1. destruct t.
  destruct (list_error_option_to_error_option_list
    (map Dimension_TensorShapeProto_to_int64 l)).
  destruct (filter not_one l0). all: inversion H.
  - reflexivity.
  - destruct l1. destruct (Z_of_int64 i). all: inversion H. inversion H1. reflexivity.
  - destruct o1. destruct t.
    destruct (list_error_option_to_error_option_list
         (map Dimension_TensorShapeProto_to_int64 l)).
    destruct (filter not_one l0). inversion H1. all: try reflexivity.
    destruct l1. destruct (Z_of_int64 i). inversion H1. inversion H1. all: try reflexivity.
    all: inversion H1.
  Qed.


Theorem isomorphism_left: forall (v1 v2: vertex) (n1 n2: NNPremodel),
  convert_vertex_to_NNPremodel v1 = Success n1 -> (*when v1 gets converted successfully to n1*)
  convert_vertex_to_NNPremodel v2 = Success n2 -> (*when v2 gets converted successfully to n2*)
  directed_edge_onnx_model v1 v2 -> (*when there is a directed edge between v1 and v2*)
  directed_edge_premodel n1 n2 (*then there is a directed edge between n1 and n2*)
.
Proof. intros v1 v2 n1 n2 H1 H2 ISO. destruct v1.
  - destruct n1.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 and v2 are node, n1 and n2 are Linear*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_linear_output_link in H1. apply node_linear_input_link in H2.
            rewrite H1 in ISO. simpl in ISO. destruct l8. rewrite H2 in ISO. rewrite ISO. reflexivity.
             rewrite H2 in ISO. rewrite ISO. reflexivity.
        +++ (*interesting: v1 and v2 are node, n1 is Linear, n2 is ReLu*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_linear_output_link in H1. apply node_relu_input_link in H2.
            rewrite H1 in ISO. simpl in ISO. destruct l8. all: try inversion ISO.
            inversion H2. rewrite H2 in ISO. rewrite <- ISO. reflexivity.
            rewrite H2 in ISO. rewrite ISO. reflexivity.
      ++ simpl in ISO. inversion ISO.
      ++ simpl in ISO. inversion ISO.
      ++ destruct n2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is node, v2 is output, n1 is Linear, n2 is output*)
            simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            simpl in ISO. destruct n. apply node_linear_output_link in H1. simpl.
            rewrite H1 in ISO. simpl in ISO. destruct ISO. apply H0. inversion H0.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 and v2 are node, n1 is ReLu, n2 is Linear*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_relu_output_link in H1. apply node_linear_input_link in H2.
            rewrite H1 in ISO. simpl in ISO. destruct l8. all: try inversion ISO.
            inversion H2. rewrite H2 in ISO. rewrite ISO. reflexivity.
            rewrite H2 in ISO. rewrite ISO. reflexivity.
        +++ (*interesting: v1 and v2 are node, n1 and n2 are ReLu*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_relu_output_link in H1. apply node_relu_input_link in H2.
            rewrite H1 in ISO. simpl in ISO. destruct l8. all: try inversion ISO.
            inversion H2. rewrite H2 in ISO. rewrite ISO. reflexivity.
            rewrite H2 in ISO. rewrite ISO. reflexivity.
      ++ simpl in ISO. inversion ISO.
      ++ simpl in ISO. inversion ISO.
      ++ destruct n2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is node, v2 is output, n1 is ReLu, n2 is output*)
            simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            simpl in ISO. destruct n. apply node_relu_output_link in H1. simpl.
            rewrite H1 in ISO. simpl in ISO. destruct ISO. apply H0. inversion H0.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
  - destruct n1.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 is tensor, v2 is node, n1 is matrix, n2 is linear*)
            simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n1. destruct o1. all: try inversion ISO.
            apply tensor_matrix_link in H1. apply node_linear_input_link in H2. simpl. rewrite H2 in ISO.
            simpl in ISO. destruct ISO.
            ** rewrite H1 in H. left. rewrite H. reflexivity.
            ** rewrite H1 in H. right. rewrite H. reflexivity.
        +++ simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n1. destruct o1. all: try inversion ISO.
            apply tensor_matrix_link in H1. apply node_relu_input_link in H2. simpl. rewrite H2 in ISO.
            simpl in ISO. inversion ISO.
      ++ simpl in ISO. inversion ISO.
      ++ destruct n2. all: simpl in H2. all: inversion H2.
      ++ destruct n2. all: simpl in H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is tensor, v2 is output, n1 is matrix, n2 is output*)
            simpl in H1. simpl in ISO. destruct t. destruct v. destruct o1. destruct o5.
            apply tensor_matrix_link in H1. apply output_link in H2.
            * simpl. rewrite <- H1. rewrite H2. rewrite ISO. reflexivity.
            * inversion ISO.
            * inversion ISO.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 is tensor, v2 is node, n1 is vector, n2 is linear*)
            simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n0. destruct o1. all: try inversion ISO.
            apply tensor_vector_link in H1. apply node_linear_input_link in H2. simpl. rewrite H2 in ISO.
            simpl in ISO. destruct ISO.
            ** rewrite H1 in H. left. rewrite H. reflexivity.
            ** rewrite H1 in H. right. rewrite H. reflexivity.
        +++ simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n0. destruct o1. all: try inversion ISO.
            apply tensor_vector_link in H1. apply node_relu_input_link in H2. simpl. rewrite H2 in ISO.
            simpl in ISO. inversion ISO.
      ++ simpl in ISO. inversion ISO.
      ++ destruct n2. all: simpl in H2. all: inversion H2.
      ++ destruct n2. all: simpl in H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is tensor, v2 is output, n1 is vector, n2 is output*)
            simpl in H1. simpl in ISO. destruct t. destruct v. destruct o1. destruct o5.
            apply tensor_vector_link in H1. apply output_link in H2.
            * simpl. rewrite <- H1. rewrite H2. rewrite ISO. reflexivity.
            * inversion ISO.
            * inversion ISO.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
  - simpl in H1. inversion H1.
  - simpl in ISO. destruct v2. all: inversion ISO.
  Qed.


Theorem isomorphism_right: forall (v1 v2: vertex) (n1 n2: NNPremodel),
  convert_vertex_to_NNPremodel v1 = Success n1 -> (*when v1 gets converted successfully to n1*)
  convert_vertex_to_NNPremodel v2 = Success n2 -> (*when v2 gets converted successfully to n2*)
  directed_edge_premodel n1 n2 -> (*when there is a directed edge between n1 and n2*)
  directed_edge_onnx_model v1 v2 (*then there is a directed edge between v1 and v2*)
.
Proof. intros v1 v2 n1 n2 H1 H2 ISO. destruct v1.
  - destruct n1.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + simpl in H1. apply convert_node_returns_relu_or_gemm in H1. destruct H1.
      * inversion H; inversion H0; inversion H1.
      * inversion H; inversion H0; inversion H1; inversion H3; inversion H4; inversion H5; inversion H6.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 and v2 are node, n1 and n2 are Linear*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_linear_output_link in H1. apply node_linear_input_link in H2.
            rewrite H1. rewrite H2. simpl. rewrite ISO. reflexivity.
        +++ (*interesting: v1 and v2 are node, n1 is Linear, n2 is ReLu*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_linear_output_link in H1. apply node_relu_input_link in H2.
            rewrite H1. rewrite H2. simpl. rewrite ISO. reflexivity.
      ++ simpl in ISO. destruct n2. all: inversion ISO.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
      ++ simpl in ISO. destruct n2. all: inversion ISO.
        +++ simpl in H2. inversion H2.
        +++ simpl in H2. inversion H2.
        +++ simpl in H2. inversion H2.
      ++ destruct n2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is node, v2 is output, n1 is Linear, n2 is output*)
            simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            simpl in ISO. destruct n. apply node_linear_output_link in H1. simpl.
            rewrite <- H2. rewrite <- ISO. rewrite H1. simpl. left. reflexivity.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 and v2 are node, n1 is ReLu, n2 is Linear*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_relu_output_link in H1. apply node_linear_input_link in H2.
            rewrite H1. rewrite H2.  simpl. rewrite ISO. reflexivity.
        +++ (*interesting: v1 and v2 are node, n1 and n2 are ReLu*)
            simpl in ISO. destruct n. destruct n0. simpl.
            apply node_relu_output_link in H1. apply node_relu_input_link in H2.
            rewrite H1. rewrite H2.  simpl. rewrite ISO. reflexivity.
      ++ simpl in ISO. destruct n2. all: inversion ISO.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ simpl in H2. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0.  destruct H0. inversion H0.
            destruct H0.  destruct H0. inversion H0.
            simpl in H2. inversion H2.
      ++ simpl in ISO. destruct n2. all: inversion ISO.
        +++ simpl in H2. inversion H2.
        +++ simpl in H2. inversion H2.
        +++ simpl in H2. inversion H2.
      ++ destruct n2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is node, v2 is output, n1 is ReLu, n2 is output*)
            simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            simpl in ISO. destruct n. apply node_relu_output_link in H1. simpl.
            rewrite <- H2. rewrite <- ISO. rewrite H1. simpl. left. reflexivity.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
        +++ simpl in H2. destruct v. destruct o.
            ** apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            ** simpl in H2. destruct o0. all: inversion H2.
  - destruct n1.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 is tensor, v2 is node, n1 is matrix, n2 is linear*)
            simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n1. destruct o1. all: try inversion ISO.
            apply tensor_matrix_link in H1. apply node_linear_input_link in H2. simpl.
            * destruct ISO.
              ** rewrite H1. rewrite H. rewrite H2. simpl. left. reflexivity.
              ** rewrite H1. rewrite H. rewrite H2. simpl. left. reflexivity.
            * apply tensor_matrix_link in H1. apply node_linear_input_link in H2. simpl.
              ** rewrite H2. rewrite H1. destruct ISO. all: rewrite H0. all: simpl.
                 *** left. reflexivity.
                 *** right. reflexivity.
            * simpl in H1. inversion H1.
            * simpl in H1. inversion H1.
        +++ simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n1. destruct o2. all: try inversion ISO.
      ++ simpl in ISO. destruct n2. all: inversion ISO.
        +++ simpl. simpl in H2. destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0. simpl in H2. inversion H2.
        +++ simpl. simpl in H2. destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0. simpl in H2. inversion H2.
        +++ simpl. simpl in H2. destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2. destruct H2.
            destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0. simpl in H2. inversion H2.
      ++ simpl in H2. inversion H2.
      ++ simpl in H2. destruct n2.
         +++ simpl in ISO. inversion ISO.
         +++ simpl in ISO. inversion ISO.
         +++ (*interesting: v1 is tensor, v2 is output, n1 is matrix, n2 is output*)
            simpl in H1. simpl in ISO. destruct t. destruct v. destruct o1. destruct o5.
            apply tensor_matrix_link in H1. apply output_link in H2.
            * simpl. rewrite H1. rewrite <- H2. rewrite ISO. reflexivity.
            * simpl in H2. destruct o6. all: inversion H2.
            * simpl in H1. inversion H1.
         +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
         +++ simpl in ISO. inversion ISO.
    + destruct v2.
      ++ destruct n2.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ simpl in H2. apply convert_node_returns_relu_or_gemm in H2. destruct H2.
            * inversion H; inversion H0; inversion H2.
            * inversion H; inversion H0; inversion H2; inversion H3; inversion H4; inversion H5; inversion H6.
        +++ (*interesting: v1 is tensor, v2 is node, n1 is vector, n2 is linear*)
            simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n0. destruct o1. all: try inversion ISO.
            apply tensor_vector_link in H1. apply node_linear_input_link in H2. simpl.
            ** rewrite H1. rewrite H. rewrite H2. simpl. destruct ISO. left. reflexivity.
               right. rewrite <- H0. rewrite <- H. reflexivity.
            ** simpl. apply tensor_vector_link in H1. apply node_linear_input_link in H2. simpl. 
               rewrite H2. rewrite H1. rewrite H. simpl. right. reflexivity.
            ** simpl in H1. inversion H1.
            ** simpl in H1. inversion H1.
        +++ simpl in H1; simpl in H2. simpl in ISO. destruct t. destruct n0. destruct o1. all: try inversion ISO.
      ++ simpl in ISO. destruct n2. all: inversion ISO. all: simpl in H2.
        +++ destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2.
            destruct H2. destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2.
            destruct H2. destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0.
            simpl in H2. inversion H2.
        +++ destruct t0. destruct o1. apply convert_tensor_returns_matrix_or_vector in H2.
            destruct H2. destruct H0. destruct H0. destruct H0. inversion H0.
            destruct H0. destruct H0. inversion H0.
            simpl in H2. inversion H2.
      ++ destruct n2. all: simpl in H2. all: inversion H2.
      ++ destruct n2. all: simpl in H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ (*interesting: v1 is tensor, v2 is output, n1 is vector, n2 is output*)
            simpl in H1. simpl in ISO. destruct t. destruct v. destruct o1. destruct o5.
            apply tensor_vector_link in H1. apply output_link in H2.
            * simpl. rewrite H1. rewrite <- H2. rewrite ISO. reflexivity.
            * simpl in H2. destruct o6. all: inversion H2.
            * simpl in H1. inversion H1.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
        +++ destruct v. destruct o.
            * apply convert_valueInfo_returns_output in H2. destruct H2. inversion H.
            * simpl in H2. destruct o0. all: inversion H2.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
    + simpl in H1. destruct t. destruct o1. apply convert_tensor_returns_matrix_or_vector in H1. destruct H1.
      destruct H. destruct H. destruct H. inversion H.
      destruct H. destruct H. inversion H. simpl in H1. inversion H1.
  - simpl in H1. inversion H1.
  - destruct n1. all: simpl in H1.
    + destruct v. destruct o. apply convert_valueInfo_returns_output in H1.
      destruct H1. inversion H.
      simpl in H1. destruct o0. all: inversion H1.
    + destruct v. destruct o. apply convert_valueInfo_returns_output in H1.
      destruct H1. inversion H.
      simpl in H1. destruct o0. all: inversion H1.
    + simpl in ISO. destruct n2. all: inversion ISO.
    + destruct v. destruct o. apply convert_valueInfo_returns_output in H1.
      destruct H1. inversion H.
      simpl in H1. destruct o0. all: inversion H1.
    + destruct v. destruct o. apply convert_valueInfo_returns_output in H1.
      destruct H1. inversion H.
      simpl in H1. destruct o0. all: inversion H1.
  Qed.


Theorem isomorphism: forall (v1 v2: vertex) (n1 n2: NNPremodel),
  convert_vertex_to_NNPremodel v1 = Success n1 -> (*when v1 gets converted successfully to n1*)
  convert_vertex_to_NNPremodel v2 = Success n2 -> (*when v2 gets converted successfully to n2*)
  directed_edge_onnx_model v1 v2 <-> directed_edge_premodel n1 n2
  (*there is a directed edge between n1 and n2 if and only if there is a directed edge between v1 and v2*)
.
Proof. intros v1 v2 n1 n2 H1 H2. split.
  - apply isomorphism_left. apply H1. apply H2.
  - apply isomorphism_right. apply H1. apply H2.
Qed.