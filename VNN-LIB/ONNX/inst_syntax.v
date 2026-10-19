From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import boot algebra order reals Rstruct.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst real.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

(********************************************)
(**************** SYNTAX ********************)
(********************************************)

Definition supported_types : seq DataType_TensorProto :=
  [:: FLOAT_TensorProto; INT32_TensorProto; INT64_TensorProto].

Definition Elem : eqType := { x in supported_types }.
Definition default_NodeProto : NodeProto :=
  NodeProto_constructor nil nil None None None None nil None nil nil.

Definition value_info_name (v : ValueInfoProto) : string :=
  match v with
  | ValueInfoProto_constructor (Some nm) _ _ _ => nm
  | ValueInfoProto_constructor None _ _ _ => ""%string
  end.

Definition graph_of (m : ModelProto) : option GraphProto :=
  match m with
  | ModelProto_constructor _ _ _ _ _ _ _ g _ _ _ _ => g
  end.

Definition graph_inputs (m : ModelProto) : list ValueInfoProto :=
  match graph_of m with
  | Some (GraphProto_constructor _ _ _ _ _ values _ _ _ _) => values
  | _ => nil
  end.

Definition graph_outputs (m : ModelProto) : list ValueInfoProto :=
  match graph_of m with
  | Some (GraphProto_constructor _ _ _ _ _ _ outp _ _ _) => outp
  | None => nil
  end.

Definition graph_nodes (m : ModelProto) : list NodeProto :=
  match graph_of m with
  | Some (GraphProto_constructor nds _ _ _ _ _ _ _ _ _) => nds
  | None => nil
  end.

Definition model_values (m : ModelProto) : list ValueInfoProto :=
  match graph_of m with
  | Some (GraphProto_constructor _ _ _ _ _ _ _ values _ _) => values
  | _ => nil
  end.

Definition node_output_names (n : NodeProto) : list string :=
  match n with
  | NodeProto_constructor _ outp _ _ _ _ _ _ _ _ => outp
  end.

Definition int32_of_DataType_TensorProto (x : DataType_TensorProto) : int32 :=
  match x with
  | UNDEFINED_TensorProto => (x00, x00, x00, x00)
  | FLOAT_TensorProto => (x00, x00, x00, x01)
  | UINT8_TensorProto => (x00, x00, x00, x02)
  | INT8_TensorProto => (x00, x00, x00, x03)
  | UINT16_TensorProto => (x00, x00, x00, x04)
  | INT16_TensorProto => (x00, x00, x00, x05)
  | INT32_TensorProto => (x00, x00, x00, x06)
  | INT64_TensorProto => (x00, x00, x00, x07)
  | STRING_TensorProto => (x00, x00, x00, x08)
  | BOOL_TensorProto => (x00, x00, x00, x09)
  | FLOAT16_TensorProto => (x00, x00, x00, x0a)
  | DOUBLE_TensorProto => (x00, x00, x00, x0b)
  | UINT32_TensorProto => (x00, x00, x00, x0c)
  | UINT64_TensorProto => (x00, x00, x00, x0d)
  | COMPLEX64_TensorProto => (x00, x00, x00, x0e)
  | COMPLEX128_TensorProto => (x00, x00, x00, x0f)
  | BFLOAT16_TensorProto => (x00, x00, x00, x10)
  | FLOAT8E4M3FN_TensorProto => (x00, x00, x00, x11)
  | FLOAT8E4M3FNUZ_TensorProto => (x00, x00, x00, x12)
  | FLOAT8E5M2_TensorProto => (x00, x00, x00, x13)
  | FLOAT8E5M2FNUZ_TensorProto => (x00, x00, x00, x14)
  | UINT4_TensorProto => (x00, x00, x00, x15)
  | INT4_TensorProto => (x00, x00, x00, x16)
  | FLOAT4E2M1_TensorProto => (x00, x00, x00, x17)
  end.

Definition DataType_TensorProto_of_int32 (i : int32) : option DataType_TensorProto :=
  match Z_of_int32 i with
  | 0 => Some UNDEFINED_TensorProto
  | 1 => Some FLOAT_TensorProto
  | 2 => Some UINT8_TensorProto
  | 3 => Some INT8_TensorProto
  | 4 => Some UINT16_TensorProto
  | 5 => Some INT16_TensorProto
  | 6 => Some INT32_TensorProto
  | 7 => Some INT64_TensorProto
  | 8 => Some STRING_TensorProto
  | 9 => Some BOOL_TensorProto
  | 10 => Some FLOAT16_TensorProto
  | 11 => Some DOUBLE_TensorProto
  | 12 => Some UINT32_TensorProto
  | 13 => Some UINT64_TensorProto
  | 14 => Some COMPLEX64_TensorProto
  | 15 => Some COMPLEX128_TensorProto
  | 16 => Some BFLOAT16_TensorProto
  | 17 => Some FLOAT8E4M3FN_TensorProto
  | 18 => Some FLOAT8E4M3FNUZ_TensorProto
  | 19 => Some FLOAT8E5M2_TensorProto
  | 20 => Some FLOAT8E5M2FNUZ_TensorProto
  | 21 => Some UINT4_TensorProto
  | 22 => Some INT4_TensorProto
  | 23 => Some FLOAT4E2M1_TensorProto
  | _ => None
  end%Z.

Definition value_tensor_type (v : ValueInfoProto) : option DataType_TensorProto :=
match v with
| ValueInfoProto_constructor _ typeP _ _ =>
    match typeP with
    | Some (TypeProto_constructor (Some (tensor_type_value_TypeProto t)) _) =>
        match t with
        | Tensor_TypeProto_constructor type _ =>  obind DataType_TensorProto_of_int32 type
        end
    | _ => None
    end
end.

Definition has_value_tensor_type (v : ValueInfoProto) : bool :=
  match value_tensor_type v with
  | Some _ => true
  | _ => false
  end.

Definition network_dim_match (m : ModelProto) (n : NetworkType Elem) : bool :=
match n with
| networkType (exist inps inpsgt0) (exist outs outsgt0) =>
    [&& (subseq (graph_inputs m) (model_values m)),
      (subseq (graph_outputs m) (model_values m)),
      all2 (fun x => eq_op (Some (tag (tensorTypes Elem x)))) inps (map value_tensor_type (graph_inputs m)) (** A predicate that says the shape and types of the NetworkType are respected by the model's outputs **)
         (** A predicate that says the shape and types of the NetworkType are respected by the model's outputs **)
      (* all (oapp (mem supported_types) false) (map value_tensor_type (graph_outputs m)) (** A predicate saying that all outputs must exist and have a valid type **) *)
      & all2 (fun x => eq_op (Some (tag (tensorTypes Elem x)))) outs (map value_tensor_type (graph_outputs m))]
end.

Definition model_well_formed (m : ModelProto) : bool :=
  (graph_of m).

Definition sized_model (d : NetworkType Elem) : eqType :=
  { m : ModelProto | network_dim_match m d && graph_of m}.

Definition nodeOutput (y : NetworkType Elem) (m' : sized_model y) (s : string)
(d : TensorType Elem) : eqType :=
match m' with
| exist m _ =>
    { v : ValueInfoProto | (v \in model_values m) && (value_info_name v == s) &&
                             (value_tensor_type v == Some (tag (tensorTypes _ d)))}
end.

Definition producing_node (m : ModelProto) (u : string) : NodeProto :=
  let nds := graph_nodes m in
  nth default_NodeProto nds (find (fun n => u \in node_output_names n) nds).

(*
A function that maps a model to a list of its outputs.
For every declared output type at position i in the network shape y, this
looks up the model's actual list of graph outputs (ModelProto -> GraphProto
-> list ValueInfoProto) at that same position, and pairs that output's name
with the NodeProto that produces it.
*)
int32_of_Z

Definition emptyValueInfoProto : ValueInfoProto :=
  ValueInfoProto_constructor None None None nil.

(** The network type's outputs line up one-to-one with the graph outputs. **)
Lemma network_dim_match_size {y : NetworkType Elem} {m : ModelProto} :
  network_dim_match m y -> size (outputs Elem y) = size (graph_outputs m).
Proof.
case: y => [[inps Hin] [outs Hout]] /= /and4P [_ _ _].
by rewrite all2E size_map => /andP [/eqP].
Qed.

(** The graph output at the same position as the i-th declared output. **)
Definition mOutput_value {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) : ValueInfoProto :=
  tnth (in_tuple (graph_outputs m)) (cast_ord (network_dim_match_size H) i).

Lemma mOutput_valueP {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) :
  let v := mOutput_value H i in
  (v \in model_values m) && (value_info_name v == value_info_name v) &&
    (value_tensor_type v == Some (projT1 (tensorTypes _ (tnth (in_tuple (outputs Elem y)) i)))).
Proof.
rewrite /mOutput_value eqxx andbT.
move: (network_dim_match_size H) => E; move: i E H.
case: y => [[inps Hin] [outs Hout]] /= i E /and4P [_ outsub _].
rewrite all2E size_map => /andP [_ /all_nthP outsame].
have /(mem_subseq outsub) -> /= :
  tnth (in_tuple (graph_outputs m)) (cast_ord E i) \in graph_outputs m := mem_tnth _ _.
set v := tnth (in_tuple (graph_outputs m)) (cast_ord E i).
set o := tnth (in_tuple outs) i.
have := outsame (o, value_tensor_type v) i.
rewrite nth_zip_cond size_zip size_map -[in minn _ _]E minnn ltn_ord /= => /(_ isT) /eqP.
rewrite (nth_map v) -?E // -[nth o outs i](tnth_nth o (in_tuple outs) i).
rewrite -[nth v _ i](tnth_nth v (in_tuple (graph_outputs m)) (cast_ord E i)) -/v -/o.
by move=> ->.
Qed.

(** For each out in the graphproto.outputs, find the valueInfoProto  **)
Definition mOutputs (y : NetworkType Elem) (m : sized_model y) :
  {dffun forall i : 'I_(size (outputs Elem y)),
 {u : string & nodeOutput y m u (tnth (in_tuple (outputs Elem y)) i)}} :=
  match m as m0 return
    {dffun forall i : 'I_(size (outputs Elem y)),
      {u : string & nodeOutput y m0 u (tnth (in_tuple (outputs Elem y)) i)}}
  with
  | exist m0 H =>
      finfun (fun i : 'I_(size (outputs Elem y)) =>
        let v := mOutput_value (andP H).1 i in
        existT _ (value_info_name v) (exist _ v (mOutput_valueP (andP H).1 i)))
  end.

(** TODO: mOutputs and nodeOutput are wrong. NodeOutput should only be
constructable if there is a node output and modl output should only contain
valid model output. Fix Model so that it holds enough information to construct
this. NodeOutput should be an inductive type that points to constructors **)

(** Ignores renaming and reordering, graph isomorphism problem. **)
Definition is_iso (y1 y2 : NetworkType Elem) (m1 : sized_model y1)
(H : NetworkShapesMatch y1 y2) (m2 : sized_model y2) : bool :=
match m1, m2 with
| exist (ModelProto_constructor _ _ _ _ _ _ _ x _ _ _ _) _,
  exist (ModelProto_constructor _ _ _ _ _ _ _ x' _ _ _ _) _ =>
    match x, x' with
    | Some y, Some y' =>
        match y, y' with
        | GraphProto_constructor n _ _ _ _ _ _ _ _ _,
          GraphProto_constructor n' _ _ _ _ _ _ _ _ _ => n == n'
        end
    | _, _ => false
    end
end.

Definition int64_to_dim (i : int64) : nat := Z.to_nat (Z_of_int64 i).

(* does p's actual dims list match the declared shape d? *)
Definition dims_match (p : TensorProto) (d : {k : nat & {posnum nat} ^ k}) : bool :=
  match p, d with
  | TensorProto_constructor dims _ _ _ _ _ _ _ _ _ _ _ _ _ _, existT _ shape =>
      map int64_to_dim dims == map (fun q : {posnum nat} => q%:num) (tval shape)
  end.

Definition Tensor_has_type (t : TensorProto) (x : DataType_TensorProto) : bool :=
match t with
| TensorProto_constructor _ (Some data_type) _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    match (DataType_TensorProto_of_int32 data_type) with
    | Some y => x == y
    | _ => false
    end
| _ => false
end.

Definition tensorProtoSized (t : TensorProto) : bool :=
match t with
| TensorProto_constructor dims (Some data_type) _ float_data int32_data _ int64_data _
    _ _ _ _ _ _ _ =>
    match DataType_TensorProto_of_int32 data_type with
    | Some FLOAT_TensorProto => size float_data == \prod_(i < size [seq int64_to_dim i | i <- dims]) tnth (in_tuple (map int64_to_dim dims)) i
    | Some INT32_TensorProto => size int32_data == \prod_(i < size [seq int64_to_dim i | i <- dims]) tnth (in_tuple (map int64_to_dim dims)) i
    | Some INT64_TensorProto => size int64_data == \prod_(i < size [seq int64_to_dim i | i <- dims]) tnth (in_tuple (map int64_to_dim dims)) i
    | _ => false
    end
| _ => false
end.

Definition sized_tensor (t : TensorType Elem) : eqType :=
  { p : qTensor | dims_match p (tensorDims _ t) && Tensor_has_type p (tag (tensorTypes _ t)) && tensorProtoSized p}.

Definition syntax_inst : NetworkTheorySyntax :=
  {|
      ElementType := Elem;
      TheoryTensor := sized_tensor;
      Model := sized_model;
      NodeOutputName := string;
      NodeOutput := nodeOutput;
      modelOutputs := mOutputs;
      iso := is_iso;
  |}.
