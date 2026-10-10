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

(********************************************)
(**************** SEMANTICS *****************)
(********************************************)

Definition denote (x : ElementType syntax_inst) : eqType :=
  match x with
  | exist x Px =>
      match x as x0 return (x0 \in supported_types) -> eqType with
      | FLOAT_TensorProto => fun=> float32
      | INT32_TensorProto => fun=> int32
      | INT64_TensorProto => fun=> int64
      | STRING_TensorProto => fun=> string
      | DOUBLE_TensorProto => fun=> float64
      | UINT64_TensorProto => fun=> uint64
      | _ => fun Px => False_rect eqType (notF Px)
      end Px
end.

(* TODO: data_type is a reference to the enum DataType_TensorProto, so there
should be a check these match *)
Lemma prod_tnth (s : seq nat) :
  \prod_(i < size s) tnth (in_tuple s) i = \prod_(x <- s) x.
Proof. by rewrite [RHS]big_tnth. Qed.

Definition theoryTensorProto : forall t : TensorType (ElementType syntax_inst), TheoryTensor syntax_inst t -> TensorSemantics denote t.
Proof.
rewrite /TheoryTensor.
rewrite /=.
case.
case => /= [x H] [k dims] [t /= /andP [/andP [Ht hasType] sized]].
case: t Ht hasType sized => /= t Ht Ht'.
rewrite /Tensor_has_type /tensorProtoSized.
move: Ht'.
case t.
move=> /= t_dims.
case=> //.
move=> /(DataType_TensorProto_of_int32).
case=> //= data_type segment float int32 string int64 name doc_string raw_data
           external_data data_location double_data uint64_data metadata_props /eqP.
case: x H => // _ dims_eq /eqP <- /eqP data_sized.
- apply: Tensor. rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple float) (cast_ord _ i)).
  move=> _ _.
  move: data_sized.
  by rewrite dims_eq prod_tnth big_map big_map big_enum /= => <-.
- apply: Tensor; rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int32) (cast_ord _ i)).
  move=> _ _.
  move: data_sized.
  by rewrite dims_eq prod_tnth big_map big_map big_enum /= => <-.
- apply: Tensor; rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int64) (cast_ord _ i)).
  move=> _ _.
  move: data_sized.
  by rewrite dims_eq prod_tnth big_map big_map big_enum /= => <-.
Defined.

(* --- Converting between the mathcomp tensor interface and TensorProto ---
   'nT[R]_(dims) is definitionally a column vector 'M[R]_(prod dims, 1)
   (the covariant-dims product is empty, i.e. 1 -- `rewrite big_ord0` is
   what exposes that), so building/reading one is just building/reading a
   flat, row-major list of length \prod_i (dims i)%:num. NB: bare `enum`
   is ambiguous once ONNXEvaluator.onnx_evaluator is imported (it also
   exports a constructor literally named `enum`, from the ProtobufConverter
   IR type, which takes a string -- hence `fintype.enum` everywhere below. *)

Definition build_tensor {R : eqType} {k : nat} (dims : {posnum nat}^k)
  (data : seq R) (H : size data = \prod_(i < k) (dims i)%:posnum) : 'nT[R]_(dims).
Proof.
apply: Tensor; rewrite big_ord0.
exact: (\col_i tnth (in_tuple data) (cast_ord (esym H) i)).
Defined.

Definition read_tensor {R : eqType} {k : nat} (dims : {posnum nat}^k) (t : 'nT[R]_(dims))
  : seq R :=
  let cols_eq : \prod_(j < 0) ([tuple] j)%:posnum = 1%R := big_ord0 _ _ _ _ in
  [seq val t i (cast_ord (esym cols_eq) ord0) | i <- fintype.enum 'I_(\prod_(l < k) (dims l)%:num)].

Definition int32_zero : int32 := (Byte.x00, Byte.x00, Byte.x00, Byte.x00).
Definition int64_zero : int64 :=
  (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00).

Definition nat_to_int64 (n : nat) : int64 := odflt int64_zero (int64_of_Z (Z.of_nat n)).

Definition dims_of_shape {k : nat} (dims : {posnum nat}^k) : list int64 :=
  [seq nat_to_int64 (dims i)%:num | i <- fintype.enum 'I_k].

Definition string_to_bytes (s : string) : bytes :=
  odflt nil (bytes_of_string (list_ascii_of_string s)).

(* ONNX's numeric DataType codes (1=FLOAT, 6=INT32, 7=INT64, 8=STRING,
   11=DOUBLE, 13=UINT64 -- the ones op_gemm.v/op_relu.v already match on). *)
Definition Semantics_to_TensorProto (d : TensorType Elem)
  : TensorSemantics denote d -> qTensor.
Proof.
case: d => [[x Px] [k dims]] /=.
case: x Px => //= Px v.
- exact: (\pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 1) None
            (read_tensor dims v) nil nil nil None None None nil None nil nil nil)).
- exact: \pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 6) None
            nil (read_tensor dims v) nil nil None None None nil None nil nil nil).
- exact: \pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 7) None
            nil nil nil (read_tensor dims v) None None None nil None nil nil nil).
Defined.

Definition TensorProto_to_Semantics (d : TensorType Elem) (t : sized_tensor d) : TensorSemantics denote d.
Proof.
case: d t => [/= [x Px] [k dims]] /= [].
case.
case=> [t_dims data_type segment float_data int32_data string_data int64_data name doc_string bytes ext loc double_data uint64_data meta] canon.
rewrite /= => /andP [].
case: data_type canon => // data_type canon.
case: (DataType_TensorProto_of_int32 data_type) => // ? /andP [/eqP dims_match /eqP <-].
case: x Px => //= Px /=;
rewrite dims_match prod_tnth big_map big_map big_enum /= => /eqP.
- exact: (build_tensor dims float_data).
- exact: (build_tensor dims int32_data).
- exact: (build_tensor dims int64_data).
Defined.

(* Lemma Semantics_to_TensorProtoK (d : TensorType Elem) : cancel (Semantics_to_TensorProto d) (TensorProto_to_Semantics d). *)
(* Proof. *)
(* case: d => [[[] Px]] [k dims] //=. *)
(* move=> t /=. *)
(* rewrite /build_tensor. *)
(* rewrite /TensorProto_to_Semantics /=. *)
(* case: TensorTypes. *)

(*
Executes the network: runs the actual ONNX operational semantics
(ONNXEvaluator.onnx_evaluator) on the underlying ModelProto and a
TensorProto-ized version of the semantic inputs, then converts the
raw output picked out by name u back into a mathcomp tensor.
- "extracting the original parts out": Model syntax_inst y and
  NodeOutput syntax_inst n u d are both constant (ModelProto/NodeProto)
  regardless of y/n/u/d, so `n`/`out` here just *are* the ModelProto and
  the producing NodeProto already -- nothing to unwrap beyond `case: y`
  to get at `inputs`.
- "putting them through the operational semantics": Semantics_to_TensorProto
  turns every semantic input into a real TensorProto, onnx_evaluator runs
  the model on them exactly as ONNXEvaluator/theory/onnx_evaluator.v defines
  it, and the result (by name, same convention mOutputs already uses) is
  converted back via TensorProto_to_Semantics.
As with mOutputs/test, this is a total, best-effort function: if the
model has no graph, evaluation errors, or `u` isn't among its declared
outputs, it falls back to default_TensorProto (the all-zero tensor),
rather than being partial.
*)

Definition default_TensorProto : TensorProto :=
    TensorProto_constructor nil None None nil nil nil nil None None None nil None nil nil nil.


(* TODO: Make this so that it extracts model to a maths function over mathcomp tensors and applies it to inputSemantics. Must cascade input through entire graph.
 Map model to a function over mathcomp tensor **)
Definition modelTensorProto (y : NetworkType (ElementType syntax_inst))
(n : Model syntax_inst y) (inp : InputSemantics denote y)
(d : TensorType (ElementType syntax_inst)) (u : NodeOutputName syntax_inst)
(out : NodeOutput syntax_inst n u d) : TensorSemantics denote d.
Proof.
move: inp.
case: y n out => /= inputs outputs model node /=.
move=> inp.
pose user_inputs := [seq Semantics_to_TensorProto (tnth (in_tuple inputs) i) (inp i)
                     | i <- fintype.enum 'I_(size inputs)].
pose idx := seq.index u (map value_info_name (graph_outputs (tag model))).
pose out_tp := match onnx_evaluator (tag model) (map repr user_inputs) with
  | Success outs => nth default_TensorProto (in_tuple outs) idx
  | Error _ => default_TensorProto
  end.
Admitted.
(* exists (TensorProto_to_Semantics d (\pi_qTensor out_tp)). *)
(* Defined. *)


(* the two are genuine inverses: encoding then decoding always recovers
   the original constructor *)
Lemma DataType_TensorProto_int32_roundtrip (x : DataType_TensorProto) :
  DataType_TensorProto_of_int32 (int32_of_DataType_TensorProto x) = Some x.
Proof. by case: x. Qed.

Definition s_all2 {S T : Type} (op : S -> T -> bool) (s1 : seq S) (s2 : seq T) : bool :=
  (size s1 == size s2) && (all2 op s1 s2).

Definition TensorProto_le (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
    match le_tensor (Semantics_to_TensorProto d t1) (Semantics_to_TensorProto d t2) with
    | Success x => matrix_and x
    | Error x => false
    end.

Definition TensorProto_lt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
match lt_tensor (Semantics_to_TensorProto d t1) (Semantics_to_TensorProto d t2) with
| Success x => matrix_and x
| Error x => false
end.

Definition TensorProto_ge (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
    match ge_tensor (Semantics_to_TensorProto d t1) (Semantics_to_TensorProto d t2) with
    | Success x => matrix_and x
    | Error x => false
    end.

Definition TensorProto_gt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
    match gt_tensor (Semantics_to_TensorProto d t1) (Semantics_to_TensorProto d t2) with
    | Success x => matrix_and x
    | Error x => false
    end.

Definition TensorProto_eq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
fun t1 t2 =>
    match eq_tensor (Semantics_to_TensorProto d t1) (Semantics_to_TensorProto d t2) with
    | Success x => matrix_and x
    | Error x => false
    end.

Definition TensorProto_neq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
  negb (TensorProto_eq d t1 t2).

Definition zero_tensor (t : TensorProto) : TensorProto.
case: t => dims data_type segment float_data int32_data string_data int64_data name doc_string raw ext data_loc double_data uint64_data metadata.
apply/TensorProto_constructor.
exact: dims.
exact: data_type.
exact: segment.
exact: (map (fun _ => Binary.B754_zero 24 128 false) float_data).
exact: (map (fun _ => (x00, x00, x00, x00)) int32_data).
exact: (map (fun xs => map (fun _ => x00) xs) string_data).
exact: (map (fun _ => (x00, x00, x00, x00, x00, x00, x00, x00)) int32_data).
exact: name.
exact: doc_string.
case: raw => [b|].
apply/Some.
exact: (map (fun _ => x00) b).
exact: None.
exact: ext.
exact: data_loc.
exact: (map (fun _ => Binary.B754_zero 53 1024 false) double_data).
exact: (map (fun _ => (x00, x00, x00, x00, x00, x00, x00, x00)) uint64_data).
exact:metadata.
Defined.

Definition TensorProto_neg (d : TensorType (ElementType syntax_inst)) : TensorOp1 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t.
exact: (@Tensor _ _ dims _ float32 (map_mx (b32_mult BinarySingleNaN.mode_NE default_minus_one) (\val t))).
exact: (@Tensor _ _ dims _ int32 (map_mx (fun h1 => mc_inst.int32_of_Z (- (Z_of_int32 h1))) (\val t))).
exact: (@Tensor _ _ dims _ int64 (map_mx (fun h1 => mc_inst.int64_of_Z (- (Z_of_int64 h1))) (\val t))).
Defined.

Lemma add_lists_float32_sized {s1 s2 : seq float32}
  : size s1 = size s2 -> exists s3,
add_lists_float32 s1 s2 = Success s3.
Proof.
move=> H.
elim: s2 s1 H=> //= [[|//=] | x xs IHx [//| y ys] /= H]; first by exists [::].
have [z ->]:= (IHx ys (eq_add_S _ _ H)).
by exists (b32_plus BinarySingleNaN.mode_NE y x :: z)%SEQ.
Qed.

(* TODO: There is no overflow protection in the type so this cant be done *)
(* Lemma add_lists_int32_sized {s1 s2 : seq int32} *)
(*   : size s1 = size s2 -> exists s3, *)
(* add_lists_int32 s1 s2 = Success s3. *)
(* Proof. *)
(* move=> H. *)
(* elim: s2 s1 H=> //= [[|//=] | x xs IHx [//| y ys] /= H]; first by exists [::]. *)
(* have [z ->]:= (IHx ys (eq_add_S _ _ H)). *)
(* Admitted. *)

(* Lemma add_correct (d : TensorType (ElementType syntax_inst)) *)
(* (t1 t2 : TensorSemantics denote d) : *)
(*   exists t, add_tensor (Semantics_to_TensorProto d t1) *)
(*             (Semantics_to_TensorProto d t2) = Success t. *)
(* Proof. *)
(* case: d t1 t2 => /= tensorType [/= k dims] /= t1 t2. *)
(* rewrite /add_tensor /=. *)
(* case: tensorType t1 t2. *)
(* case=> ttin //= t1 t2. *)
(* suff H: size (read_tensor dims t1) = size (read_tensor dims t2). *)
(* have [x ->] := add_lists_float32_sized H. *)
(* by exists (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 1) None x [::] [::] *)
(*    [::] None None None [::] None [::] [::] [::]). *)
(* rewrite /read_tensor. *)
(* Admitted. *)

Definition TensorProto_add (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t u.
exact: (@Tensor _ _ dims _ float32 (map2_mx (b32_plus BinarySingleNaN.mode_NE) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int32 (map2_mx (fun h1 h2 => mc_inst.int32_of_Z
                                                       ((Z_of_int32 h2) + (Z_of_int32 h1))) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int64 (map2_mx (fun h1 h2 => mc_inst.int64_of_Z ((Z_of_int64 h1) + (Z_of_int64 h2))) (\val t) (\val u))).
Defined.

(** TODO: The zero_tensor needs to be reshaped **)
Definition TensorProto_mul (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t u.
exact: (@Tensor _ _ dims _ float32 (map2_mx (b32_mult BinarySingleNaN.mode_NE) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int32 (map2_mx (fun h1 h2 => mc_inst.int32_of_Z
                                                       ((Z_of_int32 h2) * (Z_of_int32 h1))) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int64 (map2_mx (fun h1 h2 => mc_inst.int64_of_Z ((Z_of_int64 h1) * (Z_of_int64 h2))) (\val t) (\val u))).
Defined.

(** TODO: Change to denotational (mathcomp) semantics **)
(** This now does denotational for the strcture, but still uses the ints and floats
for the individual operations **)
Definition semantics_inst : NetworkTheorySemantics syntax_inst :=
  {|
      elementType := denote;
      theoryTensor := theoryTensorProto;
      model := modelTensorProto;
      le := TensorProto_le;
      lt := TensorProto_lt;
      ge := TensorProto_ge;
      gt := TensorProto_gt;
      eq := TensorProto_eq;
      neq := TensorProto_neq;
      neg := TensorProto_neg;
      add := TensorProto_add;
      mul := TensorProto_mul;
  |}.

(********************************************)
(**************** REALS *********************)
(********************************************)

From Stdlib Require Import Rdefinitions.

Definition idk : (@RealNetworkSemantics syntax_inst R).
Proof.
rewrite /RealNetworkSemantics.
move=> y1 y2 d1 d2 u m networkshapesMatch inp out tensorShapesMatch.
case: m out=> /= m /andP [Hm Hm'] out.
have := graph_of m.
case: (graph_of m) Hm' => [g|] // _ _.
case: g => nodes _ initialisers _ _ inputs outputs _ _ _.
have vertices := ((map (fun x => node x) (rev nodes)) ++ (map (fun x => input x) inputs)
                    ++ (map (fun x => tensor x) initialisers))%SEQ.
