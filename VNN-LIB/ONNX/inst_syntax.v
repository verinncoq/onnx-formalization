From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import boot algebra order reals Rstruct.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Lia Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst real.
From ONNXFormalization.VNNLIB.ONNX Require Export well_formed_model.
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

Definition default_NodeProto : NodeProto :=
  NodeProto_constructor nil nil None None None None nil None nil nil.

Definition graph_nodes (m : ModelProto) : list NodeProto :=
  match graph_of m with
  | Some (GraphProto_constructor nds _ _ _ _ _ _ _ _ _) => nds
  | None => nil
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

Definition has_value_tensor_type (v : ValueInfoProto) : bool :=
  match value_tensor_type v with
  | Some _ => true
  | _ => false
  end.

Lemma isSuccess_map' {T1 T2} (f : T1 -> error_option T2) (xs : seq T1) (ys : seq T2)
  : isSuccess (list_error_option_to_error_option_list (ListDef.map f xs) ys) = all isSuccess (map f xs).
elim: xs ys => //= x xs IHxs ys.
by case: (f x) => //= t.
Qed.

Definition find_vertex_bounded (items : seq vertex) (s : string)
                               (H : size (find_vertex items s) == 1%N)
  : vertex := tnth (in_tuple (find_vertex items s)) (cast_ord (esym (eqP H)) ord0).

Lemma mem_app {T : eqType} (x : T) (s1 s2 : seq T) :
  (x \in (s1 ++ s2)%list) = (x \in s1) || (x \in s2).
Proof. by rewrite app_cat mem_cat. Qed.

Lemma topo_sorted_in defined nodes n i :
  topo_sorted defined nodes -> n \in nodes -> i \in node_inputs n ->
  (i \in flatten (map node_outputs (rev nodes)) ++ defined)%SEQ &&
    (i \notin node_outputs n).
Proof.
elim: nodes defined => //= m ns IH defined /and4P [ins fresh _ ts].
rewrite in_cons => /orP [/eqP -> | nin] iin.
  have idef : i \in defined by move/allP: ins; apply.
  rewrite mem_cat idef orbT /=.
  by apply/negP => io; move/allP: fresh => /(_ i io); rewrite idef.
have := IH _ ts nin iin.
by rewrite rev_cons -cats1 map_cat flatten_cat /= cats0 -catA.
Qed.

(** Every input of a node in an acyclic graph names exactly one vertex,
    and that vertex is not the node itself. *)
Lemma graph_acyclic_find {nodes inputs initialisers n i} :
  graph_acyclic nodes inputs initialisers -> n \in nodes -> i \in node_inputs n ->
  exists2 v, find_vertex (graph_items nodes inputs initialisers) i = [:: v] &
             v != node n.
Proof.
rewrite /graph_acyclic => /andP [un ts] nin iin.
have /andP [idef inout] := topo_sorted_in _ _ _ _ ts nin iin.
have uitems : uniq (flatten (map vnames (graph_items nodes inputs initialisers))).
  by rewrite vnames_items; exact: topo_sorted_uniq.
move: idef; rewrite -vnames_items => /flattenP [ns /mapP [v vin ->] iv].
exists v; first exact: find_vertex_uniq.
by apply: contraNneq inout => vn; move: iv; rewrite vn.
Qed.

Lemma graph_acyclic_not_self_ref {nodes inputs initialisers n} :
  graph_acyclic nodes inputs initialisers -> n \in nodes ->
  not_self_ref (graph_items nodes inputs initialisers) n.
Proof.
move=> ga nin; move: (nin) => /(graph_acyclic_find ga) F.
case: n nin F => ins outs a b c d e f g h nin F /=.
rewrite all_map; apply/allP => i iin /=.
by have [v -> vn] := F i iin.
Qed.

Definition valid_pair (o1 o2 : option int32) : bool :=
  if (o1, o2) is (Some a, Some b) then
    let z := Z_of_int32 a in
    (z =? Z_of_int32 b)%Z && [|| (z =? 1)%Z, (z =? 6)%Z | (z =? 7)%Z]
  else false.

Variant valid_pair_spec (o1 o2 : option int32) : Prop :=
  | VP1 a b of o1 = Some a & o2 = Some b & Z_of_int32 a = 1%Z & Z_of_int32 b = 1%Z
  | VP6 a b of o1 = Some a & o2 = Some b & Z_of_int32 a = 6%Z & Z_of_int32 b = 6%Z
  | VP7 a b of o1 = Some a & o2 = Some b & Z_of_int32 a = 7%Z & Z_of_int32 b = 7%Z.

Lemma valid_pairP o1 o2 : valid_pair o1 o2 -> valid_pair_spec o1 o2.
Proof.
case: o1 o2 => [a|] [b|] //= /andP[/Z.eqb_spec ab /or3P[] /Z.eqb_spec za].
- by eapply VP1; [reflexivity | reflexivity | exact: za | rewrite -ab].
- by eapply VP6; [reflexivity | reflexivity | exact: za | rewrite -ab].
- by eapply VP7; [reflexivity | reflexivity | exact: za | rewrite -ab].
Qed.


Lemma match_Z0_if (A : Type) (z : Z) (a b : A) :
  match z with Z0 => a | _ => b end = if (z =? 0)%Z then a else b.
Proof. by case: z. Qed.

Lemma get_column_success {T} (a : matrix T) (n : nat)
  : all (fun x => n < size x) a ->
    isSuccess (get_column a n).
Proof.
elim: a => //= x xs IHxs /andP [sizexn alln].
move/isSuccessP: (IHxs alln) => [t ->].
move: sizexn.
rewrite -length_size.
move=> /ssrnat.ltP.
rewrite -(List.nth_error_Some x n).
by case: (List.nth_error x n).
Qed.

Definition ncols (b : matrix float32) : nat :=
  if b is row :: _ then Datatypes.length row else 0%nat.

Definition mm_ok (a b : matrix float32) : bool :=
  all (fun row => all (fun j => isSuccess (matrix_multiplicaiton_float32_helper a b row j))
                    (List.seq 0 (ncols b)))
    a.

Lemma matrix_multiplication_float_success a b :
  mm_ok a b -> isSuccess (matrix_multiplication_float32 a b).
Proof.
elim: a => [|x xs IH] //= /andP [Hrow /IH Hrec].
have /isSuccessP [r ->] :
  isSuccess (list_error_option_to_error_option_list
               (ListDef.map (matrix_multiplicaiton_float32_helper (x :: xs)%SEQ b x) (ListDef.seq 0 match b with
                                                                                        | [::] => 0
                                                                                        | (row :: _)%SEQ => Datatypes.length row
                                                                                        end))
               [::]).
rewrite isSuccess_map' /=.
rewrite all_map.
apply/allP => /= i iin.
by move/allP: Hrow => /(_ i iin).
by case/isSuccessP: Hrec => rs ->.
Qed.

Lemma matrix_float_success (t : TensorProto)
  : tensorProtoSized t -> dims_correct (get_dims t) -> tensor_dtype t = Some FLOAT_TensorProto -> isSuccess (matrix_float32_of_tensor t).
Proof.
case/tensorProtoSizedP => dims dtype seg float32 int32 bytes int64 name doc raw_data ext loc double uint64 meta -> //= datatype sized sizes.
case/dims_correctP => [|h|h w] -> /=.
have := dims_prod_pos sized.
rewrite -sizes.
by case: float32 sizes.
case: (Z_of_int64 h) => //= h' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: float32 sizes.
case: (Z_of_int64 h) => //= h' _.
case: (Z_of_int64 w) => //= w' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: float32 sizes.
by rewrite datatype.
by rewrite datatype.
Qed.

Lemma matrix_int32_success (t : TensorProto)
  : tensorProtoSized t -> dims_correct (get_dims t) -> tensor_dtype t = Some INT32_TensorProto -> isSuccess (matrix_int32_of_tensor t).
Proof.
case/tensorProtoSizedP => dims dtype seg float32 int32 bytes int64 name doc raw_data ext loc double uint64 meta -> //= datatype sized sizes.
by rewrite datatype.
case/dims_correctP => [|h|h w] -> /=.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int32 sizes.
case: (Z_of_int64 h) => //= h' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int32 sizes.
case: (Z_of_int64 h) => //= h' _.
case: (Z_of_int64 w) => //= w' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int32 sizes.
by rewrite datatype.
Qed.

Lemma matrix_int64_success (t : TensorProto)
  : tensorProtoSized t -> dims_correct (get_dims t) -> tensor_dtype t = Some INT64_TensorProto -> isSuccess (matrix_int64_of_tensor t).
Proof.
case/tensorProtoSizedP => dims dtype seg float32 int32 bytes int64 name doc raw_data ext loc double uint64 meta -> //= datatype sized sizes.
by rewrite datatype.
by rewrite datatype.
case/dims_correctP => [|h|h w] -> /=.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int64 sizes.
case: (Z_of_int64 h) => //= h' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int64 sizes.
case: (Z_of_int64 h) => //= h' _.
case: (Z_of_int64 w) => //= w' _.
have := dims_prod_pos sized.
rewrite -sizes.
by case: int64 sizes.
Qed.

Variant broadcastable_matrix_spec {T} (dim1_a dim2_a : nat) (dims_b : seq nat)
  (b : matrix T)
  : Prop :=
  | BM_scalar k of b = [:: [:: k]] &
      dims_b = [::] &
      broadcast_2d dim1_a dim2_a dims_b b = Success (nseq dim1_a (nseq dim2_a k))
  | BM_vector d n of @broadcastable_vector T dim1_a dim2_a d &
      dims_b = [:: n] &
      broadcast_2d dim1_a dim2_a dims_b b = broadcast_2d_vector dim1_a dim2_a b
  | BM_row d n of @broadcastable_vector T dim1_a dim2_a d &
      dims_b = [:: 1%nat; n] &
      broadcast_2d dim1_a dim2_a dims_b b = broadcast_2d_vector dim1_a dim2_a b
  | BM_col d n of @broadcastable_vector T dim1_a dim2_a d &
      dims_b = [::n; 1%nat] &
      broadcast_2d dim1_a dim2_a dims_b b = broadcast_2d_vector dim1_a dim2_a b
  | BM_full dim1_b dim2_b of dims_b = [:: dim1_b; dim2_b] &
      (dim1_a =? dim1_b)%nat &
      (dim2_a =? dim2_b)%nat &
      broadcast_2d dim1_a dim2_a dims_b b = Success b.

Lemma broadcastable_matrixP {T} dim1_a dim2_a dims_b (b : matrix T) :
  broadcastable_matrix dim1_a dim2_a dims_b b ->
  broadcastable_matrix_spec dim1_a dim2_a dims_b b.
Proof.
case: dims_b => [|d1 [|d2 [|d3 ds]]].
- case: b => [|[|k [|? ?]] [|? ?]] //= _.
  apply/BM_scalar; try by apply: erefl.
  by rewrite /= !repeat_is_nseq.
- move=> /= H; apply (BM_vector _ _ _ _ _ d1 H erefl).
  rewrite /=.
  by case: d1=> //; case.
- case: d1 => [|[|d1]]; case: d2 => [|[|d2]] => /= H.
  move/andP: H => [H H'].
  apply (BM_full _ _ _ _ _ _ erefl H H') => /=.
  by rewrite H H'.
  apply/BM_col/erefl/erefl/H.
  move/andP: H => [H H'].
  apply (BM_full _ _ _ _ 0%nat d2.+2%nat) => //.
  by rewrite /= H H'.
  by apply: BM_row; [ by apply: H | by apply: erefl | ].
  by apply: BM_row; [ by apply: H | by apply: erefl | ].
  by apply: BM_row; [ by apply: H | by apply: erefl | ].
  move/andP: H => [H H'].
  apply (BM_full _ _ _ _ d1.+2%nat 0%nat) => //.
  by rewrite /= H H'.
  by apply: BM_col; [ by apply: H | by apply: erefl | ].
  move/andP: H => [H H'].
  apply (BM_full _ _ _ _ d1.+2%nat d2.+2%nat) => //=.
  by rewrite /= H H'.
- by case: d1 => [|[|d1]]; case: d2 => [|[|d2]].
Qed.

Definition cycle_free (m : ModelProto) : bool :=
  if m is ModelProto_constructor _ _ _ _ _ _ _ (Some graph) _ _ _ _ then
  let : GraphProto_constructor nodes _ initialisers _ _ inputs outputs _ _ _ := graph in
  let items := ([seq node x0 | x0 <- List.rev nodes] ++ [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers])%SEQ in
  all (not_self_ref items) nodes
  else false.

Definition one_element {T} (xs : seq T) : bool :=
  if xs is [:: k] then true else false.

Lemma one_elementP {T} (xs : seq T) : one_element xs -> exists x, xs = [:: x].
Proof.
by case: xs => //= x [|//]; exists x.
Qed.

(** Two successful evaluations over the same leaves produce matching tensors. *)
Lemma eval_tensors_match d xs items v w t t' dt :
  all (fun u => tensor_dtype u == Some dt) xs ->
  (forall u, tensor u \in items -> tensor_dtype u = Some dt) ->
  v \in items -> w \in items ->
  onnx_evaluator_recursive d xs items v = Success t ->
  onnx_evaluator_recursive d xs items w = Success t' ->
  tensors_match [:: t; t'].
Proof.
move=> Dx Di vin win Ev Ew.
have Dv u : u \in items -> forall t'', tensor t'' \in u :: items -> tensor_dtype t'' = Some dt.
  move=> uin t''; rewrite in_cons => /orP [/eqP tu|]; apply: Di => //.
  by rewrite tu.
by rewrite /= (eval_dtype _ _ _ _ _ _ Dx (Dv _ vin) Ev) (eval_dtype _ _ _ _ _ _ Dx (Dv _ win) Ew) eqxx.
Qed.

(* Definition value_name_unique (v : ValueInfoProto) : bool := *)
(*   if v is Some s then uniq ( *)

(* Open Scope seq_scope. *)
(* Lemma listfilter_is_filter {T} (f : T -> bool) (xs : seq T) : List.filter f xs = [seq x <- xs | f x]. *)
(* Proof. by elim: xs. Qed. *)

(* Lemma filter_unique_name (T : Type) (name : T -> string) (s : seq T) (n : string) : *)
(*   uniq (map name s) -> n \in map name s -> *)
(*   exists y, [seq x <- s | name x == n] = [:: y]. *)
(* Proof. *)
(* move=> Huniq Hin. *)
(* have Hsize : size [seq x <- s | name x == n] = 1%nat. *)
(* rewrite size_filter. *)
(* have -> : count (fun x => name x == n) s = count (pred1 n) (map name s). *)
(* by rewrite count_map. *)
(* by rewrite count_uniq_mem // Hin. *)
(* by case: [seq x <- s | name x == n] Hsize => [|y [|z t]] // _; exists y. *)
(* Qed. *)

(* Variant graph_of_spec (m : ModelProto) : Prop := *)
(*   | Graph ir ops prod_n prod_v domain model_v doc graph meta training funcs config g_nodes g_name g_initialisers g_sparse g_doc g_input g_output g_values g_quant g_meta vertices of *)
(*       m = ModelProto_constructor ir ops prod_n prod_v domain model_v doc (Some graph) meta training funcs config & *)
(*       graph = GraphProto_constructor g_nodes g_name g_initialisers g_sparse g_doc g_input g_output g_values g_quant g_meta & *)
(*       vertices = [seq node x | x <- List.rev g_nodes] ++ [seq input x | x <- g_input] ++ [seq tensor x | x <- g_initialisers] & *)
(*       all value_name g_output & *)
(*       uniq [seq vnames v | v <- vertices]. *)
(*       (* all (fun x_name => if [seq x <- vertices | vertex_has_name x_name x] is [:: v] then true else false) [seq value_info_name x | x <- g_output]. *) *)

(* Definition test (m : ModelProto) : bool := *)
(*   graph_of m. *)

(* Lemma graph_ofP {m : ModelProto} : test m -> graph_of_spec m. *)
(* Admitted. *)
(* (* Proof. *) *)
(* (* case: m => ir ops prod_n prod_v domain model_v doc [[g_nodes g_name g_initialisers g_sparse g_doc g_input g_output g_values g_quant g_meta]|//] meta training funcs config H. *) *)
(* (* by apply: (Graph _ ir ops prod_n prod_v domain model_v doc (GraphProto_constructor g_nodes g_name g_initialisers g_sparse g_doc g_input g_output g_values g_quant g_meta)  meta training funcs config). *) *)
(* (* Qed. *) *)
(* (* [&& graph_of m]. *) *)

(* Lemma well_formed_computes (m : ModelProto) (xs : seq TensorProto) : *)
(*   test m -> isSuccess (onnx_evaluator m xs). *)
(* Proof. *)
(* rewrite /onnx_evaluator. *)
(* case/graph_ofP => ir ops prod_n prod_v domain model_v doc graph meta training funcs config g_nodes g_name g_initialisers g_sparse g_doc g_input g_output g_values g_quant g_meta vertices mis gis vertices_is /allP all_outputs_named /uniqP /= vnames_unique. *)
(* rewrite mis gis. *)
(* rewrite !listmap_map !length_size isSuccess_map !app_cat -vertices_is. *)
(* rewrite all_map. *)
(* apply/allP => /= [[]] x; *)
(* case/mapP => //= out outin outx. *)
(* move: outx outin => [] <- xin {out}. *)
(* move: (all_outputs_named x xin). *)
(* case: x xin => //= [[]] // x_name x_type x_doc x_meta xin _. *)
(* rewrite !listfilter_is_filter. *)
(* move: vnames_unique => /(_ [seq vnames x | x <- vertices]). *)



Definition nodeOutput (y : NetworkType Elem) (m' : well_formed_model y) (s : string)
(d : TensorType Elem) : eqType :=
match m' with
| exist m _ =>
    { v : ValueInfoProto |
      [&& v \in graph_outputs m, value_info_name v == s & value_has_type d v]}
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

(** The network type's outputs line up one-to-one with the graph outputs. **)
Lemma network_dim_match_size {y : NetworkType Elem} {m : ModelProto} :
  network_dim_match m y -> size (outputs Elem y) = size (graph_outputs m).
Proof.
case: y => [[inps Hin] [outs Hout]] /= /and4P [_ _ _].
by rewrite all2E => /andP [/eqP].
Qed.

(** The graph output at the same position as the i-th declared output. **)
Definition mOutput_value {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) : ValueInfoProto :=
  tnth (in_tuple (graph_outputs m)) (cast_ord (network_dim_match_size H) i).

Lemma mOutput_valueP {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (outputs Elem y))) :
  let v := mOutput_value H i in
  let d := tnth (in_tuple (outputs Elem y)) i in
  [&& v \in graph_outputs m, value_info_name v == value_info_name v & value_has_type d v].
Proof.
rewrite /mOutput_value eqxx /=.
move: (network_dim_match_size H) => E; move: i E H.
case: y => [[inps Hin] [outs Hout]] /= i E /and4P [_ outsub _].
rewrite all2E => /andP [_ /all_nthP outsame].
rewrite mem_tnth /=.
set v := tnth (in_tuple (graph_outputs m)) (cast_ord E i).
set o := tnth (in_tuple outs) i.
have := outsame (o, v) i.
rewrite nth_zip_cond size_zip -[in minn _ _]E minnn ltn_ord /= => /(_ isT).
rewrite -[nth o outs i](tnth_nth o (in_tuple outs) i).
rewrite -[nth v _ i](tnth_nth v (in_tuple (graph_outputs m)) (cast_ord E i)) -/v -/o.
by move=> ->.
Qed.

(** For each out in the graphproto.outputs, find the valueInfoProto  **)
Definition mOutputs (y : NetworkType Elem) (m : well_formed_model y) :
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
Definition is_iso (y1 y2 : NetworkType Elem) (m1 : well_formed_model y1)
(H : NetworkShapesMatch y1 y2) (m2 : well_formed_model y2) : bool :=
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

Definition syntax_inst : NetworkTheorySyntax :=
  {|
      ElementType := Elem;
      TheoryTensor := sized_tensor;
      Model := well_formed_model;
      NodeOutputName := string;
      NodeOutput := nodeOutput;
      modelOutputs := mOutputs;
      iso := is_iso;
  |}.
