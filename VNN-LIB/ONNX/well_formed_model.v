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
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

Definition supported_types : seq DataType_TensorProto :=
  [:: FLOAT_TensorProto; INT32_TensorProto; INT64_TensorProto].

Definition Elem : eqType := { x in supported_types }.

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

Definition model_values (m : ModelProto) : list ValueInfoProto :=
  match graph_of m with
  | Some (GraphProto_constructor _ _ _ _ _ _ _ values _ _) => values
  | _ => nil
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

(** The concrete dims a value declares, provided every dimension is a dim_value. *)
Definition value_dims (v : ValueInfoProto) : option (seq int64) :=
  let: ValueInfoProto_constructor _ ty _ _ := v in
  if ty is Some (TypeProto_constructor (Some (tensor_type_value_TypeProto
       (Tensor_TypeProto_constructor _ (Some (TensorShapeProto_constructor ds))))) _) then
    let dv d := if d is Dimension_TensorShapeProto_constructor
                          (Some (dim_value_value_Dimension_TensorShapeProto i)) _
                then Some i else None in
    if all (fun d => isSome (dv d)) ds then Some (pmap dv ds) else None
  else None.

Definition int64_to_dim (i : int64) : nat := Z.to_nat (Z_of_int64 i).

(** A declared value has the dtype and the dims of a network tensor type. *)
Definition value_has_type (x : TensorType Elem) (v : ValueInfoProto) : bool :=
  (value_tensor_type v == Some (tag (tensorTypes _ x))) &&
  (omap (map int64_to_dim) (value_dims v) ==
   Some (map (fun q : {posnum nat} => q%:num) (tval (projT2 (tensorDims _ x))))).

(** The model's graph inputs and outputs have the types of the network type. *)
Definition network_dim_match (m : ModelProto) (n : NetworkType Elem) : bool :=
match n with
| networkType (exist inps inpsgt0) (exist outs outsgt0) =>
    [&& (subseq (graph_inputs m) (model_values m)),
      (subseq (graph_outputs m) (model_values m)),
      all2 value_has_type inps (graph_inputs m) &
      all2 value_has_type outs (graph_outputs m)]
end.

Lemma isSuccess_map {T1 T2} (f : T1 -> error_option T2) (xs : seq T1)
  : isSuccess (escapeSequenceExtractor.list_error_option_to_error_option_list (ListDef.map f xs)) = all isSuccess (map f xs).
elim: xs => //= x xs IHxs.
case: (f x) => //= t.
rewrite -IHxs.
by case: (escapeSequenceExtractor.list_error_option_to_error_option_list (ListDef.map f xs)).
Qed.

Definition not_self_ref (items : seq vertex) (n : NodeProto) : bool :=
  let : NodeProto_constructor inp _ _ _ _ _ _ _ _ _ := n in
  let helper := fun x => if x is [:: y] then y != node n else false in
  all helper (map (find_vertex items) inp).

Lemma finds_in {items : seq vertex} {name : string} {x : vertex}
  : find_vertex items name = [:: x] -> x \in items.
Proof.
elim: items => //= v vs IHv.
case: (vertex_has_name name v) => //=.
case=> -> _.
rewrite inE.
apply/orP.
by left.
move=> /IHv H.
rewrite inE.
apply/orP.
by right.
Qed.

Lemma app_cat {T} (s1 s2 : seq T) : (s1 ++ s2)%list = cat s1 s2.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma length_size {T} (s : seq T) : Datatypes.length s = size s.
Proof. by elim: s => //= _ s ->. Qed.

Lemma listmap_map {T1 T2} {f : T1 -> T2} (s : seq T1) : ListDef.map f s = map f s.
Proof. by elim: s => //. Qed.

Lemma rev_is_rev {T} (xs : seq T) : List.rev xs = rev xs.
Proof.
elim: xs => //= x xs ->.
rewrite app_cat /=.
by rewrite rev_cons cats1.
Qed.

Definition node_inputs (n : NodeProto) : seq string :=
  let: NodeProto_constructor ins _ _ _ _ _ _ _ _ _ := n in ins.

Definition node_outputs (n : NodeProto) : seq string :=
  let: NodeProto_constructor _ outs _ _ _ _ _ _ _ _ := n in outs.

Definition value_name (v : ValueInfoProto) : option string :=
  let: ValueInfoProto_constructor n _ _ _ := v in n.

Definition tensor_name (t : TensorProto) : option string :=
  let: TensorProto_constructor _ _ _ _ _ _ _ n _ _ _ _ _ _ _ := t in n.

(** [defined] holds every name produced so far.  Each node may only read
    names that are already defined and must define fresh ones. *)
Fixpoint topo_sorted (defined : seq string) (nodes : seq NodeProto) : bool :=
  if nodes is n :: ns then
    [&& all (fun i => i \in defined) (node_inputs n),
        all (fun o => o \notin defined) (node_outputs n),
        uniq (node_outputs n) &
        topo_sorted (node_outputs n ++ defined) ns]
  else true.

Definition graph_acyclic (nodes : seq NodeProto) (inputs : seq ValueInfoProto)
  (initialisers : seq TensorProto) : bool :=
  let names := (pmap value_name inputs ++ pmap tensor_name initialisers)%SEQ in
  uniq names && topo_sorted names nodes.

Definition graph_items (nodes : seq NodeProto) (inputs : seq ValueInfoProto)
  (initialisers : seq TensorProto) : seq vertex :=
  ([seq node x0 | x0 <- List.rev nodes] ++ [seq input x0 | x0 <- inputs] ++
     [seq tensor x0 | x0 <- initialisers])%SEQ.

(** The operation and number of inputs are supported. *)
Definition valid_op (n : NodeProto) : bool :=
  if n is NodeProto_constructor ins _ _ (Some s) _ _ _ _ _ _ then
    if (s =? """Gemm""")%string then (size ins == 2%N) || (size ins == 3%N)
    else if (s =? """Relu""")%string then size ins == 1%N
    else false
  else false.

(** The names a vertex is found under by [find_vertex]. *)
Definition vnames (v : vertex) : seq string :=
  match v with
  | node n => node_outputs n
  | tensor t => oapp (fun x => [:: x]) [::] (tensor_name t)
  | input v | output v => oapp (fun x => [:: x]) [::] (value_name v)
  end.

Lemma Inb_mem s l : onnx_evaluator.Inb s l = (s \in l).
Proof.
elim: l => //= h t ->; rewrite in_cons.
have -> : (s == h) = String.eqb s h by [].
by case: (String.eqb s h).
Qed.

Lemma vertex_has_nameE name v : vertex_has_name name v = (name \in vnames v).
Proof.
case: v => [[? outs ? ? ? ? ? ? ? ?]|[? ? ? ? ? ? ? [nm|] ? ? ? ? ? ? ?]|[[nm|] ? ? ?]|[[nm|] ? ? ?]] //=.
- exact: Inb_mem.
all: by rewrite inE.
Qed.

Lemma find_vertexE s name : find_vertex s name = filter (vertex_has_name name) s.
Proof. by elim: s => //= v s ->. Qed.

Lemma find_vertex_uniq s v name :
  uniq (flatten (map vnames s)) -> v \in s -> name \in vnames v ->
  find_vertex s name = [:: v].
Proof.
rewrite find_vertexE.
elim: s => //= w s IH; rewrite cat_uniq => /and3P [_ dis us].
have notin u : u \in s -> name \in vnames u -> name \notin vnames w.
  move=> uin nu; move/hasPn: dis; apply.
  by apply/flattenP; exists (vnames u) => //; exact: map_f.
rewrite in_cons => /orP [/eqP ->|vin] nv.
  rewrite vertex_has_nameE nv; congr (_ :: _); apply/eqP.
  rewrite -[_ == _]negbK -has_filter; apply/hasPn => u uin.
  by rewrite vertex_has_nameE; apply: contraTN nv => /(notin _ uin).
by rewrite vertex_has_nameE (negbTE (notin _ vin nv)); exact: IH.
Qed.

Lemma vnames_items nodes inputs initialisers :
  flatten (map vnames (graph_items nodes inputs initialisers)) =
  (flatten (map node_outputs (rev nodes)) ++
     pmap value_name inputs ++ pmap tensor_name initialisers)%SEQ.
Proof.
rewrite /graph_items rev_is_rev !map_cat !flatten_cat.
congr (_ ++ (_ ++ _))%SEQ.
- by elim: (rev nodes) => //= ? ? ->.
- by elim: inputs => //= i ? ->; case: (value_name i).
- by elim: initialisers => //= t ? ->; case: (tensor_name t).
Qed.

(** Membership in [graph_items], one lemma per kind of vertex. *)
Lemma mem_graph_items_node nodes inputs initialisers m :
  (node m \in graph_items nodes inputs initialisers) = (m \in nodes).
Proof.
rewrite /graph_items !mem_cat rev_is_rev mem_map ?mem_rev; first by move=> ? ? [].
have -> : node m \in [seq input x | x <- inputs] = false by apply/negbTE/mapP => -[? _].
have -> : node m \in [seq tensor x | x <- initialisers] = false.
  by apply/negbTE/mapP => -[? _].
by rewrite !orbF.
Qed.

Lemma mem_graph_items_input nodes inputs initialisers i :
  (input i \in graph_items nodes inputs initialisers) = (i \in inputs).
Proof.
rewrite /graph_items !mem_cat mem_map; first by move=> ? ? [].
have -> : input i \in [seq node x | x <- List.rev nodes] = false.
  by apply/negbTE/mapP => -[? _].
have -> : input i \in [seq tensor x | x <- initialisers] = false.
  by apply/negbTE/mapP => -[? _].
by rewrite !orbF.
Qed.

Lemma mem_graph_items_tensor nodes inputs initialisers t :
  (tensor t \in graph_items nodes inputs initialisers) = (t \in initialisers).
Proof.
rewrite /graph_items !mem_cat [tensor t \in [seq tensor _ | _ <- _]]mem_map; first by move=> ? ? [].
have -> : tensor t \in [seq node x | x <- List.rev nodes] = false.
  by apply/negbTE/mapP => -[? _].
have -> : tensor t \in [seq input x | x <- inputs] = false.
  by apply/negbTE/mapP => -[? _].
by [].
Qed.

Lemma output_notin_graph_items nodes inputs initialisers o :
  (output o \in graph_items nodes inputs initialisers) = false.
Proof.
by apply/negbTE; rewrite /graph_items !mem_cat; apply/or3P => -[] /mapP [? _].
Qed.

Lemma topo_sorted_uniq defined nodes :
  topo_sorted defined nodes -> uniq defined ->
  uniq (flatten (map node_outputs (rev nodes)) ++ defined)%SEQ.
Proof.
elim: nodes defined => //= n ns IH defined /and4P [_ fresh uo ts] ud.
rewrite rev_cons -cats1 map_cat flatten_cat /= cats0 -catA.
by apply: IH ts _; rewrite cat_uniq uo ud andbT has_sym -all_predC.
Qed.

Variant valid_op_spec (items : seq vertex) (n : NodeProto) : Prop :=
  | VGemm2 i1 i2 v1 v2 outs a b c d e f g of
      n = NodeProto_constructor [:: i1; i2] outs a (Some """Gemm""") b c d e f g &
      find_vertex items i1 = [:: v1] &
      find_vertex items i2 = [:: v2] &
      not_self_ref items n
  | VGemm3 i1 i2 i3 v1 v2 v3 outs a b c d e f g of
      n = NodeProto_constructor [:: i1; i2; i3] outs a (Some """Gemm""") b c d e f g &
      find_vertex items i1 = [:: v1] &
      find_vertex items i2 = [:: v2] &
      find_vertex items i3 = [:: v3] &
      not_self_ref items n
  | VRelu i v outs a b c d e f g of
      n = NodeProto_constructor [:: i] outs a (Some """Relu""") b c d e f g &
      find_vertex items i = [:: v] &
      not_self_ref items n.

(** [acyclic_at items v] : the subgraph below [v] is acyclic.  A node is
    the only vertex named by each of its outputs, every input names exactly
    one vertex, and that child is again acyclic in the graph with the parent
    removed.  A cycle through [v] would need a lookup to find an ancestor
    that has already been removed. *)
Inductive acyclic_at (items : seq vertex) : vertex -> Prop :=
  | acyclic_leaf v : (forall n, v <> node n) -> acyclic_at items v
  | acyclic_node n :
      (forall o, o \in node_outputs n -> find_vertex items o = [:: node n]) ->
      (forall i, i \in node_inputs n ->
         exists2 w, find_vertex items i = [:: w] & acyclic_at (rem (node n) items) w) ->
      acyclic_at items (node n).

(** A child of a node in an acyclic graph is in an acyclic graph once the
    parent is removed. *)
Lemma acyclic_at_child (items : seq vertex) (n : NodeProto) (i : string) (w : vertex) :
  acyclic_at items (node n) -> i \in node_inputs n -> find_vertex items i = [:: w] ->
  acyclic_at (rem (node n) items) w.
Proof.
case E: _ / => [v nv|m _ H] iin F; first by case: (nv n).
case: E H iin => -> H /H [w' F' Hw'].
by move: F'; rewrite F => -[->].
Qed.

Lemma flatten_map_rem_sub {T U : eqType} (f : T -> seq U) x s z :
  z \in flatten (map f (rem x s)) -> z \in flatten (map f s).
Proof.
move=> /flattenP [l /mapP [y /mem_rem yin ->] zin].
by apply/flattenP; exists (f y) => //; exact: map_f.
Qed.

Lemma uniq_flatten_rem {T U : eqType} (f : T -> seq U) x s :
  uniq (flatten (map f s)) -> uniq (flatten (map f (rem x s))).
Proof.
elim: s => //= y s IH; rewrite cat_uniq => /and3P [uy dis us].
case: ifP => _ //=; rewrite cat_uniq uy IH // andbT.
by apply: contra dis => /hasP [z zin zy]; apply/hasP; exists z => //; exact: flatten_map_rem_sub zin.
Qed.

(** A node whose inputs are already defined and whose outputs are fresh is
    acyclic, given that every vertex defining an earlier name is. *)
Lemma acyclic_at_fresh_node (its : seq vertex) (D : seq string) n (U : seq vertex) :
  (forall U : seq vertex, {subset U <= its} -> uniq (flatten (map vnames U)) ->
     (forall s, s \in D -> exists2 v, v \in U & s \in vnames v) ->
     forall s v, s \in D -> v \in U -> s \in vnames v -> acyclic_at U v) ->
  all (fun i => i \in D) (node_inputs n) -> all (fun o => o \notin D) (node_outputs n) ->
  {subset U <= its} -> uniq (flatten (map vnames U)) ->
  (forall s, s \in D -> exists2 v, v \in U & s \in vnames v) ->
  node n \in U -> acyclic_at U (node n).
Proof.
move=> G ins fresh sub uU HD nU; apply: acyclic_node.
  by move=> o oin; exact: find_vertex_uniq uU nU oin.
move=> i iin; have iD := allP ins i iin.
have nf s : s \in D -> s \notin vnames (node n).
  by move=> sD; apply/negP => /(allP fresh); rewrite sD.
have [w wU iw] := HD i iD.
exists w; first exact: find_vertex_uniq uU wU iw.
have remU u s : s \in D -> u \in U -> s \in vnames u -> u \in rem (node n) U.
  move=> sD uin su; apply: rem_mem uin; apply/eqP => un.
  by move: su; rewrite un; apply/negP; exact: nf.
apply: (G (rem (node n) U) _ _ _ i w iD (remU _ _ iD wU iw) iw).
- by move=> u /mem_rem /sub.
- exact: uniq_flatten_rem.
- by move=> s sD; have [v vU sv] := HD s sD; exists v => //; exact: remU vU sv.
Qed.

Lemma acyclic_at_topo (its : seq vertex) (D : seq string) (ns : seq NodeProto) :
  uniq (flatten (map vnames its)) -> topo_sorted D ns ->
  (forall m, m \in ns -> node m \in its) ->
  (forall U : seq vertex, {subset U <= its} -> uniq (flatten (map vnames U)) ->
     (forall s, s \in D -> exists2 v, v \in U & s \in vnames v) ->
     forall s v, s \in D -> v \in U -> s \in vnames v -> acyclic_at U v) ->
  (forall s, s \in D -> exists2 v, v \in its & s \in vnames v) ->
  forall n, n \in ns -> acyclic_at its (node n).
Proof.
elim: ns D => //= m ns IH D uI /and4P [ins fresh _ ts] Hm G HD n.
have mI : node m \in its by apply: Hm; exact: mem_head.
rewrite in_cons => /orP [/eqP -> | nin].
  by apply: (acyclic_at_fresh_node its D) => //; move=> u.
apply: (IH (node_outputs m ++ D)%SEQ) => //.
- by move=> m' m'in; apply: Hm; rewrite in_cons m'in orbT.
- move=> U sub uU HD' s v; rewrite mem_cat => /orP [so|sD] vU sv; last first.
    apply: (G U sub uU _ s v sD vU sv) => s' s'D; apply: HD'.
    by rewrite mem_cat s'D orbT.
  have -> : v = node m.
    have := find_vertex_uniq _ _ _ uI (sub _ vU) sv.
    by rewrite (find_vertex_uniq _ _ _ uI mI so) => -[->].
  have sin : s \in (node_outputs m ++ D)%SEQ by rewrite mem_cat so.
  have [v' v'U sv'] := HD' s sin.
  have mU : node m \in U.
    have := find_vertex_uniq _ _ _ uI (sub _ v'U) sv'.
    by rewrite (find_vertex_uniq _ _ _ uI mI so) => -[->].
  apply: (acyclic_at_fresh_node its D) => // s' s'D; apply: HD'.
  by rewrite mem_cat s'D orbT.
- move=> s; rewrite mem_cat => /orP [so|sD]; last exact: HD.
  by exists (node m).
Qed.

(** The computable check implies the subgraph below every vertex is acyclic. *)
Lemma graph_acyclic_at {nodes inputs initialisers} v :
  graph_acyclic nodes inputs initialisers ->
  v \in graph_items nodes inputs initialisers ->
  acyclic_at (graph_items nodes inputs initialisers) v.
Proof.
rewrite /graph_acyclic => /andP [ub ts] vin.
set its := graph_items nodes inputs initialisers in vin *.
have uI : uniq (flatten (map vnames its)).
  by rewrite /its vnames_items; exact: topo_sorted_uniq.
set base := (pmap value_name inputs ++ pmap tensor_name initialisers)%SEQ in ts.
have leaf s : s \in base ->
    exists2 u, u \in its & (s \in vnames u) /\ (forall m, u <> node m).
  rewrite mem_cat !mem_pmap => /orP [/mapP [i iin E]|/mapP [t tin E]].
    by exists (input i); rewrite ?mem_graph_items_input //= -E inE.
  by exists (tensor t); rewrite ?mem_graph_items_tensor //= -E inE.
case: v vin => [n|t|i|o] vin; try by apply: acyclic_leaf.
apply: (acyclic_at_topo its base nodes) => //.
- by move=> m min; rewrite /its mem_graph_items_node.
- move=> U sub uU HD s v sD vU sv; apply: acyclic_leaf => m vm.
  have [u uI' [su nu]] := leaf s sD.
  have := find_vertex_uniq _ _ _ uI (sub _ vU) sv.
  by rewrite (find_vertex_uniq _ _ _ uI uI' su) vm => -[/nu].
- by move=> s /leaf [u uin [su _]]; exists u.
- by rewrite -(mem_graph_items_node _ inputs initialisers).
Qed.

(** Inverting [acyclic_at] at a node. *)
Lemma acyclic_at_nodeP {items n} :
  acyclic_at items (node n) ->
  forall i, i \in node_inputs n ->
  exists2 w, find_vertex items i = [:: w] & acyclic_at (rem (node n) items) w.
Proof.
case E: _ / => [v nv|m _ H]; first by case: (nv n).
by case: E H => ->.
Qed.

(** An acyclic node is the only vertex named by each of its outputs. *)
Lemma acyclic_at_owns {items n o} :
  acyclic_at items (node n) -> o \in node_outputs n ->
  find_vertex items o = [:: node n].
Proof.
case E: _ / => [v nv|m Ho _]; first by case: (nv n).
by case: E Ho => -> Ho /Ho.
Qed.

Lemma find_vertex_rem s x i :
  find_vertex s i = [:: x] -> find_vertex (rem x s) i = [::].
Proof.
rewrite !find_vertexE.
elim: s => //= y s IH; case Hy: (vertex_has_name i y).
  by case=> -> F; rewrite eqxx.
move=> F; have : x \in filter (vertex_has_name i) s by rewrite F mem_head.
rewrite mem_filter => /andP [px _].
have nyx : y != x by apply/eqP => yx; rewrite yx px in Hy.
by rewrite (negbTE nyx) /= Hy; exact: IH.
Qed.

(** Every input of an acyclic node names exactly one vertex, and that vertex
    is not the node itself. *)
Lemma acyclic_at_find {items n i} :
  acyclic_at items (node n) -> i \in node_inputs n ->
  exists2 w, find_vertex items i = [:: w] & w != node n.
Proof.
move=> /acyclic_at_nodeP H iin; have [w F Hw] := H i iin.
exists w => //; apply/eqP => wn; move: Hw F; rewrite wn => Hw F.
have [w' F' _] := acyclic_at_nodeP Hw i iin.
by rewrite (find_vertex_rem _ _ _ F) in F'.
Qed.

Lemma acyclic_at_not_self_ref {items n} :
  acyclic_at items (node n) -> not_self_ref items n.
Proof.
move=> /acyclic_at_find F.
case: n F => ins outs a b c d e f g h F /=.
rewrite all_map; apply/allP => i iin /=.
by have [v -> vn] := F i iin.
Qed.

Lemma valid_opP {items n} :
  acyclic_at items (node n) -> valid_op n -> valid_op_spec items n.
Proof.
move=> ac.
have nsr := acyclic_at_not_self_ref ac.
have F i : i \in node_inputs n -> exists v, find_vertex items i = [:: v].
  by case/(acyclic_at_find ac) => v ? _; exists v.
move: nsr F; case: n {ac} => ins outs a [s|] b c d e f g //=.
case: (String.eqb_spec s """Gemm""") => [->|_].
- case: ins => [|i1 [|i2 [|i3 [|? ?]]]] //= nsr F _.
  + have [v1 E1] := F i1 (mem_head _ _).
    have /F [v2 E2] : i2 \in [:: i1; i2] by rewrite !inE eqxx orbT.
    by eapply VGemm2; [reflexivity | exact: E1 | exact: E2 | exact: nsr].
  + have [v1 E1] := F i1 (mem_head _ _).
    have /F [v2 E2] : i2 \in [:: i1; i2; i3] by rewrite !inE eqxx orbT.
    have /F [v3 E3] : i3 \in [:: i1; i2; i3] by rewrite !inE eqxx !orbT.
    by eapply VGemm3; [reflexivity | exact: E1 | exact: E2 | exact: E3 | exact: nsr].
- case: (String.eqb_spec s """Relu""") => [->|_] //.
  case: ins => [|i [|? ?]] //= nsr F _.
  have [v E] := F i (mem_head _ _).
  by eapply VRelu; [reflexivity | exact: E | exact: nsr].
Qed.

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

Definition dims_prod (dims : seq int64) : nat := \prod_(d <- dims) int64_to_dim d.

Lemma dims_prod_pos {dims : seq int64} : all (fun x => 0 < int64_to_dim x)%nat dims -> (dims_prod dims > 0)%nat.
Proof.
elim: dims => //=.
rewrite /dims_prod /=.
by rewrite big_nil.
move=> x xs IHxs /andP [Hx Hxs].
rewrite /dims_prod.
rewrite big_cons.
rewrite muln_gt0.
apply/andP.
split=> //.
by apply/IHxs.
Qed.

Definition tensorProtoSized (t : TensorProto) : bool :=
  let: TensorProto_constructor dims data_type _ fd i32 _ i64 _ _ _ _ _ _ _ _ := t in
  (all (fun x => 0 < int64_to_dim x)%nat dims) &&
  if data_type is Some dt then
    match DataType_TensorProto_of_int32 dt with
    | Some FLOAT_TensorProto => size fd  == dims_prod dims
    | Some INT32_TensorProto => size i32 == dims_prod dims
    | Some INT64_TensorProto => size i64 == dims_prod dims
    | _ => false
    end
  else false.

Variant tensorProtoSized_spec (t : TensorProto) : Prop :=
  | TFloat dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 of
      t = TensorProto_constructor dims (Some dt) x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 &
      DataType_TensorProto_of_int32 dt = Some FLOAT_TensorProto &
      all (fun x => 0 < int64_to_dim x)%nat dims &
      size fd = dims_prod dims
  | TInt32 dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 of
      t = TensorProto_constructor dims (Some dt) x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 &
      DataType_TensorProto_of_int32 dt = Some INT32_TensorProto &
      all (fun x => 0 < int64_to_dim x)%nat dims &
      size i32 = dims_prod dims
  | TInt64 dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 of
      t = TensorProto_constructor dims (Some dt) x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 &
      DataType_TensorProto_of_int32 dt = Some INT64_TensorProto &
      all (fun x => 0 < int64_to_dim x)%nat dims &
      size i64 = dims_prod dims.

Lemma tensorProtoSizedP t : tensorProtoSized t -> tensorProtoSized_spec t.
Proof.
case: t => dims [dt|] x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 //= /andP [Hall] //.
case E: (DataType_TensorProto_of_int32 dt) => [[]|] //= /eqP H;
                                              first [ by eapply TFloat; [reflexivity | exact: E | exact: Hall | exact: H]
                                                    | by eapply TInt32; [reflexivity | exact: E | exact: Hall | exact: H]
                                                    | by eapply TInt64; [reflexivity | exact: E | exact: Hall | exact: H] ].
Qed.

Definition sized_tensor (t : TensorType Elem) : eqType :=
  { p : qTensor | dims_match p (tensorDims _ t) && Tensor_has_type p (tag (tensorTypes _ t)) && tensorProtoSized p}.

Definition tensor_dtype (t : TensorProto) : option DataType_TensorProto :=
  let: TensorProto_constructor _ ty _ _ _ _ _ _ _ _ _ _ _ _ _ := t in
  if ty is Some ty then DataType_TensorProto_of_int32 ty else None.

Definition tensors_match (ts : seq TensorProto) : bool :=
  if ts is t :: ts' then
    if tensor_dtype t is Some dt then all (fun u => tensor_dtype u == Some dt) ts'
    else false
  else true.

Variant tensors_match_spec (ts : seq TensorProto) : Prop :=
  | TMNil of ts = [::]
  | TMSome dt of ts != [::] & all (fun u => tensor_dtype u == Some dt) ts.

Lemma tensors_matchP ts : tensors_match ts -> tensors_match_spec ts.
Proof.
case: ts => [_|t ts]; first exact: TMNil.
rewrite /=; case E: (tensor_dtype t) => [dt|] // H.
by apply: (@TMSome _ dt) => //=; rewrite E eqxx.
Qed.

Lemma tensors_match2P t1 t2 :
  tensors_match [:: t1; t2] ->
  exists2 dt, tensor_dtype t1 = Some dt & tensor_dtype t2 = Some dt.
Proof.
rewrite /=; case: (tensor_dtype t1) => [dt|] //= /andP[/eqP H2 _].
by exists dt.
Qed.

Lemma DataType_float {t} :
  DataType_TensorProto_of_int32 t = Some FLOAT_TensorProto -> Z_of_int32 t = 1%Z.
Proof.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 t) => [|p|p] //=; do ? case: p => [p|p|] //=.
Qed.

Lemma DataType_int32 {t} :
  DataType_TensorProto_of_int32 t = Some INT32_TensorProto -> Z_of_int32 t = 6%Z.
Proof.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 t) => [|p|p] //=; do ? case: p => [p|p|] //=.
Qed.

Lemma DataType_int64 {t} :
  DataType_TensorProto_of_int32 t = Some INT64_TensorProto -> Z_of_int32 t = 7%Z.
Proof.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 t) => [|p|p] //=; do ? case: p => [p|p|] //=.
Qed.

Lemma isSuccessP (T : Type) (x : error_option T) :
  isSuccess x -> exists a, x = Success a.
Proof. by case: x => // a _; exists a. Qed.

Lemma list_product_float_success (xs ys : seq float32)
  : size xs = size ys -> isSuccess (list_product_float32 xs ys).
Proof.
elim: xs ys => //= [ys /esym /size0nil -> // | x xs IHxs ys sizes].
case: ys sizes => //= y ys /eq_add_S /(IHxs ys).
by case: (list_product_float32 xs ys).
Qed.

Definition dims_correct (xs : seq int64) : bool :=
  if xs is [::] then true
  else if xs is [:: h] then (0 <? (Z_of_int64 h))%Z
       else if xs is [:: h; w] then (0 <? (Z_of_int64 h))%Z && (0 <? (Z_of_int64 w))%Z
            else false.

Variant dims_correct_spec (xs : seq int64) : Prop :=
  | Scalar of xs = [::]
  | Vector h of xs = [:: h] &
      (0 <? (Z_of_int64 h))%Z
| Matrix h w of xs = [:: h; w] &
    (0 <? (Z_of_int64 h))%Z &
      (0 <? (Z_of_int64 w))%Z.

Lemma dims_correctP {xs : seq int64} : dims_correct xs -> dims_correct_spec xs.
case: xs => [_|x [H|y [/andP [H0 H1]|//]]]; first exact: Scalar.
by apply: (Vector _ x).
by apply: (Matrix _ x y).
Qed.

Definition get_dims (t : TensorProto) : list int64 :=
  match t with
  | TensorProto_constructor x _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition broadcastable_vector {T} (dim1_a dim2_a : nat) (b : matrix T) : bool :=
  if shape b is (1%nat, defined_b_dim) then
    if b is [:: row] then (defined_b_dim =? dim2_a)%nat else false
  else if shape b is (defined_b_dim, 1%nat) then
         if transpose b is [:: row] then (defined_b_dim =? dim1_a)%nat else false
       else false.

Definition broadcastable_matrix {T} (dim1_a dim2_a : nat) (dims_b : seq nat)
  (b : matrix T) : bool :=
  if dims_b is [::] then
    if b is [::[::k]] then true else false
  else if dims_b is [:: _] then broadcastable_vector dim1_a dim2_a b
       else if dims_b is [:: 1%nat; _] then broadcastable_vector dim1_a dim2_a b
            else if dims_b is [:: _; 1%nat] then broadcastable_vector dim1_a dim2_a b
                 else if dims_b is [:: dim1_b; dim2_b] then (dim1_a =? dim1_b)%nat && (dim2_a =? dim2_b)%nat
                      else false.

Lemma repeat_is_nseq {T} (n : nat) (t : T) : ListDef.repeat t n = nseq n t.
Proof.
by elim: n => //= n ->.
Qed.

Lemma add_lists_float32_success {s1 s2 : seq float32}
  : size s1 = size s2 ->
   isSuccess (add_lists_float32 s1 s2).
Proof.
move=> H.
elim: s2 s1 H=> //= [[|//=] | x xs IHx [//| y ys] /= H] //.
by case/isSuccessP: (IHx ys (succn_inj H)) => x' ->.
Qed.

Lemma matrix_addition_float_success (m1 m2 : matrix float32) :
  all2 (fun xs ys => size xs == size ys) m1 m2 ->
  isSuccess (matrix_addition_float32 m1 m2).
Proof.
elim: m1 m2 => [|xs xss IHxss m2].
by case.
case: m2=> // ys yss.
rewrite /= => /andP [/eqP] /add_lists_float32_success.
case/isSuccessP => ? ->.
move=> /(IHxss yss).
by case/isSuccessP => ? ->.
Qed.

Definition is_mat {T} (n k : nat) (m : matrix T) : bool :=
  (size m == n) && all (fun r => size r == k) m.

Lemma is_mat_cons {T} n k (r : seq T) rs :
  is_mat n k (r :: rs) = (size r == k) && is_mat n.-1 k rs && (0 < n)%nat.
Proof.
rewrite /is_mat /=; case: n => [|n] /=; first by rewrite andbF.
by rewrite eqSS andbT andbCA andbA.
Qed.

Lemma is_mat_nseq {T} n k (r : seq T) : size r = k -> is_mat n k (nseq n r).
Proof.
by move=> Hr; rewrite /is_mat size_nseq eqxx all_nseq Hr eqxx orbT.
Qed.

Lemma shape_mat {T} n k (m : matrix T) :
  (0 < n)%nat -> (0 < k)%nat -> is_mat n k m -> shape m = (n, k).
Proof.
case: m => [|[|x r] rs] /=; rewrite /is_mat /=.
- by case: n.
- by case: k => // k _ _ /andP [_ /andP []].
- by move=> _ _ /andP [/eqP <- /andP [/eqP <- _]]; rewrite !length_size.
Qed.

Lemma option_list_heads {T} (m : matrix T) :
  all (fun r => (0 < size r)%nat) m ->
  exists h, option_list_of_list_option (ListDef.map matrices.head m) = Some h /\
          size h = size m.
Proof.
elim: m => [|[|x r] rs IH] /=; first by exists [::].
- by [].
- by case/IH => h [-> <-]; exists (x :: h).
Qed.

Lemma option_list_size {T} (l : seq (option T)) h :
  option_list_of_list_option l = Some h -> size h = size l.
Proof.
elim: l h => [|[x|] l IH] h /=; first by case=> <-.
- by case E: (option_list_of_list_option l) => [h'|] // [<-] /=; rewrite (IH _ E).
- by [].
Qed.

Lemma transpose_rec_mat {T} c (m : matrix T) d :
  (0 < size m)%nat -> all (fun r => size r == c) m -> (c < d)%nat ->
  exists t, transpose_rec d m = Some t /\ is_mat c (size m) t.
Proof.
elim: c m d => [|c IH] [|x xs] [|d] //= _.
- by case: x => // /andP [] //; exists [::].
- case: x => [|y ys] /andP [] // Hx Hxs Hcd.
  have Hne : all (fun r => (0 < size r)%nat) xs by apply: sub_all Hxs => r /eqP ->.
  have [h [Eh Sh]] := @option_list_heads _ _ Hne.
  rewrite /= Eh.
  have Htl : all (fun r => size r == c) (ys :: ListDef.map (@List.tl T) xs).
    apply/andP; split; first exact: Hx.
    change (all (fun r => size r == c) (ListDef.map (@List.tl T) xs)).
    rewrite listmap_map all_map; apply: sub_all Hxs => r /eqP.
    by case: r => //= ? ? [->].
  have [t [-> Ht]] := IH (ys :: ListDef.map (@List.tl T) xs) d (ltn0Sn _) Htl Hcd.
  move: Ht; rewrite /= listmap_map size_map => Ht.
  exists ((y :: h) :: t); split=> //.
  by rewrite is_mat_cons /= Sh eqxx Ht.
Qed.

Lemma transpose_mat {T} n k (m : matrix T) :
  (0 < n)%nat -> is_mat n k m -> is_mat k n (transpose m).
Proof.
move=> n0 /[dup] Hm /andP [/eqP Sm Hall].
rewrite /transpose.
have Hsh : (shape m).2 = k.
  case: m Hm {Sm Hall} n0 => [|[|x r] rs] /=; first by case: n.
  - by rewrite /is_mat /= => /andP [_ /andP [/eqP <-]].
  - by rewrite /is_mat /= length_size => /andP [_ /andP [/eqP]].
have m0 : (0 < size m)%nat by rewrite Sm.
have kd : (k < (shape m).2 + 1)%nat by rewrite Hsh addn1.
have [t [-> Ht]] := @transpose_rec_mat _ _ _ _ m0 Hall kd.
by rewrite -Sm.
Qed.

Lemma transpose_col {T} (b : matrix T) row :
  (shape b).2 = 1%nat -> transpose b = [:: row] -> size row = size b.
Proof.
case: b => [|[|x [|y l]] rs] //= _.
rewrite /transpose /=.
case E: (option_list_of_list_option (ListDef.map matrices.head rs)) => [h|] /=.
  by case=> <- /=; rewrite (option_list_size _ _ E) listmap_map size_map.
by case: rs E.
Qed.

Lemma broadcast_vector_mat {T} n k (b : matrix T) :
  (0 < n)%nat -> (0 < k)%nat -> broadcastable_vector n k b ->
  exists c, broadcast_2d_vector n k b = Success c /\ is_mat n k c.
Proof.
move=> n0 k0.
rewrite /broadcastable_vector /broadcast_2d_vector.
move: (transpose_col b) => Htb.
move: (transpose b) Htb => tb Htb.
case: b Htb => [|[|x r] rs] //=.
case: rs => [|r' rs] /= Htb.
  case: k k0 => // k _; case: Nat.eqb_spec => // <- _.
  exists (ListDef.repeat (x :: r) n); split=> //.
  by rewrite repeat_is_nseq is_mat_nseq //= length_size.
case: r Htb => [|y r] //= Htb.
case: tb Htb => [|row [|? ?]] // /(_ row erefl erefl) Hrow.
case: n n0 => [|[|n]] //= _; case: Nat.eqb_spec => // <- _.
eexists; split; first by reflexivity.
apply: transpose_mat => //.
by rewrite repeat_is_nseq; apply: is_mat_nseq; rewrite Hrow /= length_size.
Qed.

Lemma broadcast_mat {T} n k dims (b : matrix T) :
  (0 < n)%nat -> (0 < k)%nat ->
  broadcastable_matrix n k dims b ->
  (if dims is [:: h; w] then is_mat h w b else true) ->
  exists c, broadcast_2d n k dims b = Success c /\ is_mat n k c.
Proof.
move=> n0 k0.
case: dims => [|d1 [|d2 [|d3 ds]]].
- case: b => [|[|x [|? ?]] [|? ?]] //= _ _.
  by eexists; split; first reflexivity; rewrite !repeat_is_nseq is_mat_nseq // size_nseq.
- by case: d1 => [|[|d1]] H _; exact: (broadcast_vector_mat _ _ _ n0 k0 H).
- case: d1 => [|[|d1]]; case: d2 => [|[|d2]] => H Hb;
    first [ exact: (broadcast_vector_mat _ _ _ n0 k0 H)
          | have /andP [/Nat.eqb_spec Hn /Nat.eqb_spec Hk] : ((n =? _) && (k =? _))%nat := H;
            subst; rewrite // /broadcast_2d /= ?Nat.eqb_refl; by exists b ].
- by case: d1 => [|[|d1]]; case: d2 => [|[|d2]].
Qed.

Lemma scale_matrix_float32_mat n k (m : matrix float32) s :
  is_mat n k m -> is_mat n k (scale_matrix_float32 m s).
Proof.
rewrite /is_mat /scale_matrix_float32 !listmap_map size_map all_map.
case/andP=> -> H /=; apply: sub_all H => r /=.
by rewrite listmap_map size_map.
Qed.

Lemma is_mat_all2 {T1 T2} n k (a : matrix T1) (b : matrix T2) :
  is_mat n k a -> is_mat n k b -> all2 (fun xs ys => size xs == size ys) a b.
Proof.
elim: a b n => [|x xs IH] [|y ys] [|n] //=; rewrite !is_mat_cons /=.
by case/andP=> [/andP [/eqP -> Hxs] _] /andP [/andP [/eqP -> Hys] _]; rewrite eqxx (IH _ _ Hxs Hys).
Qed.

Lemma list_error_option_seq_success {T} (f : nat -> error_option T) p s ys :
  (forall j, (s <= j)%nat -> (j < s + p)%nat -> isSuccess (f j)) ->
  exists r, list_error_option_to_error_option_list (ListDef.map f (ListDef.seq s p)) ys = Success r /\
          size r = (p + size ys)%nat.
Proof.
elim: p s ys => [|p IH] s ys H /=.
  by exists (List.rev ys); rewrite rev_is_rev size_rev.
have /isSuccessP [y ->] : isSuccess (f s).
  by apply: H => //; rewrite addnS ltnS leq_addr.
have H' : forall j, (S s <= j)%nat -> (j < S s + p)%nat -> isSuccess (f j).
  by move=> j sj jp; apply: H; [exact: ltnW | rewrite addnS -addSn].
have [r [-> Sr]] := IH (S s) (y :: ys) H'.
by exists r; rewrite Sr /= addnS.
Qed.

Lemma get_column_mat {T} k p (b : matrix T) j :
  is_mat k p b -> (j < p)%nat -> exists c, get_column b j = Success c /\ size c = k.
Proof.
move=> Hb jp.
elim: b k Hb => [|r rs IH] [|k] //=; first by exists [::].
rewrite is_mat_cons /= => /andP [/andP [/eqP Hr Hrs] _].
have : List.nth_error r j <> None.
  by apply/List.nth_error_Some; rewrite length_size; apply/ssrnat.ltP; rewrite Hr.
case: (List.nth_error r j) => [x|] // _.
by have [c [-> <-]] := IH _ Hrs; exists (x :: c).
Qed.

Lemma matrix_multiplication_float32_mat n k p (a b : matrix float32) :
  (0 < k)%nat -> is_mat n k a -> is_mat k p b ->
  exists r, matrix_multiplication_float32 a b = Success r /\ is_mat n p r.
Proof.
move=> k0 Ha Hb.
have Hcols : match b with [::] => 0%nat | row :: _ => Datatypes.length row end = p.
  case: b Hb => [|r rs].
    by rewrite /is_mat /= => /andP [/eqP Hk _]; move: k0; rewrite -Hk.
  by rewrite is_mat_cons length_size => /andP [/andP [/eqP]].
elim: a n Ha => [|x xs IH] [|n] //=; first by exists [::].
rewrite is_mat_cons /= => /andP [/andP [/eqP Hx Hxs] _].
rewrite Hcols.
have Hj : forall j, (0 <= j)%nat -> (j < 0 + p)%nat ->
    isSuccess (matrix_multiplicaiton_float32_helper (x :: xs) b x j).
  move=> j _ jp; rewrite /matrix_multiplicaiton_float32_helper.
  have [c [-> Sc]] := @get_column_mat _ _ _ _ _ Hb jp.
  by apply: list_product_float_success; rewrite Hx Sc.
have [row [-> Srow]] := @list_error_option_seq_success _ _ _ _ [::] Hj.
have [r [-> Hr]] := IH _ Hxs.
exists (row :: r); split=> //.
by rewrite is_mat_cons Srow addn0 eqxx Hr.
Qed.

Lemma gemm_float32_success (m1 m2 m3 : matrix float32) (alpha beta : float32)
  (transA transB : int64) (dims_c : seq nat) (n k p : nat) :
  (0 < n)%nat -> (0 < k)%nat -> (0 < p)%nat ->
  is_mat n k (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) ->
  is_mat k p (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) ->
  broadcastable_matrix n p dims_c m3 ->
  (if dims_c is [:: h; w] then is_mat h w m3 else true) ->
  isSuccess (gemm_float32 m1 m2 m3 alpha beta transA transB dims_c).
Proof.
move=> n0 k0 p0 HA HB Hbc Hdims.
rewrite /gemm_float32.
move: HA HB.
move: (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) => A.
move: (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) => B HA HB.
have [r [-> Hr]] := @matrix_multiplication_float32_mat _ _ _ _ _ k0
  (@scale_matrix_float32_mat _ _ _ alpha HA) HB.
rewrite (@shape_mat _ _ _ _ n0 p0 Hr) /=.
have [c [-> Hc]] := @broadcast_mat _ _ _ _ _ n0 p0 Hbc Hdims.
apply: matrix_addition_float_success.
exact: @is_mat_all2 _ _ _ _ _ _ Hr (@scale_matrix_float32_mat _ _ _ beta Hc).
Qed.

(* int32 *)

Lemma list_product_int32_success (xs ys : seq int32)
  : size xs = size ys -> isSuccess (list_product_int32 xs ys).
Proof.
elim: xs ys => //= [ys /esym /size0nil -> // | x xs IHxs ys sizes].
case: ys sizes => //= y ys /eq_add_S /(IHxs ys).
by case: (list_product_int32 xs ys).
Qed.

Lemma add_lists_int32_success {s1 s2 : seq int32}
  : size s1 = size s2 ->
   isSuccess (add_lists_int32 s1 s2).
Proof.
move=> H.
elim: s2 s1 H=> //= [[|//=] | x xs IHx [//| y ys] /= H] //.
by case/isSuccessP: (IHx ys (succn_inj H)) => x' ->.
Qed.

Lemma matrix_addition_int32_success (m1 m2 : matrix int32) :
  all2 (fun xs ys => size xs == size ys) m1 m2 ->
  isSuccess (matrix_addition_int32 m1 m2).
Proof.
elim: m1 m2 => [|xs xss IHxss m2].
by case.
case: m2=> // ys yss.
rewrite /= => /andP [/eqP] /add_lists_int32_success.
case/isSuccessP => ? ->.
move=> /(IHxss yss).
by case/isSuccessP => ? ->.
Qed.

Lemma scale_matrix_int32_mat n k (m : matrix int32) s :
  is_mat n k m -> is_mat n k (scale_matrix_int32 m s).
Proof.
rewrite /is_mat /scale_matrix_int32 !listmap_map !size_map !all_map.
case/andP=> -> H /=; apply: sub_all H => r /=.
by rewrite !listmap_map !size_map.
Qed.

Lemma matrix_multiplication_int32_mat n k p (a b : matrix int32) :
  (0 < k)%nat -> is_mat n k a -> is_mat k p b ->
  exists r, matrix_multiplication_int32 a b = Success r /\ is_mat n p r.
Proof.
move=> k0 Ha Hb.
have Hcols : match b with [::] => 0%nat | row :: _ => Datatypes.length row end = p.
  case: b Hb => [|r rs].
    by rewrite /is_mat /= => /andP [/eqP Hk _]; move: k0; rewrite -Hk.
  by rewrite is_mat_cons length_size => /andP [/andP [/eqP]].
elim: a n Ha => [|x xs IH] [|n] //=; first by exists [::].
rewrite is_mat_cons /= => /andP [/andP [/eqP Hx Hxs] _].
rewrite Hcols.
have Hj : forall j, (0 <= j)%nat -> (j < 0 + p)%nat ->
    isSuccess (matrix_multiplicaiton_int32_helper (x :: xs) b x j).
  move=> j _ jp; rewrite /matrix_multiplicaiton_int32_helper.
  have [c [-> Sc]] := @get_column_mat _ _ _ _ _ Hb jp.
  by apply: list_product_int32_success; rewrite Hx Sc.
have [row [-> Srow]] := @list_error_option_seq_success _ _ _ _ [::] Hj.
have [r [-> Hr]] := IH _ Hxs.
exists (row :: r); split=> //.
by rewrite is_mat_cons Srow addn0 eqxx Hr.
Qed.

Lemma gemm_int32_success (m1 m2 m3 : matrix int32) (alpha beta : int32)
  (transA transB : int64) (dims_c : seq nat) (n k p : nat) :
  (0 < n)%nat -> (0 < k)%nat -> (0 < p)%nat ->
  is_mat n k (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) ->
  is_mat k p (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) ->
  broadcastable_matrix n p dims_c m3 ->
  (if dims_c is [:: h; w] then is_mat h w m3 else true) ->
  isSuccess (gemm_int32 m1 m2 m3 alpha beta transA transB dims_c).
Proof.
move=> n0 k0 p0 HA HB Hbc Hdims.
rewrite /gemm_int32.
move: HA HB.
move: (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) => A.
move: (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) => B HA HB.
have [r [-> Hr]] := @matrix_multiplication_int32_mat _ _ _ _ _ k0
  (@scale_matrix_int32_mat _ _ _ alpha HA) HB.
rewrite (@shape_mat _ _ _ _ n0 p0 Hr) /=.
have [c [-> Hc]] := @broadcast_mat _ _ _ _ _ n0 p0 Hbc Hdims.
apply: matrix_addition_int32_success.
exact: @is_mat_all2 _ _ _ _ _ _ Hr (@scale_matrix_int32_mat _ _ _ beta Hc).
Qed.

(* int64 *)

Lemma list_product_int64_success (xs ys : seq int64)
  : size xs = size ys -> isSuccess (list_product_int64 xs ys).
Proof.
elim: xs ys => //= [ys /esym /size0nil -> // | x xs IHxs ys sizes].
case: ys sizes => //= y ys /eq_add_S /(IHxs ys).
by case: (list_product_int64 xs ys).
Qed.

Lemma add_lists_int64_success {s1 s2 : seq int64}
  : size s1 = size s2 ->
   isSuccess (add_lists_int64 s1 s2).
Proof.
move=> H.
elim: s2 s1 H=> //= [[|//=] | x xs IHx [//| y ys] /= H] //.
by case/isSuccessP: (IHx ys (succn_inj H)) => x' ->.
Qed.

Lemma matrix_addition_int64_success (m1 m2 : matrix int64) :
  all2 (fun xs ys => size xs == size ys) m1 m2 ->
  isSuccess (matrix_addition_int64 m1 m2).
Proof.
elim: m1 m2 => [|xs xss IHxss m2].
by case.
case: m2=> // ys yss.
rewrite /= => /andP [/eqP] /add_lists_int64_success.
case/isSuccessP => ? ->.
move=> /(IHxss yss).
by case/isSuccessP => ? ->.
Qed.

Lemma scale_matrix_int64_mat n k (m : matrix int64) s :
  is_mat n k m -> is_mat n k (scale_matrix_int64 m s).
Proof.
rewrite /is_mat /scale_matrix_int64 !listmap_map !size_map !all_map.
case/andP=> -> H /=; apply: sub_all H => r /=.
by rewrite !listmap_map !size_map.
Qed.

Lemma matrix_multiplication_int64_mat n k p (a b : matrix int64) :
  (0 < k)%nat -> is_mat n k a -> is_mat k p b ->
  exists r, matrix_multiplication_int64 a b = Success r /\ is_mat n p r.
Proof.
move=> k0 Ha Hb.
have Hcols : match b with [::] => 0%nat | row :: _ => Datatypes.length row end = p.
  case: b Hb => [|r rs].
    by rewrite /is_mat /= => /andP [/eqP Hk _]; move: k0; rewrite -Hk.
  by rewrite is_mat_cons length_size => /andP [/andP [/eqP]].
elim: a n Ha => [|x xs IH] [|n] //=; first by exists [::].
rewrite is_mat_cons /= => /andP [/andP [/eqP Hx Hxs] _].
rewrite Hcols.
have Hj : forall j, (0 <= j)%nat -> (j < 0 + p)%nat ->
    isSuccess (matrix_multiplicaiton_int64_helper (x :: xs) b x j).
  move=> j _ jp; rewrite /matrix_multiplicaiton_int64_helper.
  have [c [-> Sc]] := @get_column_mat _ _ _ _ _ Hb jp.
  by apply: list_product_int64_success; rewrite Hx Sc.
have [row [-> Srow]] := @list_error_option_seq_success _ _ _ _ [::] Hj.
have [r [-> Hr]] := IH _ Hxs.
exists (row :: r); split=> //.
by rewrite is_mat_cons Srow addn0 eqxx Hr.
Qed.

Lemma gemm_int64_success (m1 m2 m3 : matrix int64) (alpha beta : int64)
  (transA transB : int64) (dims_c : seq nat) (n k p : nat) :
  (0 < n)%nat -> (0 < k)%nat -> (0 < p)%nat ->
  is_mat n k (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) ->
  is_mat k p (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) ->
  broadcastable_matrix n p dims_c m3 ->
  (if dims_c is [:: h; w] then is_mat h w m3 else true) ->
  isSuccess (gemm_int64 m1 m2 m3 alpha beta transA transB dims_c).
Proof.
move=> n0 k0 p0 HA HB Hbc Hdims.
rewrite /gemm_int64.
move: HA HB.
move: (match Z_of_int64 transA with 0%Z => m1 | _ => transpose m1 end) => A.
move: (match Z_of_int64 transB with 0%Z => m2 | _ => transpose m2 end) => B HA HB.
have [r [-> Hr]] := @matrix_multiplication_int64_mat _ _ _ _ _ k0
  (@scale_matrix_int64_mat _ _ _ alpha HA) HB.
rewrite (@shape_mat _ _ _ _ n0 p0 Hr) /=.
have [c [-> Hc]] := @broadcast_mat _ _ _ _ _ n0 p0 Hbc Hdims.
apply: matrix_addition_int64_success.
exact: @is_mat_all2 _ _ _ _ _ _ Hr (@scale_matrix_int64_mat _ _ _ beta Hc).
Qed.

Lemma isSuccess_bind {A B} (x : error_option A) (f : A -> B) :
  isSuccess x ->
  isSuccess (match x with Success r => Success (f r) | Error e => Error e end).
Proof. by case: x. Qed.

Definition mat_dims (dims : seq int64) : nat * nat :=
  match dims with
  | [::] => (1, 1)%nat
  | [:: w] => (1%nat, int64_to_dim w)
  | [:: h; w] => (int64_to_dim h, int64_to_dim w)
  | _ => (0, 0)%nat
  end.

Lemma convert_dims_mat dims :
  dims_correct dims -> convert_dims dims = Success (mat_dims dims).
Proof.
rewrite /mat_dims /int64_to_dim.
case/dims_correctP => [|h|h w] -> //=; first by case: (Z_of_int64 h).
by case: (Z_of_int64 h) => //; case: (Z_of_int64 w).
Qed.

Lemma mat_dims_pos dims :
  dims_correct dims -> (0 < (mat_dims dims).1)%nat && (0 < (mat_dims dims).2)%nat.
Proof.
rewrite /mat_dims /int64_to_dim.
case/dims_correctP => [|h|h w] -> //=.
  by case: (Z_of_int64 h) => // q _; apply/ssrnat.ltP/Pos2Nat.is_pos.
case: (Z_of_int64 h) => // q _; case: (Z_of_int64 w) => // q' _.
by apply/andP; split; apply/ssrnat.ltP/Pos2Nat.is_pos.
Qed.

Lemma mat_dims_prod dims :
  dims_correct dims -> dims_prod dims = ((mat_dims dims).1 * (mat_dims dims).2)%nat.
Proof.
rewrite /dims_prod /mat_dims.
case/dims_correctP => [|h|h w] -> /=; rewrite ?big_cons big_nil //.
- by rewrite mul1n muln1.
- by rewrite muln1.
Qed.

Lemma size_firstn {T} (l : seq T) w :
  (w <= size l)%nat -> size (List.firstn w l) = w.
Proof.
elim: w l => [|w IH] [|x l] //= wl.
by rewrite IH.
Qed.

Lemma size_skipn {T} (l : seq T) w :
  size (List.skipn w l) = (size l - w)%nat.
Proof. by elim: w l => [|w IH] [|x l] //=; rewrite ?subn0. Qed.

Lemma convert_from_row_major_mat {T} (l : seq T) h w :
  size l = (h * w)%nat -> is_mat h w (convert_from_row_major l h w).
Proof.
elim: h l => [|h IH] l Hl /=; first by [].
have Hw : (w <= size l)%nat by rewrite Hl mulSn leq_addr.
rewrite is_mat_cons /= andbT size_firstn // eqxx /=; apply: IH.
by rewrite size_skipn Hl mulSn addKn.
Qed.

Lemma matrix_float32_of_tensor_mat t :
  tensorProtoSized t -> dims_correct (get_dims t) ->
  tensor_dtype t = Some FLOAT_TensorProto ->
  exists x, matrix_float32_of_tensor t = Success x /\
          is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 x.
Proof.
case/tensorProtoSizedP => dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 ->
  /= Hdt _ Hsize Hdc; rewrite Hdt // => _.
rewrite (convert_dims_mat _ Hdc).
move: (mat_dims_pos _ Hdc); rewrite (mat_dims_prod _ Hdc) in Hsize.
case: (mat_dims dims) Hsize => h w /= Hsize /andP [h0 w0].
case: fd Hsize => [|f fs] Hsize.
  have : (0 < h * w)%nat by rewrite muln_gt0 h0 w0.
  by rewrite -Hsize.
by eexists; split; first reflexivity; apply: convert_from_row_major_mat.
Qed.

Lemma matrix_int32_of_tensor_mat t :
  tensorProtoSized t -> dims_correct (get_dims t) ->
  tensor_dtype t = Some INT32_TensorProto ->
  exists x, matrix_int32_of_tensor t = Success x /\
          is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 x.
Proof.
case/tensorProtoSizedP => dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 ->
  /= Hdt _ Hsize Hdc; rewrite Hdt // => _.
rewrite (convert_dims_mat _ Hdc).
move: (mat_dims_pos _ Hdc); rewrite (mat_dims_prod _ Hdc) in Hsize.
case: (mat_dims dims) Hsize => h w /= Hsize /andP [h0 w0].
case: i32 Hsize => [|f fs] Hsize.
  have : (0 < h * w)%nat by rewrite muln_gt0 h0 w0.
  by rewrite -Hsize.
by eexists; split; first reflexivity; apply: convert_from_row_major_mat.
Qed.

Lemma matrix_int64_of_tensor_mat t :
  tensorProtoSized t -> dims_correct (get_dims t) ->
  tensor_dtype t = Some INT64_TensorProto ->
  exists x, matrix_int64_of_tensor t = Success x /\
          is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 x.
Proof.
case/tensorProtoSizedP => dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 ->
  /= Hdt _ Hsize Hdc; rewrite Hdt // => _.
rewrite (convert_dims_mat _ Hdc).
move: (mat_dims_pos _ Hdc); rewrite (mat_dims_prod _ Hdc) in Hsize.
case: (mat_dims dims) Hsize => h w /= Hsize /andP [h0 w0].
case: i64 Hsize => [|f fs] Hsize.
  have : (0 < h * w)%nat by rewrite muln_gt0 h0 w0.
  by rewrite -Hsize.
by eexists; split; first reflexivity; apply: convert_from_row_major_mat.
Qed.

Lemma trans_mat {T} h w (m : matrix T) (z : Z) :
  (0 < h)%nat -> is_mat h w m ->
  is_mat (if z is 0%Z then h else w) (if z is 0%Z then w else h)
         (match z with 0%Z => m | _ => transpose m end).
Proof. by case: z => [|?|?] h0 Hm //; apply: transpose_mat. Qed.

Lemma if_Z0_pos (z : Z) (a b : nat) :
  (0 < a)%nat -> (0 < b)%nat -> (0 < if z is 0%Z then a else b)%nat.
Proof. by case: z. Qed.

Definition gemm_dims_ok (d1 d2 : seq int64) (a : seq AttributeProto) : bool :=
  let: (_, _, transA, transB) := get_gemm_attributes a in
  [&& dims_correct d1, dims_correct d2 &
    (if Z_of_int64 transA is 0%Z then (mat_dims d1).2 else (mat_dims d1).1) ==
    (if Z_of_int64 transB is 0%Z then (mat_dims d2).1 else (mat_dims d2).2)].

Definition gemm_int_attrs_ok (a : seq AttributeProto) : bool :=
  let: (alpha, beta, _, _) := get_gemm_attributes a in
  isSome (Z_of_float32 alpha) && isSome (Z_of_float32 beta).

Lemma gemm_two_success (t t' : TensorProto) (a : seq AttributeProto)
  : tensors_match [:: t; t'] -> tensorProtoSized t -> tensorProtoSized t'
    -> gemm_dims_ok (get_dims t) (get_dims t') a
    -> (tensor_dtype t != Some FLOAT_TensorProto -> gemm_int_attrs_ok a)
    -> isSuccess (gemm_two_inputs t t' a).
Proof.
case/tensors_match2P=> dtype Hdtype1 Hdtype2.
move=> Ht Ht' Hdims Hint.
case/tensorProtoSizedP: (Ht) => dims1 dtype1 seg1 float321 int321 bytes1 int641 name1 doc1 raw_data1 ext1 loc1 double1 uint641 meta1 /[dup] Hist -> /= datatype1 sized1 sizes1;
case/tensorProtoSizedP: (Ht') => dims2 dtype2 seg2 float322 int322 bytes2 int642 name2 doc2 raw_data2 ext2 loc2 double2 uint642 meta2 /[dup] Hist' -> /= datatype2 sized2 sizes2 => //=;
move: (Hdtype1);
rewrite -Hdtype2 Hist Hist' /= datatype1 datatype2 // => _;
move: Hdims Hint;
rewrite /gemm_dims_ok /gemm_int_attrs_ok /gemm_two_inputs;
case: (get_gemm_attributes a) => [[[alpha beta] transA] transB] /and3P [Hdc1 Hdc2 /eqP Hk] Hint;
have /andP [h1 w1] := mat_dims_pos _ Hdc1;
have /andP [h2 w2] := mat_dims_pos _ Hdc2;
have n0 := @if_Z0_pos (Z_of_int64 transA) _ _ h1 w1;
have k0 := @if_Z0_pos (Z_of_int64 transA) _ _ w1 h1;
have p0 := @if_Z0_pos (Z_of_int64 transB) _ _ w2 h2.
- have Hty : tensor_dtype t = Some FLOAT_TensorProto by rewrite Hist /= datatype1.
  have Hty' : tensor_dtype t' = Some FLOAT_TensorProto by rewrite Hist' /= datatype2.
  have [x [Ex Hx]] := matrix_float32_of_tensor_mat _ Ht Hdc1 Hty.
  have [x' [Ex' Hx']] := matrix_float32_of_tensor_mat _ Ht' Hdc2 Hty'.
  rewrite (DataType_float datatype1) (DataType_float datatype2) -Hist -Hist' Ex Ex'.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h1 Hx.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h2 Hx'.
  rewrite -Hk in HB.
  by apply: isSuccess_bind; apply: (gemm_float32_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB).
- have Hty : tensor_dtype t = Some INT32_TensorProto by rewrite Hist /= datatype1.
  have Hty' : tensor_dtype t' = Some INT32_TensorProto by rewrite Hist' /= datatype2.
  have [x [Ex Hx]] := matrix_int32_of_tensor_mat _ Ht Hdc1 Hty.
  have [x' [Ex' Hx']] := matrix_int32_of_tensor_mat _ Ht' Hdc2 Hty'.
  rewrite (DataType_int32 datatype1) (DataType_int32 datatype2) -Hist -Hist' Ex Ex'.
  have Hnf : tensor_dtype t != Some FLOAT_TensorProto by rewrite Hty.
  have /andP [] := Hint Hnf.
  case: (Z_of_float32 alpha) => // az _; case: (Z_of_float32 beta) => // bz _.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h1 Hx.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h2 Hx'.
  rewrite -Hk in HB.
  by apply: isSuccess_bind; apply: (gemm_int32_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB).
- have Hty : tensor_dtype t = Some INT64_TensorProto by rewrite Hist /= datatype1.
  have Hty' : tensor_dtype t' = Some INT64_TensorProto by rewrite Hist' /= datatype2.
  have [x [Ex Hx]] := matrix_int64_of_tensor_mat _ Ht Hdc1 Hty.
  have [x' [Ex' Hx']] := matrix_int64_of_tensor_mat _ Ht' Hdc2 Hty'.
  rewrite (DataType_int64 datatype1) (DataType_int64 datatype2) -Hist -Hist' Ex Ex'.
  have Hnf : tensor_dtype t != Some FLOAT_TensorProto by rewrite Hty.
  have /andP [] := Hint Hnf.
  case: (Z_of_float32 alpha) => // az _; case: (Z_of_float32 beta) => // bz _.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h1 Hx.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h2 Hx'.
  rewrite -Hk in HB.
  by apply: isSuccess_bind; apply: (gemm_int64_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB).
Qed.

Lemma broadcastable_of_mat {T} n p h w (C : matrix T) :
  (0 < h)%nat -> (0 < w)%nat -> is_mat h w C ->
  (if h == 1%nat then w == p else (h == n) && ((w == 1%nat) || (w == p))) ->
  broadcastable_matrix n p [:: h; w] C.
Proof.
move=> h0 w0 HC.
have HtC := @transpose_mat _ _ _ _ h0 HC.
rewrite /broadcastable_matrix /broadcastable_vector (@shape_mat _ _ _ _ h0 w0 HC).
move: HtC; move: (transpose C) => tC HtC.
case: h h0 HC HtC => [|[|h]] // _ HC HtC.
- move=> /eqP <-.
  case: C HC {HtC} => [|row [|? ?]] //; rewrite is_mat_cons /= => /andP [/andP [/eqP Hr _] _].
  by rewrite Nat.eqb_refl.
- case: w w0 HC HtC => [|[|w]] // _ HC HtC.
  + move=> /andP [/eqP <- _].
    case: tC HtC => [|row [|? ?]] //=; rewrite ?is_mat_cons //= ?Nat.eqb_refl //.
  + move=> /andP [/eqP <- /orP [] // /eqP <-].
    by rewrite !Nat.eqb_refl.
Qed.

Definition gemm3_dims_ok (d0 d1 d2 : seq int64) (a : seq AttributeProto) : bool :=
  let: (_, _, transA, transB) := get_gemm_attributes a in
  let n := if Z_of_int64 transA is 0%Z then (mat_dims d0).1 else (mat_dims d0).2 in
  let p := if Z_of_int64 transB is 0%Z then (mat_dims d1).2 else (mat_dims d1).1 in
  let: (h, w) := mat_dims d2 in
  [&& gemm_dims_ok d0 d1 a, dims_correct d2 &
      if h == 1%nat then w == p else (h == n) && ((w == 1%nat) || (w == p))].

Lemma gemm_three_success (t0 t1 t2 : TensorProto) (a : seq AttributeProto) :
  tensors_match [:: t0; t1; t2] -> tensorProtoSized t0 -> tensorProtoSized t1 ->
  tensorProtoSized t2 ->
  gemm3_dims_ok (get_dims t0) (get_dims t1) (get_dims t2) a ->
  (tensor_dtype t0 != Some FLOAT_TensorProto -> gemm_int_attrs_ok a) ->
  isSuccess (gemm t0 t1 t2 a).
Proof.
case/tensors_matchP => //= dtype _ /and4P [/eqP Hdtype0 /eqP Hdtype1 /eqP Hdtype2 _].
move=> Ht0 Ht1 Ht2 Hdims Hint.
case/tensorProtoSizedP: (Ht0) => dims0 dtype0 seg0 float320 int320 bytes0 int640 name0 doc0 raw_data0 ext0 loc0 double0 uint640 meta0 /[dup] Hist0 -> /= datatype0 sized0 sizes0;
case/tensorProtoSizedP: (Ht1) => dims1 dtype1 seg1 float321 int321 bytes1 int641 name1 doc1 raw_data1 ext1 loc1 double1 uint641 meta1 /[dup] Hist1 -> /= datatype1 sized1 sizes1;
case/tensorProtoSizedP: (Ht2) => dims2 dtype2 seg2 float322 int322 bytes2 int642 name2 doc2 raw_data2 ext2 loc2 double2 uint642 meta2 /[dup] Hist2 -> /= datatype2 sized2 sizes2 => //=;
have := eq_trans Hdtype0 (esym Hdtype1);
have := eq_trans Hdtype0 (esym Hdtype2) => //=;
rewrite Hist0 Hist1 Hist2 /= datatype0 datatype1 datatype2 // => _ _;
rewrite /gemm;
rewrite -!Hist0 -!Hist1 -!Hist2;
move: Hdims Hint;
rewrite /gemm3_dims_ok /gemm_dims_ok /gemm_int_attrs_ok;
case: (get_gemm_attributes a) => [[[alpha beta] transA] transB];
case EC: (mat_dims (get_dims t2)) => [hC wC];
move=> /and3P [/and3P [Hdc0 Hdc1 /eqP Hk] Hdc2 HbC] Hint.
all: have Hdc2' : dims_correct dims2 by move: Hdc2; rewrite Hist2.
all: have EC' : mat_dims dims2 = (hC, wC) by move: EC; rewrite Hist2.
all: have /andP [h0 w0] := mat_dims_pos _ Hdc0.
all: have /andP [h1 w1] := mat_dims_pos _ Hdc1.
all: have /andP [h2 w2] := mat_dims_pos _ Hdc2; rewrite EC /= in h2 w2.
all: have n0 := @if_Z0_pos (Z_of_int64 transA) _ _ h0 w0.
all: have k0 := @if_Z0_pos (Z_of_int64 transA) _ _ w0 h0.
all: have p0 := @if_Z0_pos (Z_of_int64 transB) _ _ w1 h1.
- have Hty0 : tensor_dtype t0 = Some FLOAT_TensorProto by rewrite Hist0 /= datatype0.
  have Hty1 : tensor_dtype t1 = Some FLOAT_TensorProto by rewrite Hist1 /= datatype1.
  have Hty2 : tensor_dtype t2 = Some FLOAT_TensorProto by rewrite Hist2 /= datatype2.
  have [x0 [Ex0 Hx0]] := matrix_float32_of_tensor_mat _ Ht0 Hdc0 Hty0.
  have [x1 [Ex1 Hx1]] := matrix_float32_of_tensor_mat _ Ht1 Hdc1 Hty1.
  have [x2 [Ex2 Hx2]] := matrix_float32_of_tensor_mat _ Ht2 Hdc2 Hty2.
  rewrite (DataType_float datatype0) (DataType_float datatype1) (DataType_float datatype2).
  rewrite Ex0 Ex1 Ex2.
  rewrite EC /= in Hx2.
  rewrite (convert_dims_mat _ Hdc2') EC'.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h0 Hx0.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h1 Hx1.
  rewrite -Hk in HB.
  have Hbc := @broadcastable_of_mat _ _ _ _ _ _ h2 w2 Hx2 HbC.
  by apply: isSuccess_bind; apply: (gemm_float32_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB Hbc).
- have Hty0 : tensor_dtype t0 = Some INT32_TensorProto by rewrite Hist0 /= datatype0.
  have Hty1 : tensor_dtype t1 = Some INT32_TensorProto by rewrite Hist1 /= datatype1.
  have Hty2 : tensor_dtype t2 = Some INT32_TensorProto by rewrite Hist2 /= datatype2.
  have [x0 [Ex0 Hx0]] := matrix_int32_of_tensor_mat _ Ht0 Hdc0 Hty0.
  have [x1 [Ex1 Hx1]] := matrix_int32_of_tensor_mat _ Ht1 Hdc1 Hty1.
  have [x2 [Ex2 Hx2]] := matrix_int32_of_tensor_mat _ Ht2 Hdc2 Hty2.
  rewrite (DataType_int32 datatype0) (DataType_int32 datatype1) (DataType_int32 datatype2).
  rewrite Ex0 Ex1 Ex2.
  rewrite EC /= in Hx2.
  rewrite (convert_dims_mat _ Hdc2') EC'.
  have Hnf : tensor_dtype t0 != Some FLOAT_TensorProto by rewrite Hty0.
  have /andP [] := Hint Hnf.
  case: (Z_of_float32 alpha) => // az _; case: (Z_of_float32 beta) => // bz _.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h0 Hx0.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h1 Hx1.
  rewrite -Hk in HB.
  have Hbc := @broadcastable_of_mat _ _ _ _ _ _ h2 w2 Hx2 HbC.
  by apply: isSuccess_bind; apply: (gemm_int32_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB Hbc).
- have Hty0 : tensor_dtype t0 = Some INT64_TensorProto by rewrite Hist0 /= datatype0.
  have Hty1 : tensor_dtype t1 = Some INT64_TensorProto by rewrite Hist1 /= datatype1.
  have Hty2 : tensor_dtype t2 = Some INT64_TensorProto by rewrite Hist2 /= datatype2.
  have [x0 [Ex0 Hx0]] := matrix_int64_of_tensor_mat _ Ht0 Hdc0 Hty0.
  have [x1 [Ex1 Hx1]] := matrix_int64_of_tensor_mat _ Ht1 Hdc1 Hty1.
  have [x2 [Ex2 Hx2]] := matrix_int64_of_tensor_mat _ Ht2 Hdc2 Hty2.
  rewrite (DataType_int64 datatype0) (DataType_int64 datatype1) (DataType_int64 datatype2).
  rewrite Ex0 Ex1 Ex2.
  rewrite EC /= in Hx2.
  rewrite (convert_dims_mat _ Hdc2') EC'.
  have Hnf : tensor_dtype t0 != Some FLOAT_TensorProto by rewrite Hty0.
  have /andP [] := Hint Hnf.
  case: (Z_of_float32 alpha) => // az _; case: (Z_of_float32 beta) => // bz _.
  have HA := @trans_mat _ _ _ _ (Z_of_int64 transA) h0 Hx0.
  have HB := @trans_mat _ _ _ _ (Z_of_int64 transB) h1 Hx1.
  rewrite -Hk in HB.
  have Hbc := @broadcastable_of_mat _ _ _ _ _ _ h2 w2 Hx2 HbC.
  by apply: isSuccess_bind; apply: (gemm_int64_success _ _ _ _ _ _ _ _ _ _ _ n0 k0 p0 HA HB Hbc).
Qed.

Lemma relu_success (t : TensorProto) : tensorProtoSized t -> isSuccess (op_relu.relu t).
Proof.
case/tensorProtoSizedP => dims dtype seg float32 int32 bytes int64 name doc raw_data ext loc double uint64 meta -> /= datatype sized sizes.
rewrite (DataType_float datatype).
have := dims_prod_pos sized.
rewrite -sizes.
by case: float32 sizes.
rewrite (DataType_int32 datatype).
have := dims_prod_pos sized.
rewrite -sizes.
by case: int32 sizes.
rewrite (DataType_int64 datatype).
have := dims_prod_pos sized.
rewrite -sizes.
by case: int64 sizes.
Qed.

Definition get_attributes (n : NodeProto) : seq AttributeProto :=
  let : NodeProto_constructor _ _ _ _ _ _ a _ _ _ := n in a.

Lemma rem_cat (n : NodeProto) (nodes : seq NodeProto)
                  (inputs : seq ValueInfoProto)
                  (initialisers : seq TensorProto) :
  ([seq node x0
      | x0 <- rem n (rev nodes)] ++
   [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers])%SEQ =
  rem
    (node n)
    ([seq node x0 | x0 <- List.rev nodes] ++
     [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers]).
Proof.
have Hinj : injective node by move=> ? ? [].
have remE s : rem (node n) (map node s) = map node (rem n s).
  by elim: s => //= y s ->; rewrite (eqtype.inj_eq Hinj); case: ifP.
have catE (T : eqType) (x : T) (s1 s2 : seq T) :
    rem x (s1 ++ s2)%SEQ = if x \in s1 then (rem x s1 ++ s2)%SEQ else (s1 ++ rem x s2)%SEQ.
  elim: s1 => //= y s1 ->; rewrite in_cons.
  case: (eqVneq x y) => [->|nxy]; first by [].
  by case: (x \in s1).
rewrite rev_is_rev catE mem_map // remE.
case: ifP => nin //.
rewrite (rem_id (negbT nin)) rem_id //.
by rewrite mem_cat; apply/norP; split; apply/mapP => -[].
Qed.

(** TODO Add to mathcomp **)
Lemma subset_all {T : eqType} {p : pred T} {xs ys : seq T}
  : {subset xs <= ys} -> all p ys -> all p xs.
Proof.
move=> sub /allP Hall.
apply/allP => x xin.
apply/Hall/sub/xin.
Qed.

(** Evaluation only depends on the lookups that succeed. *)
Lemma eval_lookup_mono d xs V1 V2 w t :
  (forall i u, find_vertex V1 i = [:: u] -> find_vertex V2 i = [:: u]) ->
  onnx_evaluator_recursive d xs V1 w = Success t ->
  onnx_evaluator_recursive d xs V2 w = Success t.
Proof.
move=> P; elim: d w t => // d IH w t.
case: w => [[ins outs ? [op|] ? ? attrs ? ? ?]|?|?|[[nm|] ? ? ?]] //=.
- case: ifP => _.
  + case: ins => [|a [|b [|c [|? ?]]]] //=.
    * case Fa: (find_vertex V1 a) => [|va [|? ?]] //=.
      case Fb: (find_vertex V1 b) => [|vb [|? ?]] //=.
      rewrite (P _ _ Fa) (P _ _ Fb).
      case Ea: (onnx_evaluator_recursive d xs V1 va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs V1 vb) => [tb|?] //=.
      by rewrite (IH _ _ Ea) (IH _ _ Eb).
    * case Fa: (find_vertex V1 a) => [|va [|? ?]] //=.
      case Fb: (find_vertex V1 b) => [|vb [|? ?]] //=.
      case Fc: (find_vertex V1 c) => [|vc [|? ?]] //=.
      rewrite (P _ _ Fa) (P _ _ Fb) (P _ _ Fc).
      case Ea: (onnx_evaluator_recursive d xs V1 va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs V1 vb) => [tb|?] //=;
      case Ec: (onnx_evaluator_recursive d xs V1 vc) => [tc|?] //=.
      by rewrite (IH _ _ Ea) (IH _ _ Eb) (IH _ _ Ec).
  + case: ifP => // _.
    case: ins => [|a [|? ?]] //=.
    case Fa: (find_vertex V1 a) => [|va [|? ?]] //=.
    rewrite (P _ _ Fa).
    case Ea: (onnx_evaluator_recursive d xs V1 va) => [ta|?] //=.
    by rewrite (IH _ _ Ea).
- rewrite -!/(find_vertex _ nm).
  case Fa: (find_vertex V1 nm) => [|va [|? ?]] //=.
  by rewrite (P _ _ Fa); exact: IH.
Qed.

Lemma find_vertex_rem_other s x i :
  i \notin vnames x -> find_vertex (rem x s) i = find_vertex s i.
Proof.
rewrite !find_vertexE -vertex_has_nameE => nx.
elim: s => //= y s IH.
case: eqP => [->|_] /=; first by rewrite (negbTE nx).
by rewrite IH.
Qed.

(** Removing an acyclic node only makes evaluation fail more often. *)
Lemma onnx_evaluator_rec_S (depth : nat) (user_inputs : seq TensorProto)
                           (vertices : seq vertex) (n : NodeProto) (w : vertex)
  : acyclic_at vertices (node n)
 -> isSuccess (onnx_evaluator_recursive depth user_inputs (rem (node n) vertices) w)
 -> isSuccess (onnx_evaluator_recursive depth user_inputs vertices w).
Proof.
move=> ac /isSuccessP [t E].
have P i u : find_vertex (rem (node n) vertices) i = [:: u] -> find_vertex vertices i = [:: u].
  move=> F; have ni : i \notin vnames (node n).
    by apply/negP => /(acyclic_at_owns ac) Fo; rewrite (find_vertex_rem _ _ _ Fo) in F.
  by rewrite -(find_vertex_rem_other _ _ _ ni).
by rewrite (eval_lookup_mono _ _ _ _ _ _ P E).
Qed.

(** * Successful evaluation returns sized tensors *)

Lemma byte_of_toN (x : Z) :
  Z.of_N (to_N (match of_N (Z.to_N (x mod 256)) with Some b => b | None => Byte.x00 end)) =
  (x mod 256)%Z.
Proof.
have [H0 H1] : (0 <= x mod 256 < 256)%Z by apply: Z.mod_pos_bound.
case E: (of_N _) => [b|].
  by rewrite (to_of_N _ E) Z2N.id.
move/of_N_None_iff/N2Z.inj_lt: E; rewrite Z2N.id //=; lia.
Qed.

Lemma Z_of_uint64_of_Z z :
  Z_of_uint64 (uint64_of_Z z) = (z mod 18446744073709551616)%Z.
Proof.
rewrite /Z_of_uint64 /uint64_of_Z; cbv zeta beta iota.
rewrite !byte_of_toN.
rewrite -!Z.div_div; try lia.
set q1 := (z / 256)%Z; set q2 := (q1 / 256)%Z; set q3 := (q2 / 256)%Z.
set q4 := (q3 / 256)%Z; set q5 := (q4 / 256)%Z; set q6 := (q5 / 256)%Z.
set q7 := (q6 / 256)%Z.
have E0 := Z.div_mod z 256; have E1 := Z.div_mod q1 256; have E2 := Z.div_mod q2 256.
have E3 := Z.div_mod q3 256; have E4 := Z.div_mod q4 256; have E5 := Z.div_mod q5 256.
have E6 := Z.div_mod q6 256; have E7 := Z.div_mod q7 256.
have Hq : (z / 18446744073709551616 = q7 / 256)%Z.
  rewrite /q7 /q6 /q5 /q4 /q3 /q2 /q1 !Z.div_div; try lia; by [].
rewrite (Z.mod_eq z 18446744073709551616) ?Hq; lia.
Qed.

Lemma Z_of_uint64_bound i : (0 <= Z_of_uint64 i <= 18446744073709551615)%Z.
Proof.
case: i => [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0]; rewrite /Z_of_uint64.
have B b : (0 <= Z.of_N (to_N b) <= 255)%Z.
  by split; [lia|]; have := to_N_bounded b; lia.
have := B b0; have := B b1; have := B b2; have := B b3;
have := B b4; have := B b5; have := B b6; have := B b7.
move: (Z.of_N (to_N b7)) (Z.of_N (to_N b6)) (Z.of_N (to_N b5)) (Z.of_N (to_N b4))
      (Z.of_N (to_N b3)) (Z.of_N (to_N b2)) (Z.of_N (to_N b1)) (Z.of_N (to_N b0)).
move=> x7 x6 x5 x4 x3 x2 x1 x0; lia.
Qed.

Lemma int64_max_val : int64_max = 9223372036854775807%Z.
Proof. by []. Qed.

Lemma uint64_max_val : uint64_max = 18446744073709551615%Z.
Proof. by []. Qed.

Lemma Z_of_int64_of_Z z :
  (0 <= z <= int64_max)%Z -> Z_of_int64 (int64_of_Z z) = z.
Proof.
rewrite int64_max_val => Hz.
rewrite /Z_of_int64 /int64_of_Z Z_of_uint64_of_Z Z.mod_small; try lia.
by rewrite int64_max_val; case: Z.leb_spec; lia.
Qed.

Lemma Z_of_int64_le_max i : (Z_of_int64 i <= int64_max)%Z.
Proof.
rewrite /Z_of_int64; have := Z_of_uint64_bound i.
by rewrite int64_max_val uint64_max_val; case: Z.leb_spec; lia.
Qed.

(** A dimension stored back as an int64 reads back unchanged. *)
Lemma int64_to_dim_of_nat n :
  (Z.of_nat n <= int64_max)%Z -> int64_to_dim (int64_of_Z (Z.of_nat n)) = n.
Proof.
move=> Hn; rewrite /int64_to_dim Z_of_int64_of_Z ?Nat2Z.id //; lia.
Qed.

Lemma int64_to_dim_le_max d : (Z.of_nat (int64_to_dim d) <= int64_max)%Z.
Proof.
rewrite /int64_to_dim; have := Z_of_int64_le_max d.
by case: (Z_of_int64 d) => [|p|p] //=; rewrite ?positive_nat_Z //; lia.
Qed.

Lemma list_eo_size {T} (l : seq (error_option T)) acc r :
  list_error_option_to_error_option_list l acc = Success r ->
  size r = (size l + size acc)%nat.
Proof.
elim: l acc => [|x l IH] acc /=; first by case=> <-; rewrite rev_is_rev size_rev.
by case: x => // x /IH ->; rewrite /= addnS.
Qed.

Lemma size_row_major {T} n k (m : matrix T) :
  is_mat n k m -> size (convert_to_row_major m) = (n * k)%nat.
Proof.
elim: m n => [|r m IH] n /=; first by case/andP => /eqP <-.
case/andP => /eqP <- /andP [/eqP rk mk] /=.
by rewrite app_cat size_cat (IH (size m)) ?rk ?mulSn //; apply/andP.
Qed.

Lemma ncols_mat {T k p} {m : matrix T} :
  (0 < k)%nat -> is_mat k p m ->
  (if m is row :: _ then Datatypes.length row else 0%nat) = p.
Proof.
case: m => [|r m] k0 /=; first by case/andP => /eqP k00; rewrite -k00 in k0.
by case/andP => _ /andP [/eqP <- _]; rewrite length_size.
Qed.

Lemma is_mat_size {T n k} {m : matrix T} : is_mat n k m -> size m = n.
Proof. by case/andP => /eqP. Qed.

Lemma convert_dims_correct dims hw :
  convert_dims dims = Success hw -> dims_correct dims.
Proof.
case: dims => [|h [|w [|? ?]]] //=.
  by case: (Z_of_int64 h).
by case: (Z_of_int64 h) => // ?; case: (Z_of_int64 w).
Qed.

Lemma mat_dims_le_max dims :
  (Z.of_nat (mat_dims dims).1 <= int64_max)%Z /\ (Z.of_nat (mat_dims dims).2 <= int64_max)%Z.
Proof.
have one : (Z.of_nat 1 <= int64_max)%Z by rewrite int64_max_val.
have zero : (Z.of_nat 0 <= int64_max)%Z by rewrite int64_max_val.
case: dims => [|h [|w [|? ?]]] /=; by split => //; apply: int64_to_dim_le_max.
Qed.

Lemma filterE {T} (p : pred T) (s : seq T) : List.filter p s = filter p s.
Proof. by elim: s => //= x s ->. Qed.

Lemma add_lists_float32_size {a b l} : add_lists_float32 a b = Success l -> size l = size a.
Proof.
elim: a b l => [|x a IH] [|y b] l //=; first by case=> <-.
by case E: (add_lists_float32 a b) => [l'|] // [<-] /=; rewrite (IH _ _ E).
Qed.

Lemma matrix_addition_float32_shape {n k a b r} :
  matrix_addition_float32 a b = Success r -> is_mat n k a -> is_mat n k r.
Proof.
elim: a b r n => [|ra a IH] [|rb b] r n //=; first by case=> <-.
case E: (add_lists_float32 ra rb) => [l|] //.
case E2: (matrix_addition_float32 a b) => [rr|] // [<-].
rewrite !is_mat_cons (add_lists_float32_size E) => /andP [/andP [-> /(IH _ _ _ E2) ->] ->].
done.
Qed.

Lemma matrix_multiplication_float32_shape {a b r} :
  matrix_multiplication_float32 a b = Success r ->
  is_mat (size a) (if b is row :: _ then Datatypes.length row else 0%nat) r.
Proof.
elim: a r => [|ra a IH] r /=; first by case=> <-.
case E: (list_error_option_to_error_option_list _ _) => [nr|] //.
case E2: (matrix_multiplication_float32 a b) => [rr|] // [<-].
rewrite is_mat_cons (IH _ E2) /= andbT (list_eo_size _ _ _ E) addn0.
by rewrite listmap_map size_map -length_size List.length_seq ?eqxx ?ltn0Sn.
Qed.

Lemma gemm_float32_shape {A B C al be ta tb dc r} h w h2 w2 :
  (0 < h)%nat -> (0 < w)%nat -> (0 < h2)%nat -> (0 < w2)%nat ->
  is_mat h w A -> is_mat h2 w2 B ->
  gemm_float32 A B C al be ta tb dc = Success r ->
  is_mat (if Z_of_int64 ta is 0%Z then h else w) (if Z_of_int64 tb is 0%Z then w2 else h2) r.
Proof.
move=> h0 w0 h20 w20 HA HB.
have HA' := trans_mat _ _ _ (Z_of_int64 ta) h0 HA.
have HB' := trans_mat _ _ _ (Z_of_int64 tb) h20 HB.
have k0 : (0 < if Z_of_int64 tb is 0%Z then h2 else w2)%nat by case: (Z_of_int64 tb).
rewrite /gemm_float32; cbv zeta.
case E: (matrix_multiplication_float32 _ _) => [ab|] //.
case: (broadcast_2d _ _ _ _) => [cb|] // /matrix_addition_float32_shape; apply.
move: (matrix_multiplication_float32_shape E).
by rewrite (is_mat_size (scale_matrix_float32_mat _ _ _ al HA')) (ncols_mat k0 HB').
Qed.

Lemma tensor_of_matrix_float32_sized n k (m : matrix float32) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> tensorProtoSized (tensor_of_matrix_float32 m).
Proof.
move=> n0 k0 nb kb mm.
rewrite /tensor_of_matrix_float32 (shape_mat _ _ _ n0 k0 mm) /tensorProtoSized; cbn [fst snd all].
have -> : DataType_TensorProto_of_int32 (int32_of_Z 1) = Some FLOAT_TensorProto by [].
rewrite !int64_to_dim_of_nat // n0 k0 /=.
by rewrite (size_row_major _ _ _ mm) /dims_prod !big_cons big_nil !int64_to_dim_of_nat // muln1.
Qed.

Lemma matrix_float32_of_tensor_shape {t m} :
  tensorProtoSized t -> tensor_dtype t = Some FLOAT_TensorProto ->
  matrix_float32_of_tensor t = Success m ->
  exists h w, [/\ (0 < h)%nat, (0 < w)%nat, (Z.of_nat h <= int64_max)%Z,
                  (Z.of_nat w <= int64_max)%Z & is_mat h w m].
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_float32_of_tensor_mat _ S dc D.
move: E; rewrite Ex => -[<-].
have /andP [p1 p2] := mat_dims_pos _ dc.
have [b1 b2] := mat_dims_le_max (get_dims t).
by exists (mat_dims (get_dims t)).1, (mat_dims (get_dims t)).2.
Qed.

Lemma add_lists_int32_size {a b l} : add_lists_int32 a b = Success l -> size l = size a.
Proof.
elim: a b l => [|x a IH] [|y b] l //=; first by case=> <-.
by case E: (add_lists_int32 a b) => [l'|] // [<-] /=; rewrite (IH _ _ E).
Qed.

Lemma matrix_addition_int32_shape {n k a b r} :
  matrix_addition_int32 a b = Success r -> is_mat n k a -> is_mat n k r.
Proof.
elim: a b r n => [|ra a IH] [|rb b] r n //=; first by case=> <-.
case E: (add_lists_int32 ra rb) => [l|] //.
case E2: (matrix_addition_int32 a b) => [rr|] // [<-].
rewrite !is_mat_cons (add_lists_int32_size E) => /andP [/andP [-> /(IH _ _ _ E2) ->] ->].
done.
Qed.

Lemma matrix_multiplication_int32_shape {a b r} :
  matrix_multiplication_int32 a b = Success r ->
  is_mat (size a) (if b is row :: _ then Datatypes.length row else 0%nat) r.
Proof.
elim: a r => [|ra a IH] r /=; first by case=> <-.
case E: (list_error_option_to_error_option_list _ _) => [nr|] //.
case E2: (matrix_multiplication_int32 a b) => [rr|] // [<-].
rewrite is_mat_cons (IH _ E2) /= andbT (list_eo_size _ _ _ E) addn0.
by rewrite listmap_map size_map -length_size List.length_seq ?eqxx ?ltn0Sn.
Qed.

Lemma gemm_int32_shape {A B C al be ta tb dc r} h w h2 w2 :
  (0 < h)%nat -> (0 < w)%nat -> (0 < h2)%nat -> (0 < w2)%nat ->
  is_mat h w A -> is_mat h2 w2 B ->
  gemm_int32 A B C al be ta tb dc = Success r ->
  is_mat (if Z_of_int64 ta is 0%Z then h else w) (if Z_of_int64 tb is 0%Z then w2 else h2) r.
Proof.
move=> h0 w0 h20 w20 HA HB.
have HA' := trans_mat _ _ _ (Z_of_int64 ta) h0 HA.
have HB' := trans_mat _ _ _ (Z_of_int64 tb) h20 HB.
have k0 : (0 < if Z_of_int64 tb is 0%Z then h2 else w2)%nat by case: (Z_of_int64 tb).
rewrite /gemm_int32; cbv zeta.
case E: (matrix_multiplication_int32 _ _) => [ab|] //.
case: (broadcast_2d _ _ _ _) => [cb|] // /matrix_addition_int32_shape; apply.
move: (matrix_multiplication_int32_shape E).
by rewrite (is_mat_size (scale_matrix_int32_mat _ _ _ al HA')) (ncols_mat k0 HB').
Qed.

Lemma tensor_of_matrix_int32_sized n k (m : matrix int32) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> tensorProtoSized (tensor_of_matrix_int32 m).
Proof.
move=> n0 k0 nb kb mm.
rewrite /tensor_of_matrix_int32 (shape_mat _ _ _ n0 k0 mm) /tensorProtoSized; cbn [fst snd all].
have -> : DataType_TensorProto_of_int32 (int32_of_Z 6) = Some INT32_TensorProto by [].
rewrite !int64_to_dim_of_nat // n0 k0 /=.
by rewrite (size_row_major _ _ _ mm) /dims_prod !big_cons big_nil !int64_to_dim_of_nat // muln1.
Qed.

Lemma matrix_int32_of_tensor_shape {t m} :
  tensorProtoSized t -> tensor_dtype t = Some INT32_TensorProto ->
  matrix_int32_of_tensor t = Success m ->
  exists h w, [/\ (0 < h)%nat, (0 < w)%nat, (Z.of_nat h <= int64_max)%Z,
                  (Z.of_nat w <= int64_max)%Z & is_mat h w m].
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_int32_of_tensor_mat _ S dc D.
move: E; rewrite Ex => -[<-].
have /andP [p1 p2] := mat_dims_pos _ dc.
have [b1 b2] := mat_dims_le_max (get_dims t).
by exists (mat_dims (get_dims t)).1, (mat_dims (get_dims t)).2.
Qed.

Lemma add_lists_int64_size {a b l} : add_lists_int64 a b = Success l -> size l = size a.
Proof.
elim: a b l => [|x a IH] [|y b] l //=; first by case=> <-.
by case E: (add_lists_int64 a b) => [l'|] // [<-] /=; rewrite (IH _ _ E).
Qed.

Lemma matrix_addition_int64_shape {n k a b r} :
  matrix_addition_int64 a b = Success r -> is_mat n k a -> is_mat n k r.
Proof.
elim: a b r n => [|ra a IH] [|rb b] r n //=; first by case=> <-.
case E: (add_lists_int64 ra rb) => [l|] //.
case E2: (matrix_addition_int64 a b) => [rr|] // [<-].
rewrite !is_mat_cons (add_lists_int64_size E) => /andP [/andP [-> /(IH _ _ _ E2) ->] ->].
done.
Qed.

Lemma matrix_multiplication_int64_shape {a b r} :
  matrix_multiplication_int64 a b = Success r ->
  is_mat (size a) (if b is row :: _ then Datatypes.length row else 0%nat) r.
Proof.
elim: a r => [|ra a IH] r /=; first by case=> <-.
case E: (list_error_option_to_error_option_list _ _) => [nr|] //.
case E2: (matrix_multiplication_int64 a b) => [rr|] // [<-].
rewrite is_mat_cons (IH _ E2) /= andbT (list_eo_size _ _ _ E) addn0.
by rewrite listmap_map size_map -length_size List.length_seq ?eqxx ?ltn0Sn.
Qed.

Lemma gemm_int64_shape {A B C al be ta tb dc r} h w h2 w2 :
  (0 < h)%nat -> (0 < w)%nat -> (0 < h2)%nat -> (0 < w2)%nat ->
  is_mat h w A -> is_mat h2 w2 B ->
  gemm_int64 A B C al be ta tb dc = Success r ->
  is_mat (if Z_of_int64 ta is 0%Z then h else w) (if Z_of_int64 tb is 0%Z then w2 else h2) r.
Proof.
move=> h0 w0 h20 w20 HA HB.
have HA' := trans_mat _ _ _ (Z_of_int64 ta) h0 HA.
have HB' := trans_mat _ _ _ (Z_of_int64 tb) h20 HB.
have k0 : (0 < if Z_of_int64 tb is 0%Z then h2 else w2)%nat by case: (Z_of_int64 tb).
rewrite /gemm_int64; cbv zeta.
case E: (matrix_multiplication_int64 _ _) => [ab|] //.
case: (broadcast_2d _ _ _ _) => [cb|] // /matrix_addition_int64_shape; apply.
move: (matrix_multiplication_int64_shape E).
by rewrite (is_mat_size (scale_matrix_int64_mat _ _ _ al HA')) (ncols_mat k0 HB').
Qed.

Lemma tensor_of_matrix_int64_sized n k (m : matrix int64) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> tensorProtoSized (tensor_of_matrix_int64 m).
Proof.
move=> n0 k0 nb kb mm.
rewrite /tensor_of_matrix_int64 (shape_mat _ _ _ n0 k0 mm) /tensorProtoSized; cbn [fst snd all].
have -> : DataType_TensorProto_of_int32 (int32_of_Z 7) = Some INT64_TensorProto by [].
rewrite !int64_to_dim_of_nat // n0 k0 /=.
by rewrite (size_row_major _ _ _ mm) /dims_prod !big_cons big_nil !int64_to_dim_of_nat // muln1.
Qed.

Lemma matrix_int64_of_tensor_shape {t m} :
  tensorProtoSized t -> tensor_dtype t = Some INT64_TensorProto ->
  matrix_int64_of_tensor t = Success m ->
  exists h w, [/\ (0 < h)%nat, (0 < w)%nat, (Z.of_nat h <= int64_max)%Z,
                  (Z.of_nat w <= int64_max)%Z & is_mat h w m].
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_int64_of_tensor_mat _ S dc D.
move: E; rewrite Ex => -[<-].
have /andP [p1 p2] := mat_dims_pos _ dc.
have [b1 b2] := mat_dims_le_max (get_dims t).
by exists (mat_dims (get_dims t)).1, (mat_dims (get_dims t)).2.
Qed.

Lemma relu_sized t t' : tensorProtoSized t -> op_relu.relu t = Success t' -> tensorProtoSized t'.
Proof.
move=> St; case/tensorProtoSizedP: (St) => dims dt x3 fd i32 x6 i64 x8 x9 x10 x11 x12 x13 x14 x15 -> D P S;
rewrite /op_relu.relu; cbv beta iota;
first [rewrite (DataType_float D) | rewrite (DataType_int32 D) | rewrite (DataType_int64 D)]; cbv iota.
- by (have := dims_prod_pos P; rewrite -S;
      case: fd S => [|f fd] S; first by []; move=> _; cbv iota; case=> <-;
      rewrite /tensorProtoSized; cbv beta iota;
      have -> : DataType_TensorProto_of_int32 (int32_of_Z 1) = Some FLOAT_TensorProto by [];
      rewrite P andTb; cbv iota; by rewrite -S /= size_map).
- by (have := dims_prod_pos P; rewrite -S;
      case: i32 S => [|f i32] S; first by []; move=> _; cbv iota; case=> <-;
      rewrite /tensorProtoSized; cbv beta iota;
      have -> : DataType_TensorProto_of_int32 (int32_of_Z 6) = Some INT32_TensorProto by [];
      rewrite P andTb; cbv iota; by rewrite -S /= size_map).
- by (have := dims_prod_pos P; rewrite -S;
      case: i64 S => [|f i64] S; first by []; move=> _; cbv iota; case=> <-;
      rewrite /tensorProtoSized; cbv beta iota;
      have -> : DataType_TensorProto_of_int32 (int32_of_Z 7) = Some INT64_TensorProto by [];
      rewrite P andTb; cbv iota; by rewrite -S /= size_map).
Qed.

Lemma gemm_sized A B C a t :
  tensorProtoSized A -> tensorProtoSized B -> tensorProtoSized C ->
  gemm A B C a = Success t -> tensorProtoSized t.
Proof.
move=> SA SB SC.
rewrite /gemm; case: (get_gemm_attributes a) => [[[al be] ta] tb].
case/tensorProtoSizedP: (SA) => dimsA dA ? ? ? ? ? ? ? ? ? ? ? ? ? EA DA _ _.
all: case/tensorProtoSizedP: (SB) => dimsB dB ? ? ? ? ? ? ? ? ? ? ? ? ? EB DB _ _.
all: case/tensorProtoSizedP: (SC) => dimsC dC ? ? ? ? ? ? ? ? ? ? ? ? ? EC DC _ _.
all: rewrite {1}EA {1}EB {1}EC.
all: cbv beta iota zeta.
all: try first [rewrite (DataType_float DA) | rewrite (DataType_int32 DA) | rewrite (DataType_int64 DA)].
all: try first [rewrite (DataType_float DB) | rewrite (DataType_int32 DB) | rewrite (DataType_int64 DB)].
all: try first [rewrite (DataType_float DC) | rewrite (DataType_int32 DC) | rewrite (DataType_int64 DC)].
all: cbv iota.
all: try by [].
- case EmA: (matrix_float32_of_tensor A) => [mA|] //=; case EmB: (matrix_float32_of_tensor B) => [mB|] //=.
      case EmC: (matrix_float32_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
      case Eg: (gemm_float32 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_float32_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_float32_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_float32_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_float32_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int32_of_tensor A) => [mA|] //=; case EmB: (matrix_int32_of_tensor B) => [mB|] //=.
      case EmC: (matrix_int32_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
      case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
      case Eg: (gemm_int32 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_int32_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_int32_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_int32_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_int32_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int64_of_tensor A) => [mA|] //=; case EmB: (matrix_int64_of_tensor B) => [mB|] //=.
      case EmC: (matrix_int64_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
      case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
      case Eg: (gemm_int64 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_int64_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_int64_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_int64_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_int64_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
Qed.

Lemma gemm_two_sized A B a t :
  tensorProtoSized A -> tensorProtoSized B ->
  gemm_two_inputs A B a = Success t -> tensorProtoSized t.
Proof.
move=> SA SB.
rewrite /gemm_two_inputs; case: (get_gemm_attributes a) => [[[al be] ta] tb].
case/tensorProtoSizedP: (SA) => dimsA dA ? ? ? ? ? ? ? ? ? ? ? ? ? EA DA _ _;
case/tensorProtoSizedP: (SB) => dimsB dB ? ? ? ? ? ? ? ? ? ? ? ? ? EB DB _ _;
rewrite {1}EA {1}EB; cbv beta iota zeta; first [rewrite (DataType_float DA) | rewrite (DataType_int32 DA) | rewrite (DataType_int64 DA)]; first [rewrite (DataType_float DB) | rewrite (DataType_int32 DB) | rewrite (DataType_int64 DB)]; cbv iota; try by [].
- case EmA: (matrix_float32_of_tensor A) => [mA|] //=; case EmB: (matrix_float32_of_tensor B) => [mB|] //=.
      case Eg: (gemm_float32 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_float32_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_float32_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_float32_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_float32_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int32_of_tensor A) => [mA|] //=; case EmB: (matrix_int32_of_tensor B) => [mB|] //=.
      case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
      case Eg: (gemm_int32 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_int32_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_int32_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_int32_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_int32_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int64_of_tensor A) => [mA|] //=; case EmB: (matrix_int64_of_tensor B) => [mB|] //=.
      case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
      case Eg: (gemm_int64 _ _ _ _ _ _ _ _) => [res|] // [<-].
      have [h [w [h0 w0 hb wb HA]]] := matrix_int64_of_tensor_shape SA (etrans (f_equal tensor_dtype EA) DA) EmA.
      have [h2 [w2 [h20 w20 hb2 wb2 HB]]] := matrix_int64_of_tensor_shape SB (etrans (f_equal tensor_dtype EB) DB) EmB.
      move: (gemm_int64_shape h w h2 w2 h0 w0 h20 w20 HA HB Eg) => Hr.
      apply: (tensor_of_matrix_int64_sized _ _ _ _ _ _ _ Hr).
      all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
Qed.

(** A successful evaluation returns a sized tensor, provided the user inputs
    and the initialisers are sized. *)
Lemma eval_sized d xs items v t :
  all tensorProtoSized xs ->
  (forall t', tensor t' \in v :: items -> tensorProtoSized t') ->
  onnx_evaluator_recursive d xs items v = Success t -> tensorProtoSized t.
Proof.
move=> Sx; elim: d v t => // d IH v t St.
have Si w : w \in items -> forall t', tensor t' \in w :: items -> tensorProtoSized t'.
  move=> win t'; rewrite in_cons => /orP [/eqP tw|ti]; apply: St; rewrite in_cons.
    by rewrite tw win orbT.
  by rewrite ti orbT.
have IHf i w t'' : find_vertex items i = [:: w] ->
    onnx_evaluator_recursive d xs items w = Success t'' -> tensorProtoSized t''.
  by move=> F; apply: IH; apply: Si; exact: finds_in F.
case: v St => [[ins outs ? [op|] ? ? attrs ? ? ?]|t'|[[nm|] ? ? ?]|[[nm|] ? ? ?]] St //=.
- case: ifP => _.
  + case: ins St => [|a [|b [|c [|? ?]]]] St //=.
    * case Fa: (find_vertex items a) => [|va [|? ?]] //=.
      case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
      case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=.
      exact: gemm_two_sized (IHf _ _ _ Fa Ea) (IHf _ _ _ Fb Eb).
    * case Fa: (find_vertex items a) => [|va [|? ?]] //=.
      case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
      case Fc: (find_vertex items c) => [|vc [|? ?]] //=.
      case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=;
      case Ec: (onnx_evaluator_recursive d xs items vc) => [tc|?] //=.
      exact: gemm_sized (IHf _ _ _ Fa Ea) (IHf _ _ _ Fb Eb) (IHf _ _ _ Fc Ec).
  + case: ifP => // _.
    case: ins St => [|a [|? ?]] St //=.
    case Fa: (find_vertex items a) => [|va [|? ?]] //=.
    case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=.
    exact: relu_sized (IHf _ _ _ Fa Ea).
- by case=> <-; apply: St; exact: mem_head.
- rewrite filterE; case F: (filter _ xs) => [|u [|? ?]] //= [<-].
  have : u \in filter (tensor_has_name nm) xs by rewrite F mem_head.
  by rewrite mem_filter => /andP [_ /(allP Sx)].
- rewrite -/(find_vertex items nm).
  case F: (find_vertex items nm) => [|w [|? ?]] //=.
  exact: IHf F.
Qed.

Lemma relu_dtype t t' : op_relu.relu t = Success t' -> tensor_dtype t' = tensor_dtype t.
Proof.
case: t => dims [dt|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 dt) => [|p|p] //=; do ? case: p => [p|p|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

Lemma gemm_two_dtype A B a t :
  gemm_two_inputs A B a = Success t -> tensor_dtype t = tensor_dtype A.
Proof.
rewrite /gemm_two_inputs; case: (get_gemm_attributes a) => [[[al be] tA] tB].
case: A => dA [ta|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: B => dB [tb|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 ta) => [|p|p] //=; do ? case: p => [p|p|] //=;
case: (Z_of_int32 tb) => [|q|q] //=; do ? case: q => [q|q|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

Lemma gemm_dtype A B C a t :
  gemm A B C a = Success t -> tensor_dtype t = tensor_dtype A.
Proof.
rewrite /gemm; case: (get_gemm_attributes a) => [[[al be] tA] tB].
case: A => dA [ta|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: B => dB [tb|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: C => dC [tc|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
rewrite /DataType_TensorProto_of_int32.
case: (Z_of_int32 ta) => [|p|p] //=; do ? case: p => [p|p|] //=;
case: (Z_of_int32 tb) => [|q|q] //=; do ? case: q => [q|q|] //=;
case: (Z_of_int32 tc) => [|r|r] //=; do ? case: r => [r|r|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

(** If every leaf (user input and initialiser) has dtype dt, so does every
    successful evaluation. *)
Lemma eval_dtype d xs items v t dt :
  all (fun u => tensor_dtype u == Some dt) xs ->
  (forall t', tensor t' \in v :: items -> tensor_dtype t' = Some dt) ->
  onnx_evaluator_recursive d xs items v = Success t -> tensor_dtype t = Some dt.
Proof.
move=> Dx; elim: d v t => // d IH v t Dt.
have IHf i w t'' : find_vertex items i = [:: w] ->
    onnx_evaluator_recursive d xs items w = Success t'' -> tensor_dtype t'' = Some dt.
  move=> /finds_in win; apply: IH => t'; rewrite in_cons => /orP [/eqP tw|ti];
  by apply: Dt; rewrite in_cons ?tw ?win ?ti orbT.
case: v Dt => [[ins outs ? [op|] ? ? attrs ? ? ?]|t'|[[nm|] ? ? ?]|[[nm|] ? ? ?]] Dt //=.
- case: ifP => _.
    case: ins Dt => [|a [|b [|c [|? ?]]]] Dt //=.
      case Fa: (find_vertex items a) => [|va [|? ?]] //=.
      case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
      case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=.
      by move=> /gemm_two_dtype ->; exact: IHf Fa Ea.
    case Fa: (find_vertex items a) => [|va [|? ?]] //=.
    case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
    case Fc: (find_vertex items c) => [|vc [|? ?]] //=.
    case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
    case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=;
    case Ec: (onnx_evaluator_recursive d xs items vc) => [tc|?] //=.
    by move=> /gemm_dtype ->; exact: IHf Fa Ea.
  case: ifP => // _.
  case: ins Dt => [|a [|? ?]] Dt //=.
  case Fa: (find_vertex items a) => [|va [|? ?]] //=.
  case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=.
  by move=> /relu_dtype ->; exact: IHf Fa Ea.
- by case=> <-; apply: Dt; exact: mem_head.
- rewrite filterE; case F: (filter _ xs) => [|u [|? ?]] //= [<-].
  have : u \in filter (tensor_has_name nm) xs by rewrite F mem_head.
  by rewrite mem_filter => /andP [_ /(allP Dx) /eqP].
- rewrite -/(find_vertex items nm).
  case F: (find_vertex items nm) => [|w [|? ?]] //=.
  exact: IHf F.
Qed.

Lemma dims_correct_sized t :
  (size (get_dims t) <= 2)%nat -> tensorProtoSized t -> dims_correct (get_dims t).
Proof.
case: t => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /= + /andP [+ _].
rewrite /int64_to_dim.
case: dims => [|h [|w [|? ?]]] //=.
  by rewrite andbT => _ /ssrnat.ltP ?; apply/Z.ltb_lt; lia.
by rewrite andbT => _ /andP [/ssrnat.ltP ? /ssrnat.ltP ?]; apply/andP; split; apply/Z.ltb_lt; lia.
Qed.

Lemma relu_dims t t' : op_relu.relu t = Success t' -> get_dims t' = get_dims t.
Proof.
case: t => dims [dt|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
case: (Z_of_int32 dt) => [|p|p] //=; do ? case: p => [p|p|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

Lemma gemm_two_rank A B a t :
  gemm_two_inputs A B a = Success t -> size (get_dims t) = 2%nat.
Proof.
rewrite /gemm_two_inputs; case: (get_gemm_attributes a) => [[[al be] tA] tB].
case: A => dA [ta|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: B => dB [tb|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
case: (Z_of_int32 ta) => [|p|p] //=; do ? case: p => [p|p|] //=;
case: (Z_of_int32 tb) => [|q|q] //=; do ? case: q => [q|q|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

(** The output shape comes from A and B only: C is broadcast to it. *)
Lemma gemm_rank A B C a t :
  gemm A B C a = Success t -> size (get_dims t) = 2%nat.
Proof.
rewrite /gemm; case: (get_gemm_attributes a) => [[[al be] tA] tB].
case: A => dA [ta|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: B => dB [tb|] ? ? ? ? ? ? ? ? ? ? ? ? ?;
case: C => dC [tc|] ? ? ? ? ? ? ? ? ? ? ? ? ? //=.
case: (Z_of_int32 ta) => [|p|p] //=; do ? case: p => [p|p|] //=;
case: (Z_of_int32 tb) => [|q|q] //=; do ? case: q => [q|q|] //=;
case: (Z_of_int32 tc) => [|r|r] //=; do ? case: r => [r|r|] //=;
repeat match goal with
 | |- (match ?x with _ => _ end = Success _) -> _ => destruct x
 | |- Error _ = Success _ -> _ => discriminate
 end; by case=> <-.
Qed.

(** A successful evaluation returns correct dims, provided the user inputs and
    the initialisers are sized and have correct dims. *)
Lemma eval_dims_correct d xs items v t :
  all tensorProtoSized xs -> all (fun u => dims_correct (get_dims u)) xs ->
  (forall t', tensor t' \in v :: items -> tensorProtoSized t') ->
  (forall t', tensor t' \in v :: items -> dims_correct (get_dims t')) ->
  onnx_evaluator_recursive d xs items v = Success t -> dims_correct (get_dims t).
Proof.
move=> Sx Cx; elim: d v t => // d IH v t St Ct Et.
have Si w : w \in items -> forall P : TensorProto -> Prop,
    (forall t', tensor t' \in v :: items -> P t') ->
    forall t', tensor t' \in w :: items -> P t'.
  move=> win P H t'; rewrite in_cons => /orP [/eqP tw|ti]; apply: H; rewrite in_cons.
    by rewrite tw win orbT.
  by rewrite ti orbT.
have IHf i w t'' : find_vertex items i = [:: w] ->
    onnx_evaluator_recursive d xs items w = Success t'' ->
    tensorProtoSized t'' /\ dims_correct (get_dims t'').
  move=> /finds_in win E; split.
    exact: eval_sized Sx (Si _ win _ St) E.
  exact: IH (Si _ win _ St) (Si _ win _ Ct) E.
move: Et; clear Si; case: v St Ct => [[ins outs ? [op|] ? ? attrs ? ? ?]|t'|[[nm|] ? ? ?]|[[nm|] ? ? ?]] St Ct //=.
- case: ifP => _.
    case: ins St Ct => [|a [|b [|c [|? ?]]]] St Ct //=.
      case Fa: (find_vertex items a) => [|va [|? ?]] //=.
      case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
      case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=.
      move=> E; apply: dims_correct_sized; first by rewrite (gemm_two_rank _ _ _ _ E).
      by apply: gemm_two_sized E; [case: (IHf _ _ _ Fa Ea) | case: (IHf _ _ _ Fb Eb)].
    case Fa: (find_vertex items a) => [|va [|? ?]] //=.
    case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
    case Fc: (find_vertex items c) => [|vc [|? ?]] //=.
    case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
    case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=;
    case Ec: (onnx_evaluator_recursive d xs items vc) => [tc|?] //=.
    move=> E; apply: dims_correct_sized; first by rewrite (gemm_rank _ _ _ _ _ E).
    by apply: gemm_sized E; [case: (IHf _ _ _ Fa Ea) | case: (IHf _ _ _ Fb Eb) | case: (IHf _ _ _ Fc Ec)].
  case: ifP => // _.
  case: ins St Ct => [|a [|? ?]] St Ct //=.
  case Fa: (find_vertex items a) => [|va [|? ?]] //=.
  case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=.
  by move=> /relu_dims ->; case: (IHf _ _ _ Fa Ea).
- by case=> <-; apply: Ct; exact: mem_head.
- rewrite filterE; case F: (filter _ xs) => [|u [|? ?]] //= [<-].
  have : u \in filter (tensor_has_name nm) xs by rewrite F mem_head.
  by rewrite mem_filter => /andP [_ /(allP Cx)].
- rewrite -/(find_vertex items nm).
  case F: (find_vertex items nm) => [|w [|? ?]] //=.
  by move=> E; case: (IHf _ _ _ F E).
Qed.

Lemma matrix_float32_of_tensor_dims {t m} :
  tensorProtoSized t -> tensor_dtype t = Some FLOAT_TensorProto ->
  matrix_float32_of_tensor t = Success m ->
  is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 m /\ dims_correct (get_dims t).
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_float32_of_tensor_mat _ S dc D.
by move: E; rewrite Ex => -[<-].
Qed.

Lemma tensor_of_matrix_float32_dims n k (m : matrix float32) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> mat_dims (get_dims (tensor_of_matrix_float32 m)) = (n, k).
Proof.
move=> n0 k0 nb kb mm.
by rewrite /tensor_of_matrix_float32 (shape_mat _ _ _ n0 k0 mm) /= !int64_to_dim_of_nat.
Qed.

Lemma matrix_int32_of_tensor_dims {t m} :
  tensorProtoSized t -> tensor_dtype t = Some INT32_TensorProto ->
  matrix_int32_of_tensor t = Success m ->
  is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 m /\ dims_correct (get_dims t).
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_int32_of_tensor_mat _ S dc D.
by move: E; rewrite Ex => -[<-].
Qed.

Lemma tensor_of_matrix_int32_dims n k (m : matrix int32) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> mat_dims (get_dims (tensor_of_matrix_int32 m)) = (n, k).
Proof.
move=> n0 k0 nb kb mm.
by rewrite /tensor_of_matrix_int32 (shape_mat _ _ _ n0 k0 mm) /= !int64_to_dim_of_nat.
Qed.

Lemma matrix_int64_of_tensor_dims {t m} :
  tensorProtoSized t -> tensor_dtype t = Some INT64_TensorProto ->
  matrix_int64_of_tensor t = Success m ->
  is_mat (mat_dims (get_dims t)).1 (mat_dims (get_dims t)).2 m /\ dims_correct (get_dims t).
Proof.
move=> S D E.
have dc : dims_correct (get_dims t).
  move: E; case: t {S D} => dims ? ? ? ? ? ? ? ? ? ? ? ? ? ? /=.
  by case C: (convert_dims dims) => [hw|] // _; exact: convert_dims_correct C.
have [x [Ex Hx]] := matrix_int64_of_tensor_mat _ S dc D.
by move: E; rewrite Ex => -[<-].
Qed.

Lemma tensor_of_matrix_int64_dims n k (m : matrix int64) :
  (0 < n)%nat -> (0 < k)%nat -> (Z.of_nat n <= int64_max)%Z -> (Z.of_nat k <= int64_max)%Z ->
  is_mat n k m -> mat_dims (get_dims (tensor_of_matrix_int64 m)) = (n, k).
Proof.
move=> n0 k0 nb kb mm.
by rewrite /tensor_of_matrix_int64 (shape_mat _ _ _ n0 k0 mm) /= !int64_to_dim_of_nat.
Qed.

(** The output of Gemm is (rows of A', columns of B'); C is only broadcast. *)
Lemma gemm_two_mat_dims A B a t :
  tensorProtoSized A -> tensorProtoSized B ->
  gemm_two_inputs A B a = Success t ->
  mat_dims (get_dims t) =
  (let: (_, _, tA, tB) := get_gemm_attributes a in
   (if Z_of_int64 tA is 0%Z then (mat_dims (get_dims A)).1 else (mat_dims (get_dims A)).2,
    if Z_of_int64 tB is 0%Z then (mat_dims (get_dims B)).2 else (mat_dims (get_dims B)).1)).
Proof.
move=> SA SB.
rewrite /gemm_two_inputs; case: (get_gemm_attributes a) => [[[al be] ta] tb].
case/tensorProtoSizedP: (SA) => dimsA dA ? ? ? ? ? ? ? ? ? ? ? ? ? EA DA _ _;
case/tensorProtoSizedP: (SB) => dimsB dB ? ? ? ? ? ? ? ? ? ? ? ? ? EB DB _ _;
rewrite {1}EA {1}EB; cbv beta iota zeta; first [rewrite (DataType_float DA) | rewrite (DataType_int32 DA) | rewrite (DataType_int64 DA)]; first [rewrite (DataType_float DB) | rewrite (DataType_int32 DB) | rewrite (DataType_int64 DB)]; cbv iota; try by [].
- case EmA: (matrix_float32_of_tensor A) => [mA|] //=; case EmB: (matrix_float32_of_tensor B) => [mB|] //=.
  case Eg: (gemm_float32 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_float32_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_float32_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_float32_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_float32_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int32_of_tensor A) => [mA|] //=; case EmB: (matrix_int32_of_tensor B) => [mB|] //=.
  case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
  case Eg: (gemm_int32 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_int32_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_int32_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_int32_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_int32_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int64_of_tensor A) => [mA|] //=; case EmB: (matrix_int64_of_tensor B) => [mB|] //=.
  case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
  case Eg: (gemm_int64 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_int64_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_int64_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_int64_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_int64_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
Qed.

Lemma gemm_mat_dims A B C a t :
  tensorProtoSized A -> tensorProtoSized B -> tensorProtoSized C ->
  gemm A B C a = Success t ->
  mat_dims (get_dims t) =
  (let: (_, _, tA, tB) := get_gemm_attributes a in
   (if Z_of_int64 tA is 0%Z then (mat_dims (get_dims A)).1 else (mat_dims (get_dims A)).2,
    if Z_of_int64 tB is 0%Z then (mat_dims (get_dims B)).2 else (mat_dims (get_dims B)).1)).
Proof.
move=> SA SB SC.
rewrite /gemm; case: (get_gemm_attributes a) => [[[al be] ta] tb].
case/tensorProtoSizedP: (SA) => dimsA dA ? ? ? ? ? ? ? ? ? ? ? ? ? EA DA _ _.
all: case/tensorProtoSizedP: (SB) => dimsB dB ? ? ? ? ? ? ? ? ? ? ? ? ? EB DB _ _.
all: case/tensorProtoSizedP: (SC) => dimsC dC ? ? ? ? ? ? ? ? ? ? ? ? ? EC DC _ _.
all: rewrite {1}EA {1}EB {1}EC.
all: cbv beta iota zeta.
all: try first [rewrite (DataType_float DA) | rewrite (DataType_int32 DA) | rewrite (DataType_int64 DA)].
all: try first [rewrite (DataType_float DB) | rewrite (DataType_int32 DB) | rewrite (DataType_int64 DB)].
all: try first [rewrite (DataType_float DC) | rewrite (DataType_int32 DC) | rewrite (DataType_int64 DC)].
all: cbv iota.
all: try by [].
- case EmA: (matrix_float32_of_tensor A) => [mA|] //=; case EmB: (matrix_float32_of_tensor B) => [mB|] //=.
  case EmC: (matrix_float32_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
  case Eg: (gemm_float32 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_float32_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_float32_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_float32_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_float32_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int32_of_tensor A) => [mA|] //=; case EmB: (matrix_int32_of_tensor B) => [mB|] //=.
  case EmC: (matrix_int32_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
  case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
  case Eg: (gemm_int32 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_int32_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_int32_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_int32_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_int32_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
- case EmA: (matrix_int64_of_tensor A) => [mA|] //=; case EmB: (matrix_int64_of_tensor B) => [mB|] //=.
  case EmC: (matrix_int64_of_tensor C) => [mC|] //=; case: (convert_dims _) => [[hc wc]|] //=.
  case: (Z_of_float32 al) => [az|] //=; case: (Z_of_float32 be) => [bz|] //=.
  case Eg: (gemm_int64 _ _ _ _ _ _ _ _) => [res|] // [<-].
  have [HA dcA] := matrix_int64_of_tensor_dims SA (etrans (f_equal tensor_dtype EA) DA) EmA.
  have [HB dcB] := matrix_int64_of_tensor_dims SB (etrans (f_equal tensor_dtype EB) DB) EmB.
  have /andP [h0 w0] := mat_dims_pos _ dcA; have /andP [h20 w20] := mat_dims_pos _ dcB.
  have [hb wb] := mat_dims_le_max (get_dims A); have [hb2 wb2] := mat_dims_le_max (get_dims B).
  move: (gemm_int64_shape _ _ _ _ h0 w0 h20 w20 HA HB Eg) => Hr.
  apply: (tensor_of_matrix_int64_dims _ _ _ _ _ _ _ Hr).
  all: try by [case: (Z_of_int64 ta) => [|?|?]; cbv iota | case: (Z_of_int64 tb) => [|?|?]; cbv iota].
Qed.

(** Static check of a single Gemm node: if its inputs evaluate to tensors with
    the annotated shapes s0 and s1, and those shapes agree on the inner
    dimension, then gemm_dims_ok holds. *)
Lemma static_gemm_dims_ok t0 t1 a (s0 s1 : nat * nat) :
  dims_correct (get_dims t0) -> dims_correct (get_dims t1) ->
  mat_dims (get_dims t0) = s0 -> mat_dims (get_dims t1) = s1 ->
  (let: (_, _, tA, tB) := get_gemm_attributes a in
   (if Z_of_int64 tA is 0%Z then s0.2 else s0.1) ==
   (if Z_of_int64 tB is 0%Z then s1.1 else s1.2)) ->
  gemm_dims_ok (get_dims t0) (get_dims t1) a.
Proof.
move=> c0 c1 <- <-; rewrite /gemm_dims_ok.
by case: (get_gemm_attributes a) => [[[? ?] ?] ?]; rewrite c0 c1.
Qed.

(** Given a shape annotation sh that is checked locally at every vertex, every
    successful evaluation returns a tensor of the annotated shape. *)
Lemma eval_static_dims d xs items (vs : seq vertex) (sh : vertex -> nat * nat) v t :
  {subset items <= vs} -> v \in vs ->
  all tensorProtoSized xs -> all (fun u => dims_correct (get_dims u)) xs ->
  (forall t', tensor t' \in vs -> tensorProtoSized t') ->
  (forall t', tensor t' \in vs -> dims_correct (get_dims t')) ->
  (** initialisers have their annotated shape *)
  (forall t', tensor t' \in vs -> sh (tensor t') = mat_dims (get_dims t')) ->
  (** user inputs have their annotated shape *)
  (forall i nm u, input i \in vs -> value_name i = Some nm ->
     u \in xs -> tensor_has_name nm u -> sh (input i) = mat_dims (get_dims u)) ->
  (** an output has the shape of the vertex it names *)
  (forall o nm w, output o \in vs -> value_name o = Some nm ->
     find_vertex items nm = [:: w] -> sh (output o) = sh w) ->
  (** Relu keeps the shape of its input *)
  (forall outs nm dom ov attrs doc meta x a w,
     let n := NodeProto_constructor [:: a] outs nm (Some """Relu""") dom ov attrs doc meta x in
     node n \in vs -> find_vertex items a = [:: w] -> sh (node n) = sh w) ->
  (** Gemm has shape (rows of A', columns of B') *)
  (forall ins outs nm dom ov attrs doc meta x a b c wa wb,
     let n := NodeProto_constructor ins outs nm (Some """Gemm""") dom ov attrs doc meta x in
     node n \in vs -> ins = [:: a; b] \/ ins = [:: a; b; c] ->
     find_vertex items a = [:: wa] -> find_vertex items b = [:: wb] ->
     sh (node n) =
     (let: (_, _, tA, tB) := get_gemm_attributes attrs in
      (if Z_of_int64 tA is 0%Z then (sh wa).1 else (sh wa).2,
       if Z_of_int64 tB is 0%Z then (sh wb).2 else (sh wb).1))) ->
  onnx_evaluator_recursive d xs items v = Success t -> mat_dims (get_dims t) = sh v.
Proof.
move=> sub + Sx Cx St Ct Lt Li Lo Lr Lg.
elim: d v t => // d IH v t vin.
have Pw (P : TensorProto -> Prop) : (forall t', tensor t' \in vs -> P t') ->
    forall w, w \in items -> forall t', tensor t' \in w :: items -> P t'.
  move=> HP w win t'; rewrite in_cons => /orP [/eqP tw|/sub]; last exact: HP.
  by apply: HP; rewrite tw; apply: sub.
have IHf i w t'' : find_vertex items i = [:: w] ->
    onnx_evaluator_recursive d xs items w = Success t'' ->
    [/\ tensorProtoSized t'', dims_correct (get_dims t'') & mat_dims (get_dims t'') = sh w].
  move=> /finds_in win E; split.
  - exact: eval_sized Sx (Pw _ St _ win) E.
  - exact: eval_dims_correct Sx Cx (Pw _ St _ win) (Pw _ Ct _ win) E.
  - exact: IH (sub _ win) E.
move: vin; case: v => [[ins outs nm [op|] dom ov attrs doc meta x]|t'|[[nmi|] ? ? ?]|[[nmo|] ? ? ?]] vin //=.
- case: ifP => Hs.
    move/String.eqb_eq: Hs => ?; subst op.
    case: ins vin => [|a [|b [|c [|? ?]]]] vin //=.
      case Fa: (find_vertex items a) => [|va [|? ?]] //=.
      case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
      case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
      case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=.
      move=> E; have [Sa _ Ma] := IHf _ _ _ Fa Ea; have [Sb _ Mb] := IHf _ _ _ Fb Eb.
      rewrite (gemm_two_mat_dims _ _ _ _ Sa Sb E) Ma Mb.
      by rewrite (Lg _ _ _ _ _ _ _ _ _ a b a va vb vin (or_introl erefl) Fa Fb).
    case Fa: (find_vertex items a) => [|va [|? ?]] //=.
    case Fb: (find_vertex items b) => [|vb [|? ?]] //=.
    case Fc: (find_vertex items c) => [|vc [|? ?]] //=.
    case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=;
    case Eb: (onnx_evaluator_recursive d xs items vb) => [tb|?] //=;
    case Ec: (onnx_evaluator_recursive d xs items vc) => [tc|?] //=.
    move=> E; have [Sa _ Ma] := IHf _ _ _ Fa Ea; have [Sb _ Mb] := IHf _ _ _ Fb Eb.
    have [Sc _ _] := IHf _ _ _ Fc Ec.
    rewrite (gemm_mat_dims _ _ _ _ _ Sa Sb Sc E) Ma Mb.
    by rewrite (Lg _ _ _ _ _ _ _ _ _ a b c va vb vin (or_intror erefl) Fa Fb).
  case: ifP => // Hr.
  move/String.eqb_eq: Hr => ?; subst op.
  case: ins vin => [|a [|? ?]] vin //=.
  case Fa: (find_vertex items a) => [|va [|? ?]] //=.
  case Ea: (onnx_evaluator_recursive d xs items va) => [ta|?] //=.
  move=> /relu_dims ->; have [_ _ Ma] := IHf _ _ _ Fa Ea.
  by rewrite Ma (Lr _ _ _ _ _ _ _ _ a va vin Fa).
- by case=> <-; rewrite (Lt _ vin).
- rewrite filterE; case F: (filter _ xs) => [|u [|? ?]] //= [<-].
  have : u \in filter (tensor_has_name nmi) xs by rewrite F mem_head.
  by rewrite mem_filter => /andP [hn ux]; rewrite (Li _ nmi u vin erefl ux hn).
- rewrite -/(find_vertex items nmo).
  case F: (find_vertex items nmo) => [|w [|? ?]] //= E.
  have [_ _ Mw] := IHf _ _ _ F E.
  by rewrite Mw (Lo _ nmo w vin erefl F).
Qed.

(** The static shape of a value name: an initialiser's own dims, otherwise the
    first declaration of that name. *)
Definition name_shape (initialisers : seq TensorProto) (decls : seq ValueInfoProto)
  (s : string) : nat * nat :=
  if List.find (tensor_has_name s) initialisers is Some t then mat_dims (get_dims t)
  else if List.find (fun v => value_name v == Some s) decls is Some v then
    if value_dims v is Some d then mat_dims d else (0, 0)%nat
  else (0, 0)%nat.

(** Local shape check of a node against the static shapes of its input and
    output names.  A Gemm needs matching inner dimensions and a C that
    broadcasts to the output; every output name has the computed shape. *)
Definition node_shape_ok (shn : string -> nat * nat) (n : NodeProto) : bool :=
  if n is NodeProto_constructor ins outs _ (Some s) _ _ attrs _ _ _ then
    let outs_are S := (outs != [::]) && all (fun o => shn o == S) outs in
    if (s =? """Gemm""")%string then
      if ins is a :: b :: rest then
        let: (_, _, tA, tB) := get_gemm_attributes attrs in
        let N := if Z_of_int64 tA is 0%Z then (shn a).1 else (shn a).2 in
        let P := if Z_of_int64 tB is 0%Z then (shn b).2 else (shn b).1 in
        [&& (if Z_of_int64 tA is 0%Z then (shn a).2 else (shn a).1) ==
            (if Z_of_int64 tB is 0%Z then (shn b).1 else (shn b).2),
            outs_are (N, P) &
            if rest is [:: c] then
              let: (h, w) := shn c in
              if h == 1%nat then w == P else (h == N) && ((w == 1%nat) || (w == P))
            else rest == [::]]
      else false
    else if (s =? """Relu""")%string then
      if ins is [:: a] then outs_are (shn a) else false
    else false
  else false.

Lemma node_shape_ok_outs shn n :
  node_shape_ok shn n ->
  exists S, (node_outputs n != [::]) && all (fun o => shn o == S) (node_outputs n).
Proof.
case: n => ins outs ? [s|] ? ? attrs ? ? ? //=.
case: ifP => _.
  case: ins => [|a [|b rest]] //.
  by case: (get_gemm_attributes attrs) => [[[? ?] tA] tB] /and3P [_ H _]; eexists; exact: H.
case: ifP => // _; case: ins => [|a [|? ?]] // H.
by exists (shn a).
Qed.

Lemma node_shape_relu shn a outs nm dom ov attrs doc meta x :
  node_shape_ok shn (NodeProto_constructor [:: a] outs nm (Some """Relu""") dom ov attrs doc meta x) ->
  shn (seq.head ""%string outs) = shn a.
Proof. by rewrite /node_shape_ok /=; case: outs => [|o os] //= /andP [/eqP ->]. Qed.

Lemma node_shape_gemm shn a b rest outs nm dom ov attrs doc meta x :
  node_shape_ok shn (NodeProto_constructor [:: a, b & rest] outs nm (Some """Gemm""") dom ov attrs doc meta x) ->
  let: (_, _, tA, tB) := get_gemm_attributes attrs in
  ((if Z_of_int64 tA is 0%Z then (shn a).2 else (shn a).1) ==
   (if Z_of_int64 tB is 0%Z then (shn b).1 else (shn b).2)) &&
  (shn (seq.head ""%string outs) ==
   (if Z_of_int64 tA is 0%Z then (shn a).1 else (shn a).2,
    if Z_of_int64 tB is 0%Z then (shn b).2 else (shn b).1)).
Proof.
rewrite /node_shape_ok; case: (get_gemm_attributes attrs) => [[[? ?] tA] tB] /=.
case: outs => [|o os] /=; first by rewrite andbF.
by case/and3P => -> /andP [/eqP -> _] _; rewrite eqxx.
Qed.

Lemma node_shape_gemm3 shn a b c outs nm dom ov attrs doc meta x :
  node_shape_ok shn (NodeProto_constructor [:: a; b; c] outs nm (Some """Gemm""") dom ov attrs doc meta x) ->
  let: (_, _, tA, tB) := get_gemm_attributes attrs in
  let N := if Z_of_int64 tA is 0%Z then (shn a).1 else (shn a).2 in
  let P := if Z_of_int64 tB is 0%Z then (shn b).2 else (shn b).1 in
  let: (h, w) := shn c in
  if h == 1%nat then w == P else (h == N) && ((w == 1%nat) || (w == P)).
Proof.
rewrite /node_shape_ok; case: (get_gemm_attributes attrs) => [[[? ?] tA] tB] /=.
by case/and3P.
Qed.

(** Every vertex found under a name has that name's static shape. *)
Lemma graph_sh_find nodes inputs initialisers shn a w :
  all (node_shape_ok shn) nodes ->
  find_vertex (graph_items nodes inputs initialisers) a = [:: w] ->
  shn (seq.head ""%string (vnames w)) = shn a.
Proof.
move=> Hn F; have win := finds_in F.
have : vertex_has_name a w.
  have : w \in find_vertex (graph_items nodes inputs initialisers) a by rewrite F mem_head.
  by rewrite /find_vertex filterE mem_filter => /andP [].
rewrite vertex_has_nameE.
case: w win {F} => [m|t|i|o] win /=.
- move=> ain; have mn : m \in nodes by rewrite -(mem_graph_items_node _ inputs initialisers).
  have [S /andP [ne /allP HS]] := node_shape_ok_outs _ _ (allP Hn m mn).
  rewrite (eqP (HS a ain)); case: (node_outputs m) ne HS => [|o os] //= _ HS.
  by rewrite (eqP (HS o (mem_head _ _))).
- by case: (tensor_name t) => [s|] //=; rewrite inE => /eqP ->.
- by case: (value_name i) => [s|] //=; rewrite inE => /eqP ->.
- by case: (value_name o) => [s|] //=; rewrite inE => /eqP ->.
Qed.

Lemma all_rem_rev {T : eqType} (p : pred T) (n : T) (s : seq T) :
  all p s -> all p (rev (rem n (rev s))).
Proof.
by move=> H; rewrite all_rev; apply: (subset_all (@mem_rem _ n (rev s))); rewrite all_rev.
Qed.

(** In a graph whose names are checked locally, every successful evaluation
    of a vertex returns correct dims of the vertex's static shape. *)
Lemma eval_graph_dims d xs nodes inputs initialisers shn v t :
  all tensorProtoSized xs -> all (fun u => dims_correct (get_dims u)) xs ->
  all tensorProtoSized initialisers -> all (fun u => dims_correct (get_dims u)) initialisers ->
  all (fun u => if tensor_name u is Some s then shn s == mat_dims (get_dims u) else false)
      initialisers ->
  (forall i, i \in inputs -> forall nm u, value_name i = Some nm -> u \in xs ->
     tensor_has_name nm u -> shn nm = mat_dims (get_dims u)) ->
  all (node_shape_ok shn) nodes ->
  v \in graph_items nodes inputs initialisers ->
  onnx_evaluator_recursive d xs (graph_items nodes inputs initialisers) v = Success t ->
  dims_correct (get_dims t) /\ mat_dims (get_dims t) = shn (seq.head ""%string (vnames v)).
Proof.
move=> Sx Cx Si Ci Ii In Nn vin E.
have Ti (P : TensorProto -> Prop) : (forall u, u \in initialisers -> P u) ->
    forall u, tensor u \in graph_items nodes inputs initialisers -> P u.
  by move=> HP u; rewrite mem_graph_items_tensor; exact: HP.
have Tv (P : TensorProto -> Prop) : (forall u, u \in initialisers -> P u) ->
    forall u, tensor u \in v :: graph_items nodes inputs initialisers -> P u.
  move=> HP u; rewrite in_cons => /orP [/eqP uv|]; last exact: Ti.
  by apply: (Ti _ HP); rewrite uv.
have Nm m : node m \in graph_items nodes inputs initialisers -> node_shape_ok shn m.
  by rewrite mem_graph_items_node => /(allP Nn).
split.
  exact: eval_dims_correct Sx Cx (Tv _ (fun u h => allP Si u h)) (Tv _ (fun u h => allP Ci u h)) E.
apply: (eval_static_dims _ _ _ _ (fun w => shn (seq.head ""%string (vnames w))) _ _ (fun _ h => h) vin Sx Cx
          (Ti _ (fun u h => allP Si u h)) (Ti _ (fun u h => allP Ci u h)) _ _ _ _ _ E).
- move=> u /(Ti _ (fun u h => allP Ii u h)); rewrite /vnames.
  by case: (tensor_name u) => [s|] //= /eqP.
- move=> i nm u ii E1 ux hn; rewrite /vnames E1 /=.
  by apply: (In _ _ nm u E1 ux hn); rewrite -(mem_graph_items_input nodes _ initialisers).
- by move=> o nm w; rewrite output_notin_graph_items.
- move=> outs nm dom ov attrs doc meta x a w /= nin F.
  by rewrite (graph_sh_find _ _ _ _ _ _ Nn F) (node_shape_relu _ _ _ _ _ _ _ _ _ _ (Nm _ nin)).
- move=> ins outs nm dom ov attrs doc meta x a b c wa wb; cbv zeta => nin Hins Fa Fb.
  rewrite (graph_sh_find _ _ _ _ _ _ Nn Fa) (graph_sh_find _ _ _ _ _ _ Nn Fb).
  have : node_shape_ok shn (NodeProto_constructor ins outs nm (Some """Gemm""") dom ov attrs doc meta x).
    exact: Nm.
  case: Hins => -> /node_shape_gemm;
  by case: (get_gemm_attributes attrs) => [[[? ?] ?] ?] /andP [_ /eqP <-].
Qed.

(** The syntactic part of well-formedness: facts about the ONNX graph
    itself, independent of how it is evaluated. *)
Definition model_syntax_ok (m : ModelProto) : bool :=
  if m is ModelProto_constructor _ _ _ _ _ _ _ (Some graph) _ _ _ _ then
  let : GraphProto_constructor nodes _ initialisers _ _ inputs outputs _ _ _ := graph in
  let items := ([seq node x0 | x0 <- List.rev nodes] ++ [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers])%SEQ in
  let dt := if outputs is o :: _ then value_tensor_type o else None in
  [&& (** names are unique and every node input is defined before it is used **)
      graph_acyclic nodes inputs initialisers, (** The graph structure is acyclic **)
      (** every output names exactly one vertex, and that vertex is a node **)
      all (fun x => if value_name x is Some s then
                      if find_vertex items s is [:: node _] then true else false
                    else false) outputs,
      (** inputs and outputs are named, declare their dims, and share one dtype dt **)
      all (fun v => [&& value_tensor_type v != None, value_tensor_type v == dt,
                        value_name v != None & value_dims v != None]) (inputs ++ outputs) &
      (** initialisers are named, have dtype dt, and their data fills their dims **)
      all (fun t => [&& tensor_dtype t == dt, tensorProtoSized t & tensor_name t != None])
          initialisers]
  else false.

(** The part of well-formedness specific to our evaluator: only Gemm and Relu,
    every value is a matrix (rank <= 2), and the static matrix shapes check. *)
Definition model_eval_ok (m : ModelProto) : bool :=
  if m is ModelProto_constructor _ _ _ _ _ _ _ (Some graph) _ _ _ _ then
  let : GraphProto_constructor nodes _ initialisers _ _ inputs outputs value_info _ _ := graph in
  let shn := name_shape initialisers (inputs ++ outputs ++ value_info)%SEQ in
  let mat_shape s ds := dims_correct ds && (shn s == mat_dims ds) in
  [&& all (predI valid_op (predI (node_shape_ok shn) (gemm_int_attrs_ok \o get_attributes))) nodes,
      all (fun v => if (value_name v, value_dims v) is (Some s, Some ds) then mat_shape s ds
                    else false) (inputs ++ outputs) &
      all (fun t => if tensor_name t is Some s then mat_shape s (get_dims t) else false)
          initialisers]
  else false.

Definition model_well_formed (m : ModelProto) : bool :=
  model_syntax_ok m && model_eval_ok m.

Lemma well_formed_computes (m : ModelProto) (xs : seq TensorProto)
  : all tensorProtoSized xs ->
    all (fun o => all (fun u => tensor_dtype u == value_tensor_type o) xs) (graph_outputs m) ->
    all (fun u => dims_correct (get_dims u)) xs ->
    all (fun i => if value_name i is Some nm then
                    all (fun u => tensor_has_name nm u ==>
                                  (omap mat_dims (value_dims i) == Some (mat_dims (get_dims u)))) xs
                  else true) (graph_inputs m) ->
    (** every graph input is named and given exactly one user tensor **)
    all (fun i => if value_name i is Some nm then
                    size (filter (tensor_has_name nm) xs) == 1%nat
                  else false) (graph_inputs m) ->
    model_well_formed m -> isSuccess (onnx_evaluator m xs).
Proof.
move=> inputs_sized inputs_dt xs_dc xs_sh in_one H.
rewrite /onnx_evaluator.
case: m inputs_dt xs_sh in_one H => ir opset prod_name prod_vers domain model_version doc [[nodes name initialisers sparse_initialisers doc_string inputs outputs value_info quantisation metadata_props]|//] metadata training functions config inputs_dt xs_sh in_one well_formed /=.
rewrite isSuccess_map.
rewrite all_map.
apply/allP => /= x xin.
rewrite length_size !listmap_map !app_cat.
move H: ([seq node x0 | x0 <- List.rev nodes] ++
           [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers])%SEQ => items.
move H': (size items) => k.
(* case: k H' => [|k ksize] /=. *)
(* move: well_formed => /andP [H' _]. (* size0. *) *)
(* move: H'. *)
(* by rewrite H size0. *)
(* case: x {xin}. *)
(* case=>[x_name|]; last first. *)
(* admit. (** output has name **) *)
(* move=> x_type x_doc x_meta. *)
(* suff: exists y, List.filter (vertex_has_name x_name) items = [:: y] /\ y \in items; last admit. (** Output name is unique **) *)
(* move=> [y [-> yin]]. *)
(* elim: k ksize y yin nodes inputs initialisers well_formed H => [| k IHk] ksize y yin nodes inputs initialisers well_formed H. *)
(* move: well_formed => /andP []. *)
(* by rewrite H ksize. *)
(* case: y yin IHk => /=. *)

move: xin.
rewrite listmap_map.
case: x => x /mapP [// x0 xin [xis]].
move: xin.
rewrite -xis => xin.
move/andP: well_formed => [/and4P [w3 /allP /(_ x xin) + decl init_ok]].
move=> + /and3P [w_nodes v_sh i_sh].
move: w_nodes; rewrite all_predI => /andP [w2].
rewrite all_predI => /andP [nodes_sh w5].
have w4 : all tensorProtoSized initialisers.
  by apply/allP => t /(allP init_ok) /and3P [].
have init_dc : all (fun u => dims_correct (get_dims u)) initialisers.
  by apply/allP => t /(allP i_sh); case: (tensor_name t) => // ? /andP [].
have init_sh : all (fun u => if tensor_name u is Some s then
                               name_shape initialisers (inputs ++ outputs ++ value_info)%SEQ s
                               == mat_dims (get_dims u) else false) initialisers.
  by apply/allP => t /(allP i_sh); case: (tensor_name t) => // ? /andP [].
have := allP decl x; rewrite mem_cat xin orbT => /(_ isT) /and4P [xdt_ne /eqP xdt _ _].
have init_dt : all (fun t => tensor_dtype t == value_tensor_type x) initialisers.
  by rewrite xdt; apply/allP => t /(allP init_ok) /and3P [].
move/allP/(_ x xin): inputs_dt => xs_dt.
case: (value_tensor_type x) xdt_ne init_dt xs_dt => [dt|//] _ init_dt xs_dt.
move: (name_shape _ _) nodes_sh init_sh v_sh => shn nodes_sh init_sh v_sh.
have in_sh : forall i, i \in inputs -> forall nm u, value_name i = Some nm -> u \in xs ->
    tensor_has_name nm u -> shn nm = mat_dims (get_dims u).
  move=> i iin nm u E ux hn; move: (allP v_sh i) (allP xs_sh i iin).
  rewrite mem_cat iin E => /(_ isT); case: (value_dims i) => // ds /andP [_ /eqP e].
  by move=> /allP /(_ u ux); rewrite hn /= -e => /eqP [].
move=> {v_sh xs_sh i_sh decl init_ok xdt}.
have {in_one} in_one : all (fun i => if value_name i is Some nm then
    size (filter (tensor_has_name nm) xs) == 1%nat else false) inputs := in_one.
rewrite /value_name.
case: x x0 xis xin => [[xname|//]] xtype xstring xmeta /[dup] /= x' x'' -> xin'.
case E: (find_vertex _ xname) => [|x [|? ?]] //; last by case: x E.
move=> _; move: E => /[dup] /finds_in.
rewrite H => xin.
rewrite /find_vertex => ->.
move=> {x' x'' xin' xname xtype xstring xmeta ir opset prod_name prod_vers domain model_version doc name doc_string value_info quantisation metadata_props metadata training functions config}.
move/graph_acyclic_at:w3.
rewrite /= /graph_items H=> /(_ x xin) w3.
have {w2 w3 w4 w5} well_formed := (And4 w2 w3 w4 w5).
elim: k x items xin H' nodes inputs initialisers H well_formed init_dt init_dc init_sh in_sh nodes_sh in_one => //= [|k IHk] x items xin H' nodes inputs initialisers H well_formed init_dt init_dc init_sh in_sh nodes_sh in_one.
(* elim: k x items H' nodes inputs initialisers H well_formed => //= [|k IHk] x items H' nodes inputs initialisers H well_formed. *)
  by move/eqP: H'; rewrite size_eq0 => /eqP E; rewrite E in xin.
(* rewrite !size_cat H' => ->. *)
(* rewrite !size_cat. !addn_eq0 !size_map. => /and3P [_ /eqP -> _]. *)
case: x xin well_formed IHk => [n|t|v|v] /= xin well_formed IHk.
- (** node **)
  have ninnodes : n \in nodes.
    by move: xin; rewrite -H -/(graph_items _ _ _) mem_graph_items_node.
  case: (well_formed) => vo ac Si go.
  have vop := allP vo n ninnodes; have gi := allP go n ninnodes.
  (** evaluating an input of [n] succeeds in the whole graph **)
  have child i w : i \in node_inputs n -> find_vertex items i = [:: w] ->
      isSuccess (onnx_evaluator_recursive k xs items w).
    move=> iin F; apply: (onnx_evaluator_rec_S _ _ _ n _ ac).
    have wn : w != node n.
      by have [w' F' wn] := acyclic_at_find ac iin; move: F' wn; rewrite F => -[->].
    have H'' : graph_items (rev (rem n (rev nodes))) inputs initialisers =
               rem (node n) items.
      by rewrite /graph_items rev_is_rev revK -H rem_cat.
    apply: (IHk w _ _ _ _ inputs initialisers H'' _ init_dt init_dc init_sh in_sh
              (all_rem_rev _ _ _ nodes_sh) in_one).
    - exact: rem_mem (finds_in F).
    - by rewrite size_rem // H'.
    - case: well_formed => vo' _ si go'; split => //; first exact: all_rem_rev.
        exact: (acyclic_at_child _ _ _ _ ac iin F).
      exact: all_rem_rev.
  (** the evaluated inputs are sized, have dtype [dt] and their static shape **)
  have Ti (P : TensorProto -> Prop) : (forall u, u \in initialisers -> P u) ->
      forall w, w \in items -> forall u, tensor u \in w :: items -> P u.
    move=> HP w win u; rewrite in_cons => /orP [/eqP uw|ui]; apply: HP.
      by move: win; rewrite -uw -H -/(graph_items _ _ _) mem_graph_items_tensor.
    by move: ui; rewrite -H -/(graph_items _ _ _) mem_graph_items_tensor.
  have Sv w t : w \in items -> onnx_evaluator_recursive k xs items w = Success t ->
      tensorProtoSized t.
    move=> win; apply: (eval_sized _ _ _ _ _ inputs_sized).
    by apply: (Ti _ _ w win) => u; apply: (allP Si).
  have Dv w t : w \in items -> onnx_evaluator_recursive k xs items w = Success t ->
      tensor_dtype t = Some dt.
    move=> win; apply: (eval_dtype _ _ _ _ _ _ xs_dt).
    by apply: (Ti _ _ w win) => u /(allP init_dt) /eqP.
  have Gd i w t : find_vertex items i = [:: w] ->
      onnx_evaluator_recursive k xs items w = Success t ->
      dims_correct (get_dims t) /\ mat_dims (get_dims t) = shn i.
    move: (Si) => Si'; rewrite -H => F E.
    have [c m] := eval_graph_dims _ _ _ _ _ _ _ _ inputs_sized xs_dc Si' init_dc init_sh
                    in_sh nodes_sh (finds_in F) E.
    by rewrite (graph_sh_find _ _ _ _ _ _ nodes_sh F) in m.
  have Nn := allP nodes_sh n ninnodes.
  case: (valid_opP ac vop) => /=.
  + (** Gemm 2 inputs **)
    move=> a b va vb outs nm dom ov attrs doc meta x' nis Fa Fb _.
    have ina : a \in node_inputs n by rewrite nis /= inE eqxx.
    have inb : b \in node_inputs n by rewrite nis /= !inE eqxx orbT.
    rewrite nis /= Fa Fb.
    case/isSuccessP: (child a va ina Fa) => t0 E0.
    case/isSuccessP: (child b vb inb Fb) => t1 E1.
    rewrite E0 E1.
    have [c0 m0] := Gd _ _ _ Fa E0; have [c1 m1] := Gd _ _ _ Fb E1.
    move: Nn; rewrite nis => /node_shape_gemm Nn.
    apply: gemm_two_success.
    - by rewrite /= (Dv _ _ (finds_in Fa) E0) (Dv _ _ (finds_in Fb) E1) eqxx.
    - exact: Sv (finds_in Fa) E0.
    - exact: Sv (finds_in Fb) E1.
    - apply: (static_gemm_dims_ok _ _ _ _ _ c0 c1 m0 m1).
      by move: Nn; case: (get_gemm_attributes _) => [[[? ?] ?] ?] /andP [].
    - by move=> _; move: gi; rewrite nis.
  + (** Gemm 3 inputs **)
    move=> a b c va vb vc outs nm dom ov attrs doc meta x' nis Fa Fb Fc _.
    have ina : a \in node_inputs n by rewrite nis /= inE eqxx.
    have inb : b \in node_inputs n by rewrite nis /= !inE eqxx orbT.
    have inc : c \in node_inputs n by rewrite nis /= !inE eqxx !orbT.
    rewrite nis /= Fa Fb Fc.
    case/isSuccessP: (child a va ina Fa) => t0 E0.
    case/isSuccessP: (child b vb inb Fb) => t1 E1.
    case/isSuccessP: (child c vc inc Fc) => t2 E2.
    rewrite E0 E1 E2.
    have [c0 m0] := Gd _ _ _ Fa E0; have [c1 m1] := Gd _ _ _ Fb E1.
    have [c2 m2] := Gd _ _ _ Fc E2.
    move: Nn; rewrite nis => Nn.
    have G : gemm_dims_ok (get_dims t0) (get_dims t1) attrs.
      apply: (static_gemm_dims_ok _ _ _ _ _ c0 c1 m0 m1).
      by move/node_shape_gemm: Nn; case: (get_gemm_attributes _) => [[[? ?] ?] ?] /andP [].
    apply: gemm_three_success.
    - rewrite /= (Dv _ _ (finds_in Fa) E0) (Dv _ _ (finds_in Fb) E1).
      by rewrite (Dv _ _ (finds_in Fc) E2) !eqxx.
    - exact: Sv (finds_in Fa) E0.
    - exact: Sv (finds_in Fb) E1.
    - exact: Sv (finds_in Fc) E2.
    - rewrite /gemm3_dims_ok G c2 m0 m1 m2.
      move/node_shape_gemm3: Nn.
      by case: (get_gemm_attributes _) => [[[? ?] ?] ?] /=; case: (shn c).
    - by move=> _; move: gi; rewrite nis.
  + (** Relu **)
    move=> a va outs nm dom ov attrs doc meta x' nis Fa _.
    have ina : a \in node_inputs n by rewrite nis /= inE eqxx.
    rewrite nis /= Fa.
    case/isSuccessP: (child a va ina Fa) => t0 E0.
    by rewrite E0; apply/relu_success/(Sv _ _ (finds_in Fa) E0).
- by []. (** tensor **)
- (** input **)
  move=> {well_formed IHk}.
  have iin : v \in inputs.
    by move: xin; rewrite -H -/(graph_items _ _ _) mem_graph_items_input.
  move: (allP in_one v iin); case: v {xin iin} => [[nm|] ? ? ?] //= one.
  rewrite filterE; move: one.
  by case: (filter (tensor_has_name nm) xs) => [|u [|? ?]].
- (** output **)
  by move: xin; rewrite -H -/(graph_items _ _ _) output_notin_graph_items.
Qed.

Definition well_formed_model (d : NetworkType Elem) : eqType :=
  { m : ModelProto | network_dim_match m d && model_well_formed m}.

(* Definition nodeOutput (y : NetworkType Elem) (m' : well_formed_model y) (s : string) *)
(* (d : TensorType Elem) : eqType := *)
(* match m' with *)
(* | exist m _ => *)
(*     { v : ValueInfoProto | *)
(*       [&& v \in graph_outputs m, value_info_name v == s & value_has_type d v]} *)
(* end. *)

(* Definition denote (x : Elem) : eqType := *)
(*   match x with *)
(*   | exist x Px => *)
(*       match x as x0 return (x0 \in supported_types) -> eqType with *)
(*       | FLOAT_TensorProto => fun=> float32 *)
(*       | INT32_TensorProto => fun=> int32 *)
(*       | INT64_TensorProto => fun=> int64 *)
(*       | STRING_TensorProto => fun=> string *)
(*       | DOUBLE_TensorProto => fun=> float64 *)
(*       | UINT64_TensorProto => fun=> uint64 *)
(*       | _ => fun Px => False_rect eqType (notF Px) *)
(*       end Px *)
(* end. *)

(* Definition theoryTensorProto : forall t : TensorType Elem, sized_tensor t -> TensorSemantics denote t. *)
(* Proof. *)
(* rewrite /sized_tensor. *)
(* rewrite /=. *)
(* case. *)
(* case => /= [x H] [k dims] [t /= /andP [/andP [Ht hasType] sized]]. *)
(* case: t Ht hasType sized => /= t Ht Ht'. *)
(* rewrite /Tensor_has_type /tensorProtoSized. *)
(* move: Ht'. *)
(* case t. *)
(* move=> /= t_dims. *)
(* case=> //. *)
(* move=> /(DataType_TensorProto_of_int32). *)
(* case=> //= data_type segment float int32 string int64 name doc_string raw_data *)
(*            external_data data_location double_data uint64_data metadata_props /eqP. *)
(* case: x H => // _ dims_eq /eqP <- /andP [dims_pos /eqP data_sized]. *)
(* - apply: Tensor. rewrite big_ord0. *)
(*   apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple float) (cast_ord _ i)). *)
(*   move=> _ _. *)
(*   rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord. *)
(*   move: (f_equal size dims_eq). *)
(*   rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->. *)
(*   apply/eq_bigr => i _. *)
(*   have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=. *)
(*   rewrite (nth_map default_zero); first by rewrite Hk ltn_ord. *)
(*   rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord. *)
(*   rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord. *)
(*   by rewrite nth_ord_enum => ->. *)
(* - apply: Tensor; rewrite big_ord0. *)
(*   apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int32) (cast_ord _ i)). *)
(*   move=> _ _. *)
(*   rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord. *)
(*   move: (f_equal size dims_eq). *)
(*   rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->. *)
(*   apply/eq_bigr => i _. *)
(*   have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=. *)
(*   rewrite (nth_map default_zero); first by rewrite Hk ltn_ord. *)
(*   rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord. *)
(*   rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord. *)
(*   by rewrite nth_ord_enum => ->. *)
(* - apply: Tensor; rewrite big_ord0. *)
(*   apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int64) (cast_ord _ i)). *)
(*   move=> _ _. *)
(*   rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord. *)
(*   move: (f_equal size dims_eq). *)
(*   rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->. *)
(*   apply/eq_bigr => i _. *)
(*   have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=. *)
(*   rewrite (nth_map default_zero); first by rewrite Hk ltn_ord. *)
(*   rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord. *)
(*   rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord. *)
(*   by rewrite nth_ord_enum => ->. *)
(* Defined. *)

(* (* *)
(* Executes the network by exploring the ModelProto exactly as *)
(* ONNXEvaluator.onnx_evaluator does: build the same list of vertices, *)
(* evaluate the output vertex, and recurse through node inputs found with *)
(* find_vertex. Every failure branch of onnx_evaluator is ruled out by *)
(* model_well_formed (the fuel by acyclic_at, as in well_formed_computes). *)
(* - Node:   Gemm (2 or 3 inputs) and Relu inputs are evaluated recursively, *)
(*           then gemm_2_inputs, gemm_3_inputs or op_relu is applied. *)
(* - Tensor: the initialiser is turned into a mathcomp tensor with *)
(*           theoryTensorProto. *)
(* - Input:  the semantic inputs are positional, so the input at the same *)
(*           position in the graph inputs is returned. *)
(* Intermediate vertices evaluate to a tensor of some type d'. *)
(* *) *)

(* Definition gemm_2_inputs {R} {m n p} (zero : R) (mul : R -> R -> R) (add : R -> R -> R) *)
(* (a : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) : 'M[R]_(m, p) := *)
(*   \matrix[mulmx_key]_(i, k) \big[add/zero]_j (mul a (mul (m1 i j) (m2 j k))). *)

(* Definition gemm_3_inputs {R} {m n p} (zero : R) (mul : R -> R -> R) (add : R -> R -> R) *)
(* (a b : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) (m3 : 'M[R]_(m, p)) : 'M[R]_(m, p) := *)
(*   (map2_mx (fun x y => add x (mul b y)) (\matrix[mulmx_key]_(i, k) \big[add/zero]_j (mul a (mul (m1 i j) (m2 j k)))) m3). *)

(* Definition op_relu {R} {m n} (zero : R) (lt : R -> R -> bool) *)
(*                    (m1 : 'M[R]_(m, n)) : 'M[R]_(m, n) := *)
(*   map_mx (fun x => if lt x zero then zero else x) m1. *)

(* (** The rank-2 type of a static shape (h, w); [insubd] keeps it total, and on *)
(*     well-formed shapes it is the identity *) *)
(* Definition mat_type (e : Elem) (hw : nat * nat) : TensorType Elem := *)
(*   @tensorType Elem e (existT _ 2%nat [ffun i : 'I_2 => *)
(*     insubd 1%:posnat *)
(*            (if i == ord0 then hw.1 else hw.2)]). *)

(* (** Reshape a tensor to any shape with the same number of entries **) *)
(* Definition reshape {R : Type} {k k'} {ds : {posnum nat} ^ k} {ds' : {posnum nat} ^ k'} *)
(*   (E : (\prod_(i < k) (ds i)%:num = \prod_(i < k') (ds' i)%:num)%nat) *)
(*   (t : 'nT[R]_(ds)) : 'nT[R]_(ds') := *)
(*   @Tensor _ _ ds' [tuple] R (castmx (E, erefl) (tensor_val t)). *)

(* Definition modelTensorProto (y : NetworkType Elem) *)
(* (n : well_formed_model y) (inp : InputSemantics denote y) *)
(* (d : TensorType Elem) (u : string) *)
(* (out : nodeOutput y n u d) : TensorSemantics denote d. *)
(* Proof. *)
(* case: y n inp out => [[inps inps_gt0] [outs outs_gt0]] [m /andP [dm wf]] /= inp. *)
(* case=> o /and3P [oin /eqP oname otype]. *)
(* case: m dm wf oin => ir opset prod_name prod_vers domain model_version doc *)
(*   [[nodes name initialisers sparse_initialisers doc_string inputs outputs value_info *)
(*     quantisation metadata_props]|//] metadata training functions config dm wf oin /=. *)
(* move: dm wf oin => /= dm wf oin. *)
(* (** [vertices] of onnx_evaluator **) *)
(* move Hv: (graph_items nodes inputs initialisers) => vertices. *)
(* move/andP: wf => [/and4P [acyc /allP outs_one /allP decl /allP init_ok]]. *)
(* move=> /and3P [/allP nodes_ok /allP v_sh /allP i_sh]. *)
(* have vop n : node n \in vertices -> valid_op n. *)
(*   by rewrite -Hv mem_graph_items_node => /nodes_ok /andP []. *)
(* have sized t : tensor t \in vertices -> tensorProtoSized t. *)
(*   by rewrite -Hv mem_graph_items_tensor => /init_ok /and3P []. *)
(* have named i : input i \in vertices -> value_name i != None. *)
(*   rewrite -Hv mem_graph_items_input => iin. *)
(*   by move: (decl i); rewrite mem_cat iin => /(_ isT) /and4P []. *)
(* have in_inputs i : input i \in vertices -> i \in inputs. *)
(*   by rewrite -Hv mem_graph_items_input. *)
(* have no_output v : output v \in vertices = false. *)
(*   by rewrite -Hv output_notin_graph_items. *)
(* have Hsz : size inps = size inputs. *)
(*   by move/and4P: dm => [_ _ + _]; rewrite all2E => /andP [/eqP]. *)
(* (** every vertex has the matrix type of its static shape, in the dtype of d **) *)
(* pose shn := name_shape initialisers (inputs ++ outputs ++ value_info)%SEQ. *)
(* pose ty (w : vertex) := mat_type (tensorTypes _ d) (shn (seq.head ""%string (vnames w))). *)
(* have nodes_sh : all (node_shape_ok shn) nodes. *)
(*   by apply/allP => m /nodes_ok /andP [_ /andP []]. *)
(* (** the graph dtype is the dtype of d **) *)
(* have dtE : (if outputs is o' :: _ then value_tensor_type o' else None) = *)
(*            Some (tag (tensorTypes _ d)). *)
(*   move: (decl o); rewrite mem_cat oin orbT => /(_ isT) /and4P [_ /eqP <- _ _]. *)
(*   by case/andP: otype => /eqP. *)
(* have elemE (x : Elem) : Some (tag x) = Some (tag (tensorTypes _ d)) -> x = tensorTypes _ d. *)
(*   by move=> [] /val_inj. *)
(* (** reshaping a declared shape l of the name s into the matrix type of s **) *)
(* have mat_prod hw : (0 < hw.1)%nat -> (0 < hw.2)%nat -> *)
(*   (\prod_(i < 2) ([ffun i : 'I_2 => insubd 1%:posnat (if i == ord0 then hw.1 else hw.2)] i *)
(*      : {posnum nat})%:num = hw.1 * hw.2)%nat. *)
(*   case: hw => [h w] /= h0 w0; rewrite big_ord_recr big_ord1 /= !ffunE /= !insubdK //; *)
(*     by rewrite -topredE /= /Itv.spec /= /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat. *)
(* have dims_prodE k (ds : {posnum nat} ^ k) (l : seq int64) : *)
(*   map (fun q : {posnum nat} => q%:num) (tval ds) = map int64_to_dim l -> *)
(*   dims_correct l -> (\prod_(i < k) (ds i)%:num = (mat_dims l).1 * (mat_dims l).2)%nat. *)
(*   move=> E dc; rewrite -mat_dims_prod // /dims_prod -(big_map int64_to_dim xpredT id) -E big_map. *)
(*   by rewrite big_tuple; apply: eq_bigr => i _; rewrite /tuple_of_finfun tnth_mktuple. *)
(* have to_mat (e : Elem) s k (ds : {posnum nat} ^ k) (l : seq int64) : *)
(*   map (fun q : {posnum nat} => q%:num) (tval ds) = map int64_to_dim l -> *)
(*   dims_correct l -> shn s = mat_dims l -> *)
(*   'nT[denote e]_(ds) -> TensorSemantics denote (mat_type e (shn s)). *)
(*   move=> E dc sh t /=; apply: (reshape _ t). *)
(*   have /andP [h0 w0] := mat_dims_pos _ dc. *)
(*   by rewrite (dims_prodE _ _ _ E dc) sh mat_prod. *)
(* (** every vertex found under a name has that name's static shape **) *)
(* have sh_find its i w : {subset its <= vertices} -> find_vertex its i = [:: w] -> *)
(*     shn (seq.head ""%string (vnames w)) = shn i. *)
(*   move=> sub F; have win : w \in vertices by apply: sub; exact: finds_in F. *)
(*   have : vertex_has_name i w. *)
(*     have : w \in find_vertex its i by rewrite F mem_head. *)
(*     by rewrite /find_vertex filterE mem_filter => /andP []. *)
(*   rewrite vertex_has_nameE; move: win; rewrite -Hv. *)
(*   case: w {F} => [m|t|i'|o'] win /=. *)
(*   - move=> iin; have mn : m \in nodes by rewrite -(mem_graph_items_node _ inputs initialisers). *)
(*     have [S /andP [ne /allP HS]] := node_shape_ok_outs _ _ (allP nodes_sh m mn). *)
(*     rewrite (eqP (HS i iin)); case: (node_outputs m) ne HS => [|o1 os] //= _ HS. *)
(*     by rewrite (eqP (HS o1 (mem_head _ _))). *)
(*   - by case: (tensor_name t) => [s|] //=; rewrite inE => /eqP ->. *)
(*   - by case: (value_name i') => [s|] //=; rewrite inE => /eqP ->. *)
(*   - by case: (value_name o') => [s|] //=; rewrite inE => /eqP ->. *)
(* (** a value of matrix type (h, w) as a mathcomp matrix, and back **) *)
(* pose dimc (x : nat) : nat := ltac:(exact ((insubd 1%:posnat x : {posnum nat})%:num)). *)
(* have prod2 hw : (\prod_(i < 2) ([ffun i : 'I_2 => insubd 1%:posnat (if i == ord0 then hw.1 else hw.2)] i *)
(*                   : {posnum nat})%:num = dimc hw.1 * dimc hw.2)%nat. *)
(*   by rewrite big_ord_recr big_ord1 /= !ffunE. *)
(* have prod0 (f : {posnum nat} ^ 0) : (\prod_(j < 0) (f j)%:num = 1)%nat by rewrite big_ord0. *)
(* pose to_m hw (t : TensorSemantics denote (mat_type (tensorTypes _ d) hw)) *)
(*   : 'M[denote (tensorTypes _ d)]_(dimc hw.1, dimc hw.2) := *)
(*   vec_mx (castmx (prod0 _, prod2 hw) (tensor_val t)^T). *)
(* pose of_m hw (M : 'M[denote (tensorTypes _ d)]_(dimc hw.1, dimc hw.2)) *)
(*   : TensorSemantics denote (mat_type (tensorTypes _ d) hw) := *)
(*   @Tensor _ _ _ _ _ (castmx (esym (prod2 hw), esym (prod0 _)) (mxvec M)^T). *)
(* (** zero, mul and add of the dtype of d, and alpha converted to it, as in op_gemm **) *)
(* pose gemm_ops (alpha : float32) : denote (tensorTypes _ d) * *)
(*     (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> denote (tensorTypes _ d)) * *)
(*     (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> denote (tensorTypes _ d)) * *)
(*     denote (tensorTypes _ d) := *)
(*   ltac:(case: (tensorTypes _ d) => [[] xin]; *)
(*         first [ exact (Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE 0 0 false, *)
(*                        b32_mult BinarySingleNaN.mode_NE, b32_plus BinarySingleNaN.mode_NE, alpha) *)
(*               | exact (int32_of_Z 0, fun x y => int32_of_Z (Z_of_int32 x * Z_of_int32 y)%Z, *)
(*                        fun x y => int32_of_Z (Z_of_int32 x + Z_of_int32 y)%Z, *)
(*                        int32_of_Z (odflt 0%Z (Z_of_float32 alpha))) *)
(*               | exact (int64_of_Z 0, fun x y => int64_of_Z (Z_of_int64 x * Z_of_int64 y)%Z, *)
(*                        fun x y => int64_of_Z (Z_of_int64 x + Z_of_int64 y)%Z, *)
(*                        int64_of_Z (odflt 0%Z (Z_of_float32 alpha))) *)
(*               | by exfalso; move: xin; rewrite !inE => /or3P [] /eqP ]). *)
(* (** the value relu sends negatives to, and the comparison it uses, as in op_relu **) *)
(* pose relu_ops : denote (tensorTypes _ d) * *)
(*     (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> bool) := *)
(*   ltac:(case: (tensorTypes _ d) => [[] xin]; *)
(*         first [ exact (Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE 0 0 true, *)
(*                        fun x y : float32 => if x is Binary.B754_finite true _ _ _ then (if Binary.Bcompare 24 128 x y is Some Lt then true else false) else false) *)
(*               | exact (int32_of_Z 0, fun x y => (Z_of_int32 x <? Z_of_int32 y)%Z) *)
(*               | exact (int64_of_Z 0, fun x y => (Z_of_int64 x <? Z_of_int64 y)%Z) *)
(*               | by exfalso; move: xin; rewrite !inE => /or3P [] /eqP ]). *)
(* (** broadcasting index: k if it is in range, otherwise 0 **) *)
(* have dimc_gt0 x : (0 < dimc x)%nat. *)
(*   by rewrite /dimc; case: (insubd _ _) => v /=; rewrite /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat. *)
(* pose bidx x (k : nat) : 'I_(dimc x) := insubd (Ordinal (dimc_gt0 x)) k. *)
(* (** onnx_evaluator_recursive **) *)
(* have go : forall (depth : nat) (its : seq vertex) (w : vertex), *)
(*     size its = depth -> w \in its -> {subset its <= vertices} -> acyclic_at its w -> *)
(*     TensorSemantics denote (ty w). *)
(*   elim=> [|depth IH] its w Hd win sub ac. *)
(*     by move/size0nil: Hd win => ->. *)
(*   case: w win ac => [n|t|v|v] win ac. *)
(*   - (** Node: check op_type and compute it if possible **) *)
(*     have child i w : i \in node_inputs n -> find_vertex its i = [:: w] -> *)
(*         TensorSemantics denote (ty w). *)
(*       move=> iin F. *)
(*       have wn : w != node n. *)
(*         by have [w' F' wn] := acyclic_at_find ac iin; move: F' wn; rewrite F => -[->]. *)
(*       apply: (IH (rem (node n) its) w). *)
(*       + by rewrite size_rem // Hd. *)
(*       + exact: rem_mem (finds_in F). *)
(*       + by move=> z /mem_rem /sub. *)
(*       + exact: acyclic_at_child ac iin F. *)
(*     have found i : i \in node_inputs n -> *)
(*         exists2 w, find_vertex its i = [:: w] & w != node n := acyclic_at_find ac. *)
(*     have := vop n (sub _ win). *)
(*     case: n win ac child found => ins n_outs n_name [s|] n_dom n_ov attrs n_doc n_meta n_x *)
(*                                   win ac child found //=. *)
(*     case: ifP => sG. *)
(*     + (** Gemm **) *)
(*       case: ins win ac child found => [|a [|b [|c [|? ?]]]] //= win ac child found _. *)
(*       * (** two inputs **) *)
(*         have ina : a \in [:: a; b] by rewrite inE eqxx. *)
(*         have inb : b \in [:: a; b] by rewrite !inE eqxx orbT. *)
(*         case Fa: (find_vertex its a) => [|va [|? ?]]; *)
(*           try by exfalso; case: (found a ina) => ?; rewrite Fa. *)
(*         case Fb: (find_vertex its b) => [|vb [|? ?]]; *)
(*           try by exfalso; case: (found b inb) => ?; rewrite Fb. *)
(*         (** node_shape_ok: the static shapes of a, b and the output agree **) *)
(*         have Nn : node_shape_ok shn (NodeProto_constructor [:: a; b] n_outs n_name (Some s) *)
(*                                        n_dom n_ov attrs n_doc n_meta n_x). *)
(*           by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*         move: (child a va ina Fa) (child b vb inb Fb). *)
(*         rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb). *)
(*         move: Nn; rewrite /node_shape_ok sG. *)
(*         case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB]. *)
(*         case/and3P => inner /andP [ne /allP outs_sh] _ A B. *)
(*         have hd : seq.head ""%string n_outs \in n_outs. *)
(*           by case: (n_outs) ne => // ? ? _; exact: mem_head. *)
(*         rewrite (eqP (outs_sh _ hd)). *)
(*         apply: (of_m (_, _)). *)
(*         pose ops := gemm_ops alpha. *)
(*         (** transpose A and B as transA, transB say, then A' * B' **) *)
(*         move: inner A B; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB]; *)
(*           move=> /eqP inner A B; *)
(*           first [ exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)) ]. *)
(*       * (** three inputs **) *)
(*         have ina : a \in [:: a; b; c] by rewrite inE eqxx. *)
(*         have inb : b \in [:: a; b; c] by rewrite !inE eqxx orbT. *)
(*         have inc : c \in [:: a; b; c] by rewrite !inE eqxx !orbT. *)
(*         case Fa: (find_vertex its a) => [|va [|? ?]]; *)
(*           try by exfalso; case: (found a ina) => ?; rewrite Fa. *)
(*         case Fb: (find_vertex its b) => [|vb [|? ?]]; *)
(*           try by exfalso; case: (found b inb) => ?; rewrite Fb. *)
(*         case Fc: (find_vertex its c) => [|vc [|? ?]]; *)
(*           try by exfalso; case: (found c inc) => ?; rewrite Fc. *)
(*         have Nn : node_shape_ok shn (NodeProto_constructor [:: a; b; c] n_outs n_name (Some s) *)
(*                                        n_dom n_ov attrs n_doc n_meta n_x). *)
(*           by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*         move: (child a va ina Fa) (child b vb inb Fb) (child c vc inc Fc). *)
(*         rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) (sh_find _ _ _ sub Fc). *)
(*         move: Nn; rewrite /node_shape_ok sG. *)
(*         case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB]. *)
(*         case/and3P => inner /andP [ne /allP outs_sh] _ A B C. *)
(*         have hd : seq.head ""%string n_outs \in n_outs. *)
(*           by case: (n_outs) ne => // ? ? _; exact: mem_head. *)
(*         rewrite (eqP (outs_sh _ hd)). *)
(*         apply: (of_m (_, _)). *)
(*         pose ops := gemm_ops alpha. *)
(*         pose beta' := (gemm_ops beta).2. *)
(*         (** C broadcast to (N, P): a dimension of size 1 always reads index 0 **) *)
(*         move: inner A B C; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB]; *)
(*           move=> /eqP inner A B C; *)
(*           first [ exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)) *)
(*                            (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)) *)
(*                            (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T) *)
(*                            (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T) *)
(*                            (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))) ]. *)
(*     + case: ifP => // sR. *)
(*       (** Relu **) *)
(*       case: ins win ac child found => [|a [|? ?]] //= win ac child found _. *)
(*       have ina : a \in [:: a] by rewrite inE eqxx. *)
(*       case Fa: (find_vertex its a) => [|va [|? ?]]; *)
(*         try by exfalso; case: (found a ina) => ?; rewrite Fa. *)
(*       have Nn : node_shape_ok shn (NodeProto_constructor [:: a] n_outs n_name (Some s) *)
(*                                      n_dom n_ov attrs n_doc n_meta n_x). *)
(*         by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*       move: (child a va ina Fa); rewrite /ty (sh_find _ _ _ sub Fa). *)
(*       move: Nn; rewrite /node_shape_ok sG sR => /andP [ne /allP outs_sh] A. *)
(*       have hd : seq.head ""%string n_outs \in n_outs. *)
(*         by case: (n_outs) ne => // ? ? _; exact: mem_head. *)
(*       rewrite (eqP (outs_sh _ hd)). *)
(*       exact (of_m _ (op_relu relu_ops.1 relu_ops.2 (to_m (shn a) A))). *)
(*   - (** Tensor: just return itself **) *)
(*     have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor. *)
(*     have := sized t (sub _ win). *)
(*     move: (init_ok t tin) (i_sh t tin) => /and3P [/eqP tdt _ _] tsh. *)
(*     case: t win ac tin tdt tsh => dims [dt|] seg fd i32 sd i64 tn ds rd ed dl dd u64 mp *)
(*                                   win ac tin tdt tsh /andP [dpos] //. *)
(*     case E: (DataType_TensorProto_of_int32 dt) => [x|] // Hsize. *)
(*     have xin : x \in supported_types by case: x E Hsize. *)
(*     have pos (i : 'I_(size dims)) : Itv.spec Itv.nat_sem (Itv.Real `]0%R, +oo[) *)
(*                                      (int64_to_dim (tnth (in_tuple dims) i)). *)
(*       have := allP dpos _ (mem_tnth i (in_tuple dims)). *)
(*       by rewrite /Itv.spec /= /Itv.nat_sem in_itv /= andbT. *)
(*     (** [ltac:] so that the positivity of [1%:posnat] is solved, not abstracted **) *)
(*     pose shape : {posnum nat} ^ (size dims) := *)
(*       ltac:(exact [ffun i => insubd 1%:posnat (int64_to_dim (tnth (in_tuple dims) i))]). *)
(*     have shapeE : map (fun q : {posnum nat} => q%:num) (tval shape) = map int64_to_dim dims. *)
(*       have -> : map (fun q : {posnum nat} => q%:num) (tval shape) = *)
(*                 tval (map_tuple (fun q : {posnum nat} => q%:num) shape) by []. *)
(*       have -> : map int64_to_dim dims = tval (map_tuple int64_to_dim (in_tuple dims)) by []. *)
(*       congr tval; apply: eq_from_tnth => i. *)
(*       by rewrite !tnth_map tnth_ord_tuple ffunE insubdK //; exact: pos i. *)
(*     suff T : TensorSemantics denote (@tensorType Elem (exist _ x xin) (existT _ (size dims) shape)). *)
(*       (** reshape T to the matrix type of t **) *)
(*       have xE : exist _ x xin = tensorTypes _ d. *)
(*         by apply: elemE; rewrite -dtE -tdt /= E. *)
(*       move: T; rewrite xE /ty /=. *)
(*       case Etn: tn tsh => [s|] //= /andP [dc /eqP sh] T. *)
(*       exact: (to_mat _ s _ shape dims shapeE dc sh T). *)
(*     apply: theoryTensorProto. *)
(*     exists (qtensor_pi (TensorProto_constructor dims (Some dt) seg fd i32 sd i64 tn *)
(*                                                 ds rd ed dl dd u64 mp)). *)
(*     have Edims : dims = map (tnth (in_tuple dims)) (fintype.enum 'I_(size dims)). *)
(*       by rewrite map_tnth_enum. *)
(*     case: x E Hsize xin => // E Hsize xin; *)
(*       [move: (DataType_float E) | move: (DataType_int32 E) | move: (DataType_int64 E)] => Z; *)
(*       rewrite /= /storage_of Z /= E eqxx Hsize dpos /= !andbT; *)
(*       rewrite -map_comp; apply/eqP; *)
(*       rewrite {1}Edims; *)
(*       by rewrite -map_comp enumT; apply: eq_map => i /=; rewrite ffunE insubdK //; exact: pos i. *)
(*   - (** Input: the user inputs are positional, take the one at v's position **) *)
(*     have vin := in_inputs v (sub _ win). *)
(*     have ilt : (seq.index v inputs < size inps)%nat by rewrite Hsz index_mem. *)
(*     (** network_dim_match: the input at v's position has v's declared type **) *)
(*     have vt_ok : value_has_type (tnth (in_tuple inps) (Ordinal ilt)) v. *)
(*       move/and4P: dm => [_ _ + _]; rewrite all2E => /andP [_ /all_nthP same]. *)
(*       have := same (tnth (in_tuple inps) (Ordinal ilt), v) (seq.index v inputs). *)
(*       rewrite nth_zip_cond size_zip -Hsz minnn ilt => /(_ isT) /=. *)
(*       by rewrite nth_index // -(tnth_nth _ (in_tuple inps) (Ordinal ilt)). *)
(*     move: (inp (Ordinal ilt)) vt_ok. *)
(*     case: (tnth (in_tuple inps) (Ordinal ilt)) => ei [ki dsi] /= X /andP [/eqP vdt /eqP vdims]. *)
(*     have eiE : ei = tensorTypes _ d. *)
(*       apply: elemE; rewrite -vdt -dtE. *)
(*       by move: (decl v); rewrite mem_cat vin => /(_ isT) /and4P [_ /eqP]. *)
(*     (** reshape X to the matrix type of the input **) *)
(*     move: (v_sh v) vdims; rewrite mem_cat vin => /(_ isT). *)
(*     rewrite /ty /= -eiE. *)
(*     case: (value_name v) => [nm|] //=. *)
(*     case: (value_dims v) => [l|] //= /andP [dc /eqP sh] [vdims]. *)
(*     exact: (to_mat _ nm _ dsi l (esym vdims) dc sh X). *)
(*   - (** Output **) *)
(*     by move: (sub _ win); rewrite no_output. *)
(* (** onnx_evaluator: evaluate the output vertex **) *)
(* have := outs_one o oin; rewrite -/(graph_items nodes inputs initialisers) Hv. *)
(* case: o oin oname otype dtE => [[nm|] ot od om] oin oname otype dtE //=. *)
(* (** model_well_formed: the output names exactly one vertex, a node **) *)
(* case F: (find_vertex vertices nm) => [|w [|? ?]] //; last by case: w F. *)
(* case: w F => // n F _. *)
(* have win := finds_in F. *)
(* have ac : acyclic_at vertices (node n). *)
(*   by move: (graph_acyclic_at (node n) acyc); rewrite Hv => /(_ win). *)
(* have Y := go (size vertices) vertices (node n) erefl win (fun _ x => x) ac. *)
(* (** reshape Y to d: the output's declared dims are d's and its static shape **) *)
(* have Fg : find_vertex (graph_items nodes inputs initialisers) nm = [:: node n] by rewrite Hv. *)
(* move: Y; rewrite /ty (graph_sh_find _ _ _ _ _ _ nodes_sh Fg) => Y. *)
(* have oin' : ValueInfoProto_constructor (Some nm) ot od om \in (inputs ++ outputs)%SEQ. *)
(*   by rewrite mem_cat oin orbT. *)
(* set ov := ValueInfoProto_constructor (Some nm) ot od om in oin' otype *. *)
(* move: (v_sh _ oin') otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //. *)
(* case: (value_dims ov) => [l|] //= /andP [dc /eqP sh] /andP [_ /eqP [odims]]. *)
(* have dE : d = @tensorType Elem (tensorTypes _ d) (tensorDims _ d) by clear -d; case: d. *)
(* rewrite dE /=; apply: (reshape _ Y). *)
(* have /andP [h0 w0] := mat_dims_pos _ dc. *)
(* by rewrite (dims_prodE _ _ _ (esym odims) dc) /= /shn sh mat_prod. *)
(* Defined. *)
