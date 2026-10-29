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
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst real inst_syntax.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.


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
case: x H => // _ dims_eq /eqP <- /andP [dims_pos /eqP data_sized].
- apply: Tensor. rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple float) (cast_ord _ i)).
  move=> _ _.
  rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord.
  move: (f_equal size dims_eq).
  rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->.
  apply/eq_bigr => i _.
  have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=.
  rewrite (nth_map default_zero); first by rewrite Hk ltn_ord.
  rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord.
  rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord.
  by rewrite nth_ord_enum => ->.
- apply: Tensor; rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int32) (cast_ord _ i)).
  move=> _ _.
  rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord.
  move: (f_equal size dims_eq).
  rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->.
  apply/eq_bigr => i _.
  have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=.
  rewrite (nth_map default_zero); first by rewrite Hk ltn_ord.
  rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord.
  rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord.
  by rewrite nth_ord_enum => ->.
- apply: Tensor; rewrite big_ord0.
  apply: (\col_(i < \prod_(i < k) (dims i)%:posnum) tnth (in_tuple int64) (cast_ord _ i)).
  move=> _ _.
  rewrite data_sized /dims_prod /= (big_nth default_zero) big_mkord.
  move: (f_equal size dims_eq).
  rewrite !size_map /= -enumT size_enum_ord => /[dup] Hk ->.
  apply/eq_bigr => i _.
  have := congr1 (fun s => nth (dims i)%:posnum s i) dims_eq => /=.
  rewrite (nth_map default_zero); first by rewrite Hk ltn_ord.
  rewrite (nth_map (dims i));     first by rewrite size_map size_enum_ord ltn_ord.
  rewrite (nth_map i);            first by rewrite size_enum_ord ltn_ord.
  by rewrite nth_ord_enum => ->.
Defined.

(*
Executes the network by exploring the ModelProto exactly as
ONNXEvaluator.onnx_evaluator does: build the same list of vertices,
evaluate the output vertex, and recurse through node inputs found with
find_vertex. Every failure branch of onnx_evaluator is ruled out by
model_well_formed (the fuel by acyclic_at, as in well_formed_computes).
- Node:   Gemm (2 or 3 inputs) and Relu inputs are evaluated recursively,
          then gemm_2_inputs, gemm_3_inputs or op_relu is applied.
- Tensor: the initialiser is turned into a mathcomp tensor with
          theoryTensorProto.
- Input:  the semantic inputs are positional, so the input at the same
          position in the graph inputs is returned.
Intermediate vertices evaluate to a tensor of some type d'.
*)

Definition gemm_2_inputs {R} {m n p} (zero : R) (mul : R -> R -> R) (add : R -> R -> R)
(a : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \big[add/zero]_j (mul a (mul (m1 i j) (m2 j k))).

Definition gemm_3_inputs {R} {m n p} (zero : R) (mul : R -> R -> R) (add : R -> R -> R)
(a b : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) (m3 : 'M[R]_(m, p)) : 'M[R]_(m, p) :=
  (map2_mx (fun x y => add x (mul b y)) (\matrix[mulmx_key]_(i, k) \big[add/zero]_j (mul a (mul (m1 i j) (m2 j k)))) m3).

Definition op_relu {R} {m n} (zero : R) (lt : R -> R -> bool)
                   (m1 : 'M[R]_(m, n)) : 'M[R]_(m, n) :=
  map_mx (fun x => if lt x zero then zero else x) m1.

(* TODO: Make this so that it extracts model to a maths function over mathcomp tensors and applies it to inputSemantics. Must cascade input through entire graph.
 Map model to a function over mathcomp tensor **)
(** The rank-2 type of a static shape (h, w); [insubd] keeps it total, and on
    well-formed shapes it is the identity *)
Definition mat_type (e : Elem) (hw : nat * nat) : TensorType Elem :=
  @tensorType Elem e (existT _ 2%nat [ffun i : 'I_2 =>
    insubd 1%:posnat
           (if i == ord0 then hw.1 else hw.2)]).

(** Reshape a tensor to any shape with the same number of entries **)
Definition reshape {R : Type} {k k'} {ds : {posnum nat} ^ k} {ds' : {posnum nat} ^ k'}
  (E : (\prod_(i < k) (ds i)%:num = \prod_(i < k') (ds' i)%:num)%nat)
  (t : 'nT[R]_(ds)) : 'nT[R]_(ds') :=
  @Tensor _ _ ds' [tuple] R (castmx (E, erefl) (tensor_val t)).

Definition modelTensorProto (y : NetworkType (ElementType syntax_inst))
(n : Model syntax_inst y) (inp : InputSemantics denote y)
(d : TensorType (ElementType syntax_inst)) (u : NodeOutputName syntax_inst)
(out : NodeOutput syntax_inst n u d) : TensorSemantics denote d.
Proof.
case: y n inp out => [[inps inps_gt0] [outs outs_gt0]] [m /andP [dm wf]] /= inp.
case=> o /and3P [oin /eqP oname otype].
case: m dm wf oin => ir opset prod_name prod_vers domain model_version doc
  [[nodes name initialisers sparse_initialisers doc_string inputs outputs value_info
    quantisation metadata_props]|//] metadata training functions config dm wf oin /=.
move: dm wf oin => /= dm wf oin.
(** [vertices] of onnx_evaluator **)
move Hv: (graph_items nodes inputs initialisers) => vertices.
move/andP: wf => [/and4P [acyc /allP outs_one /allP decl /allP init_ok]].
move=> /and3P [/allP nodes_ok /allP v_sh /allP i_sh].
have vop n : node n \in vertices -> valid_op n.
  by rewrite -Hv mem_graph_items_node => /nodes_ok /andP [].
have sized t : tensor t \in vertices -> tensorProtoSized t.
  by rewrite -Hv mem_graph_items_tensor => /init_ok /and3P [].
have named i : input i \in vertices -> value_name i != None.
  rewrite -Hv mem_graph_items_input => iin.
  by move: (decl i); rewrite mem_cat iin => /(_ isT) /and4P [].
have in_inputs i : input i \in vertices -> i \in inputs.
  by rewrite -Hv mem_graph_items_input.
have no_output v : output v \in vertices = false.
  by rewrite -Hv output_notin_graph_items.
have Hsz : size inps = size inputs.
  by move/and4P: dm => [_ _ + _]; rewrite all2E => /andP [/eqP].
(** every vertex has the matrix type of its static shape, in the dtype of d **)
pose shn := name_shape initialisers (inputs ++ outputs ++ value_info)%SEQ.
pose ty (w : vertex) := mat_type (tensorTypes _ d) (shn (seq.head ""%string (vnames w))).
have nodes_sh : all (node_shape_ok shn) nodes.
  by apply/allP => m /nodes_ok /andP [_ /andP []].
(** the graph dtype is the dtype of d **)
have dtE : (if outputs is o' :: _ then value_tensor_type o' else None) =
           Some (tag (tensorTypes _ d)).
  move: (decl o); rewrite mem_cat oin orbT => /(_ isT) /and4P [_ /eqP <- _ _].
  by case/andP: otype => /eqP.
have elemE (x : Elem) : Some (tag x) = Some (tag (tensorTypes _ d)) -> x = tensorTypes _ d.
  by move=> [] /val_inj.
(** reshaping a declared shape l of the name s into the matrix type of s **)
have mat_prod hw : (0 < hw.1)%nat -> (0 < hw.2)%nat ->
  (\prod_(i < 2) ([ffun i : 'I_2 => insubd 1%:posnat (if i == ord0 then hw.1 else hw.2)] i
     : {posnum nat})%:num = hw.1 * hw.2)%nat.
  case: hw => [h w] /= h0 w0; rewrite big_ord_recr big_ord1 /= !ffunE /= !insubdK //;
    by rewrite -topredE /= /Itv.spec /= /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat.
have dims_prodE k (ds : {posnum nat} ^ k) (l : seq int64) :
  map (fun q : {posnum nat} => q%:num) (tval ds) = map int64_to_dim l ->
  dims_correct l -> (\prod_(i < k) (ds i)%:num = (mat_dims l).1 * (mat_dims l).2)%nat.
  move=> E dc; rewrite -mat_dims_prod // /dims_prod -(big_map int64_to_dim xpredT id) -E big_map.
  by rewrite big_tuple; apply: eq_bigr => i _; rewrite /tuple_of_finfun tnth_mktuple.
have to_mat (e : Elem) s k (ds : {posnum nat} ^ k) (l : seq int64) :
  map (fun q : {posnum nat} => q%:num) (tval ds) = map int64_to_dim l ->
  dims_correct l -> shn s = mat_dims l ->
  'nT[denote e]_(ds) -> TensorSemantics denote (mat_type e (shn s)).
  move=> E dc sh t /=; apply: (reshape _ t).
  have /andP [h0 w0] := mat_dims_pos _ dc.
  by rewrite (dims_prodE _ _ _ E dc) sh mat_prod.
(** every vertex found under a name has that name's static shape **)
have sh_find its i w : {subset its <= vertices} -> find_vertex its i = [:: w] ->
    shn (seq.head ""%string (vnames w)) = shn i.
  move=> sub F; have win : w \in vertices by apply: sub; exact: finds_in F.
  have : vertex_has_name i w.
    have : w \in find_vertex its i by rewrite F mem_head.
    by rewrite /find_vertex filterE mem_filter => /andP [].
  rewrite vertex_has_nameE; move: win; rewrite -Hv.
  case: w {F} => [m|t|i'|o'] win /=.
  - move=> iin; have mn : m \in nodes by rewrite -(mem_graph_items_node _ inputs initialisers).
    have [S /andP [ne /allP HS]] := node_shape_ok_outs _ _ (allP nodes_sh m mn).
    rewrite (eqP (HS i iin)); case: (node_outputs m) ne HS => [|o1 os] //= _ HS.
    by rewrite (eqP (HS o1 (mem_head _ _))).
  - by case: (tensor_name t) => [s|] //=; rewrite inE => /eqP ->.
  - by case: (value_name i') => [s|] //=; rewrite inE => /eqP ->.
  - by case: (value_name o') => [s|] //=; rewrite inE => /eqP ->.
(** a value of matrix type (h, w) as a mathcomp matrix, and back **)
pose dimc (x : nat) : nat := ltac:(exact ((insubd 1%:posnat x : {posnum nat})%:num)).
have prod2 hw : (\prod_(i < 2) ([ffun i : 'I_2 => insubd 1%:posnat (if i == ord0 then hw.1 else hw.2)] i
                  : {posnum nat})%:num = dimc hw.1 * dimc hw.2)%nat.
  by rewrite big_ord_recr big_ord1 /= !ffunE.
have prod0 (f : {posnum nat} ^ 0) : (\prod_(j < 0) (f j)%:num = 1)%nat by rewrite big_ord0.
pose to_m hw (t : TensorSemantics denote (mat_type (tensorTypes _ d) hw))
  : 'M[denote (tensorTypes _ d)]_(dimc hw.1, dimc hw.2) :=
  vec_mx (castmx (prod0 _, prod2 hw) (tensor_val t)^T).
pose of_m hw (M : 'M[denote (tensorTypes _ d)]_(dimc hw.1, dimc hw.2))
  : TensorSemantics denote (mat_type (tensorTypes _ d) hw) :=
  @Tensor _ _ _ _ _ (castmx (esym (prod2 hw), esym (prod0 _)) (mxvec M)^T).
(** zero, mul and add of the dtype of d, and alpha converted to it, as in op_gemm **)
pose gemm_ops (alpha : float32) : denote (tensorTypes _ d) *
    (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> denote (tensorTypes _ d)) *
    (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> denote (tensorTypes _ d)) *
    denote (tensorTypes _ d) :=
  ltac:(case: (tensorTypes _ d) => [[] xin];
        first [ exact (Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE 0 0 false,
                       b32_mult BinarySingleNaN.mode_NE, b32_plus BinarySingleNaN.mode_NE, alpha)
              | exact (int32_of_Z 0, fun x y => int32_of_Z (Z_of_int32 x * Z_of_int32 y)%Z,
                       fun x y => int32_of_Z (Z_of_int32 x + Z_of_int32 y)%Z,
                       int32_of_Z (odflt 0%Z (Z_of_float32 alpha)))
              | exact (int64_of_Z 0, fun x y => int64_of_Z (Z_of_int64 x * Z_of_int64 y)%Z,
                       fun x y => int64_of_Z (Z_of_int64 x + Z_of_int64 y)%Z,
                       int64_of_Z (odflt 0%Z (Z_of_float32 alpha)))
              | by exfalso; move: xin; rewrite !inE => /or3P [] /eqP ]).
(** the value relu sends negatives to, and the comparison it uses, as in op_relu **)
pose relu_ops : denote (tensorTypes _ d) *
    (denote (tensorTypes _ d) -> denote (tensorTypes _ d) -> bool) :=
  ltac:(case: (tensorTypes _ d) => [[] xin];
        first [ exact (Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE 0 0 true,
                       fun x y : float32 => if x is Binary.B754_finite true _ _ _ then (if Binary.Bcompare 24 128 x y is Some Lt then true else false) else false)
              | exact (int32_of_Z 0, fun x y => (Z_of_int32 x <? Z_of_int32 y)%Z)
              | exact (int64_of_Z 0, fun x y => (Z_of_int64 x <? Z_of_int64 y)%Z)
              | by exfalso; move: xin; rewrite !inE => /or3P [] /eqP ]).
(** broadcasting index: k if it is in range, otherwise 0 **)
have dimc_gt0 x : (0 < dimc x)%nat.
  by rewrite /dimc; case: (insubd _ _) => v /=; rewrite /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat.
pose bidx x (k : nat) : 'I_(dimc x) := insubd (Ordinal (dimc_gt0 x)) k.
(** onnx_evaluator_recursive **)
have go : forall (depth : nat) (its : seq vertex) (w : vertex),
    size its = depth -> w \in its -> {subset its <= vertices} -> acyclic_at its w ->
    TensorSemantics denote (ty w).
  elim=> [|depth IH] its w Hd win sub ac.
    by move/size0nil: Hd win => ->.
  case: w win ac => [n|t|v|v] win ac.
  - (** Node: check op_type and compute it if possible **)
    have child i w : i \in node_inputs n -> find_vertex its i = [:: w] ->
        TensorSemantics denote (ty w).
      move=> iin F.
      have wn : w != node n.
        by have [w' F' wn] := acyclic_at_find ac iin; move: F' wn; rewrite F => -[->].
      apply: (IH (rem (node n) its) w).
      + by rewrite size_rem // Hd.
      + exact: rem_mem (finds_in F).
      + by move=> z /mem_rem /sub.
      + exact: acyclic_at_child ac iin F.
    have found i : i \in node_inputs n ->
        exists2 w, find_vertex its i = [:: w] & w != node n := acyclic_at_find ac.
    have := vop n (sub _ win).
    case: n win ac child found => ins n_outs n_name [s|] n_dom n_ov attrs n_doc n_meta n_x
                                  win ac child found //=.
    case: ifP => sG.
    + (** Gemm **)
      case: ins win ac child found => [|a [|b [|c [|? ?]]]] //= win ac child found _.
      * (** two inputs **)
        have ina : a \in [:: a; b] by rewrite inE eqxx.
        have inb : b \in [:: a; b] by rewrite !inE eqxx orbT.
        case Fa: (find_vertex its a) => [|va [|? ?]];
          try by exfalso; case: (found a ina) => ?; rewrite Fa.
        case Fb: (find_vertex its b) => [|vb [|? ?]];
          try by exfalso; case: (found b inb) => ?; rewrite Fb.
        (** node_shape_ok: the static shapes of a, b and the output agree **)
        have Nn : node_shape_ok shn (NodeProto_constructor [:: a; b] n_outs n_name (Some s)
                                       n_dom n_ov attrs n_doc n_meta n_x).
          by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
        move: (child a va ina Fa) (child b vb inb Fb).
        rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb).
        move: Nn; rewrite /node_shape_ok sG.
        case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB].
        case/and3P => inner /andP [ne /allP outs_sh] _ A B.
        have hd : seq.head ""%string n_outs \in n_outs.
          by case: (n_outs) ne => // ? ? _; exact: mem_head.
        rewrite (eqP (outs_sh _ hd)).
        apply: (of_m (_, _)).
        pose ops := gemm_ops alpha.
        (** transpose A and B as transA, transB say, then A' * B' **)
        move: inner A B; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB];
          move=> /eqP inner A B;
          first [ exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (to_m (shn a) A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)) ].
      * (** three inputs **)
        have ina : a \in [:: a; b; c] by rewrite inE eqxx.
        have inb : b \in [:: a; b; c] by rewrite !inE eqxx orbT.
        have inc : c \in [:: a; b; c] by rewrite !inE eqxx !orbT.
        case Fa: (find_vertex its a) => [|va [|? ?]];
          try by exfalso; case: (found a ina) => ?; rewrite Fa.
        case Fb: (find_vertex its b) => [|vb [|? ?]];
          try by exfalso; case: (found b inb) => ?; rewrite Fb.
        case Fc: (find_vertex its c) => [|vc [|? ?]];
          try by exfalso; case: (found c inc) => ?; rewrite Fc.
        have Nn : node_shape_ok shn (NodeProto_constructor [:: a; b; c] n_outs n_name (Some s)
                                       n_dom n_ov attrs n_doc n_meta n_x).
          by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
        move: (child a va ina Fa) (child b vb inb Fb) (child c vc inc Fc).
        rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) (sh_find _ _ _ sub Fc).
        move: Nn; rewrite /node_shape_ok sG.
        case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB].
        case/and3P => inner /andP [ne /allP outs_sh] _ A B C.
        have hd : seq.head ""%string n_outs \in n_outs.
          by case: (n_outs) ne => // ? ? _; exact: mem_head.
        rewrite (eqP (outs_sh _ hd)).
        apply: (of_m (_, _)).
        pose ops := gemm_ops alpha.
        pose beta' := (gemm_ops beta).2.
        (** C broadcast to (N, P): a dimension of size 1 always reads index 0 **)
        move: inner A B C; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB];
          move=> /eqP inner A B C;
          first [ exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))
                           (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))
                           (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)
                           (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (to_m (shn a) A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)
                           (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))) ].
    + case: ifP => // sR.
      (** Relu **)
      case: ins win ac child found => [|a [|? ?]] //= win ac child found _.
      have ina : a \in [:: a] by rewrite inE eqxx.
      case Fa: (find_vertex its a) => [|va [|? ?]];
        try by exfalso; case: (found a ina) => ?; rewrite Fa.
      have Nn : node_shape_ok shn (NodeProto_constructor [:: a] n_outs n_name (Some s)
                                     n_dom n_ov attrs n_doc n_meta n_x).
        by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
      move: (child a va ina Fa); rewrite /ty (sh_find _ _ _ sub Fa).
      move: Nn; rewrite /node_shape_ok sG sR => /andP [ne /allP outs_sh] A.
      have hd : seq.head ""%string n_outs \in n_outs.
        by case: (n_outs) ne => // ? ? _; exact: mem_head.
      rewrite (eqP (outs_sh _ hd)).
      exact (of_m _ (op_relu relu_ops.1 relu_ops.2 (to_m (shn a) A))).
  - (** Tensor: just return itself **)
    have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor.
    have := sized t (sub _ win).
    move: (init_ok t tin) (i_sh t tin) => /and3P [/eqP tdt _ _] tsh.
    case: t win ac tin tdt tsh => dims [dt|] seg fd i32 sd i64 tn ds rd ed dl dd u64 mp
                                  win ac tin tdt tsh /andP [dpos] //.
    case E: (DataType_TensorProto_of_int32 dt) => [x|] // Hsize.
    have xin : x \in supported_types by case: x E Hsize.
    have pos (i : 'I_(size dims)) : Itv.spec Itv.nat_sem (Itv.Real `]0%R, +oo[)
                                     (int64_to_dim (tnth (in_tuple dims) i)).
      have := allP dpos _ (mem_tnth i (in_tuple dims)).
      by rewrite /Itv.spec /= /Itv.nat_sem in_itv /= andbT.
    (** [ltac:] so that the positivity of [1%:posnat] is solved, not abstracted **)
    pose shape : {posnum nat} ^ (size dims) :=
      ltac:(exact [ffun i => insubd 1%:posnat (int64_to_dim (tnth (in_tuple dims) i))]).
    have shapeE : map (fun q : {posnum nat} => q%:num) (tval shape) = map int64_to_dim dims.
      have -> : map (fun q : {posnum nat} => q%:num) (tval shape) =
                tval (map_tuple (fun q : {posnum nat} => q%:num) shape) by [].
      have -> : map int64_to_dim dims = tval (map_tuple int64_to_dim (in_tuple dims)) by [].
      congr tval; apply: eq_from_tnth => i.
      by rewrite !tnth_map tnth_ord_tuple ffunE insubdK //; exact: pos i.
    suff T : TensorSemantics denote (@tensorType Elem (exist _ x xin) (existT _ (size dims) shape)).
      (** reshape T to the matrix type of t **)
      have xE : exist _ x xin = tensorTypes _ d.
        by apply: elemE; rewrite -dtE -tdt /= E.
      move: T; rewrite xE /ty /=.
      case Etn: tn tsh => [s|] //= /andP [dc /eqP sh] T.
      exact: (to_mat _ s _ shape dims shapeE dc sh T).
    apply: theoryTensorProto.
    exists (qtensor_pi (TensorProto_constructor dims (Some dt) seg fd i32 sd i64 tn
                                                ds rd ed dl dd u64 mp)).
    have Edims : dims = map (tnth (in_tuple dims)) (fintype.enum 'I_(size dims)).
      by rewrite map_tnth_enum.
    case: x E Hsize xin => // E Hsize xin;
      [move: (DataType_float E) | move: (DataType_int32 E) | move: (DataType_int64 E)] => Z;
      rewrite /= /storage_of Z /= E eqxx Hsize dpos /= !andbT;
      rewrite -map_comp; apply/eqP;
      rewrite {1}Edims;
      by rewrite -map_comp enumT; apply: eq_map => i /=; rewrite ffunE insubdK //; exact: pos i.
  - (** Input: the user inputs are positional, take the one at v's position **)
    have vin := in_inputs v (sub _ win).
    have ilt : (seq.index v inputs < size inps)%nat by rewrite Hsz index_mem.
    (** network_dim_match: the input at v's position has v's declared type **)
    have vt_ok : value_has_type (tnth (in_tuple inps) (Ordinal ilt)) v.
      move/and4P: dm => [_ _ + _]; rewrite all2E => /andP [_ /all_nthP same].
      have := same (tnth (in_tuple inps) (Ordinal ilt), v) (seq.index v inputs).
      rewrite nth_zip_cond size_zip -Hsz minnn ilt => /(_ isT) /=.
      by rewrite nth_index // -(tnth_nth _ (in_tuple inps) (Ordinal ilt)).
    move: (inp (Ordinal ilt)) vt_ok.
    case: (tnth (in_tuple inps) (Ordinal ilt)) => ei [ki dsi] /= X /andP [/eqP vdt /eqP vdims].
    have eiE : ei = tensorTypes _ d.
      apply: elemE; rewrite -vdt -dtE.
      by move: (decl v); rewrite mem_cat vin => /(_ isT) /and4P [_ /eqP].
    (** reshape X to the matrix type of the input **)
    move: (v_sh v) vdims; rewrite mem_cat vin => /(_ isT).
    rewrite /ty /= -eiE.
    case: (value_name v) => [nm|] //=.
    case: (value_dims v) => [l|] //= /andP [dc /eqP sh] [vdims].
    exact: (to_mat _ nm _ dsi l (esym vdims) dc sh X).
  - (** Output **)
    by move: (sub _ win); rewrite no_output.
(** onnx_evaluator: evaluate the output vertex **)
have := outs_one o oin; rewrite -/(graph_items nodes inputs initialisers) Hv.
case: o oin oname otype dtE => [[nm|] ot od om] oin oname otype dtE //=.
(** model_well_formed: the output names exactly one vertex, a node **)
case F: (find_vertex vertices nm) => [|w [|? ?]] //; last by case: w F.
case: w F => // n F _.
have win := finds_in F.
have ac : acyclic_at vertices (node n).
  by move: (graph_acyclic_at (node n) acyc); rewrite Hv => /(_ win).
have Y := go (size vertices) vertices (node n) erefl win (fun _ x => x) ac.
(** reshape Y to d: the output's declared dims are d's and its static shape **)
have Fg : find_vertex (graph_items nodes inputs initialisers) nm = [:: node n] by rewrite Hv.
move: Y; rewrite /ty (graph_sh_find _ _ _ _ _ _ nodes_sh Fg) => Y.
have oin' : ValueInfoProto_constructor (Some nm) ot od om \in (inputs ++ outputs)%SEQ.
  by rewrite mem_cat oin orbT.
set ov := ValueInfoProto_constructor (Some nm) ot od om in oin' otype *.
move: (v_sh _ oin') otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //.
case: (value_dims ov) => [l|] //= /andP [dc /eqP sh] /andP [_ /eqP [odims]].
have dE : d = @tensorType Elem (tensorTypes _ d) (tensorDims _ d) by clear -d; case: d.
rewrite dE /=; apply: (reshape _ Y).
have /andP [h0 w0] := mat_dims_pos _ dc.
by rewrite (dims_prodE _ _ _ (esym odims) dc) /= /shn sh mat_prod.
Defined.

(* the two are genuine inverses: encoding then decoding always recovers
   the original constructor *)
Lemma DataType_TensorProto_int32_roundtrip (x : DataType_TensorProto) :
  DataType_TensorProto_of_int32 (int32_of_DataType_TensorProto x) = Some x.
Proof. by case: x. Qed.

Definition TensorProto_le (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_le (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) <= (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) <= (\val t2 ij.1 ij.2)].
Defined.

Definition TensorProto_lt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_lt (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) < (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) < (\val t2 ij.1 ij.2)].
Defined.

Definition TensorProto_ge (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_ge (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) >= (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) >= (\val t2 ij.1 ij.2)].
Defined.

Definition TensorProto_gt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_gt (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) > (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) > (\val t2 ij.1 ij.2)].
Defined.

Definition TensorProto_eq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof. case: d => [[/= [] //= Px]] [k dims] /= t1 t2; exact: (t1 == t2). Qed.

Definition TensorProto_neq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
  negb (TensorProto_eq d t1 t2).

Definition TensorProto_neg (d : TensorType (ElementType syntax_inst)) : TensorOp1 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t.
exact: (@Tensor _ _ dims _ float32 (map_mx (b32_mult BinarySingleNaN.mode_NE default_minus_one) (\val t))).
exact: (@Tensor _ _ dims _ int32 (map_mx (fun h1 => int32_of_Z (- (Z_of_int32 h1))) (\val t))).
exact: (@Tensor _ _ dims _ int64 (map_mx (fun h1 => int64_of_Z (- (Z_of_int64 h1))) (\val t))).
Defined.

Definition TensorProto_add (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t u.
exact: (@Tensor _ _ dims _ float32 (map2_mx (b32_plus BinarySingleNaN.mode_NE) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int32 (map2_mx (fun h1 h2 => int32_of_Z
                                                       ((Z_of_int32 h2) + (Z_of_int32 h1))) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int64 (map2_mx (fun h1 h2 => int64_of_Z ((Z_of_int64 h1) + (Z_of_int64 h2))) (\val t) (\val u))).
Defined.

(** TODO: The zero_tensor needs to be reshaped **)
Definition TensorProto_mul (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t u.
exact: (@Tensor _ _ dims _ float32 (map2_mx (b32_mult BinarySingleNaN.mode_NE) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int32 (map2_mx (fun h1 h2 => int32_of_Z
                                                       ((Z_of_int32 h2) * (Z_of_int32 h1))) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int64 (map2_mx (fun h1 h2 => int64_of_Z ((Z_of_int64 h1) * (Z_of_int64 h2))) (\val t) (\val u))).
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
