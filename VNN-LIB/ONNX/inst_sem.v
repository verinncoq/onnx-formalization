Set Warnings "-notation-overridden,-ambiguous-paths".
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

(** Function from qTensor + predicates into mathcomp tensor **)
Definition theoryTensorProto : forall t : TensorType (ElementType syntax_inst), TheoryTensor syntax_inst t -> TensorSemantics denote t.
Proof.
rewrite /TheoryTensor.
rewrite /=.
case.
case => /= [x H] [k dims] [[t /andP [sized _]] /= /andP [Ht hasType]].
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
case/and5P: wf => acyc /allP outs_one /allP decl /allP init_ok /and3P [/allP nodes_ok /allP o_sh _].
have vop n : node n \in vertices -> valid_op n.
  by rewrite -Hv mem_graph_items_node => /nodes_ok /node_dims_ok_valid_op.
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
(** every vertex has the tensor type of its name's declared dims, in the dtype of d **)
pose shn := infer_dims nodes inputs initialisers.
pose ty (w : vertex) := @tensorType Elem (tensorTypes _ d)
  (dims_type (odflt [::] (shn (seq.head ""%string (vnames w))))).
have nodes_sh : all (node_dims_ok shn) nodes by apply/allP.
(** the graph dtype is the dtype of d **)
have dtE : (if outputs is o' :: _ then value_tensor_type o' else None) =
           Some (tag (tensorTypes _ d)).
  move: (decl o); rewrite mem_cat oin orbT => /(_ isT) /and4P [_ /eqP <- _ _].
  by case/andP: otype => /eqP.
have elemE (x : Elem) : Some (tag x) = Some (tag (tensorTypes _ d)) -> x = tensorTypes _ d.
  by move=> [] /val_inj.
(** every vertex found under a name has that name's dims **)
have sh_find its i w : {subset its <= vertices} -> find_vertex its i = [:: w] ->
    shn (seq.head ""%string (vnames w)) = shn i.
  by move=> sub F; apply: (graph_dims_find nodes inputs initialisers _ _ _ _ nodes_sh _ F); rewrite Hv.
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
      move/String.eqb_eq: sG => sE; subst s.
      case: ins win ac child found => [|a [|b [|c [|? ?]]]] //= win ac child found _.
      * (** two inputs **)
        have ina : a \in [:: a; b] by rewrite inE eqxx.
        have inb : b \in [:: a; b] by rewrite !inE eqxx orbT.
        case Fa: (find_vertex its a) => [|va [|? ?]];
          try by exfalso; case: (found a ina) => ?; rewrite Fa.
        case Fb: (find_vertex its b) => [|vb [|? ?]];
          try by exfalso; case: (found b inb) => ?; rewrite Fb.
        (** node_dims_ok: a and b are matrices with matching inner dimension, and the
            output is declared as [N; P] **)
        have Nn : node_dims_ok shn (NodeProto_constructor [:: a; b] n_outs n_name (Some """Gemm""")
                                       n_dom n_ov attrs n_doc n_meta n_x).
          by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
        move: (child a va ina Fa) (child b vb inb Fb).
        rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) /vnames /node_outputs.
        case/node_dims_ok_gemm2: Nn => da [db [ds [-> -> /gemm_out_dimsP + ->]]].
        case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB] [sa sb inner -> _] A B.
        apply: (mx_tensor (trans_dims tA (mat_of_dims da)).1 (trans_dims tB (mat_of_dims db)).2).
        pose ops := gemm_ops alpha.
        (** transpose A and B as transA, transB say, then A' * B' **)
        move: inner A B; rewrite /trans_dims.
        case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB] inner A B;
          first [ exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T))
                | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T)) ].
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
        have Nn : node_dims_ok shn (NodeProto_constructor [:: a; b; c] n_outs n_name (Some """Gemm""")
                                       n_dom n_ov attrs n_doc n_meta n_x).
          by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
        move: (child a va ina Fa) (child b vb inb Fb) (child c vc inc Fc).
        rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) (sh_find _ _ _ sub Fc).
        rewrite /vnames /node_outputs.
        case/node_dims_ok_gemm3: Nn => da [db [dc [ds [-> -> -> /gemm_out_dimsP + ->]]]].
        case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB] [sa sb inner -> cok] A B C.
        have sc : (size dc <= 2)%nat by move: cok; case: (mat_of_dims dc) => ? ? /andP [].
        apply: (mx_tensor (trans_dims tA (mat_of_dims da)).1 (trans_dims tB (mat_of_dims db)).2).
        pose ops := gemm_ops alpha.
        pose beta' := (gemm_ops beta).2.
        (** C broadcast to (N, P): a dimension of size 1 always reads index 0 **)
        move: inner A B; rewrite /trans_dims.
        case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB] inner A B;
          first [ exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B))
                           (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B))
                           (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T)
                           (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j)))
                | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)^T
                           (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T)
                           (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j))) ].
    + case: ifP => // sR.
      (** Relu: the same dims as its input, whatever the rank **)
      move/String.eqb_eq: sR => sE; subst s.
      case: ins win ac child found => [|a [|? ?]] //= win ac child found _.
      have ina : a \in [:: a] by rewrite inE eqxx.
      case Fa: (find_vertex its a) => [|va [|? ?]];
        try by exfalso; case: (found a ina) => ?; rewrite Fa.
      have Nn : node_dims_ok shn (NodeProto_constructor [:: a] n_outs n_name (Some """Relu""")
                                     n_dom n_ov attrs n_doc n_meta n_x).
        by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node.
      move: (child a va ina Fa); rewrite /ty (sh_find _ _ _ sub Fa) /vnames /node_outputs.
      move/node_dims_ok_relu: Nn => -> A.
      exact (@Tensor _ _ _ _ _ (op_relu relu_ops.1 relu_ops.2 (tensor_val A))).
  - (** Tensor: just return itself **)
    have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor.
    have := sized t (sub _ win).
    have tsh : if tensor_name t is Some s
               then infer_dims nodes inputs initialisers s == Some (map int64_to_dim (get_dims t))
               else false.
      move: (init_ok t tin) => /and3P [_ _]; case E: (tensor_name t) => [s|] // _.
      by rewrite (infer_dims_initialiser _ _ _ _ _ acyc tin E) eqxx.
    move: (init_ok t tin) => /and3P [/eqP tdt _ _].
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
      (** T has the type of t's dims **)
      have xE : exist _ x xin = tensorTypes _ d.
        by apply: elemE; rewrite -dtE -tdt /= E.
      move: T; rewrite xE /ty /vnames /=.
      case Etn: tn tsh => [s|] //= /eqP; rewrite -/shn => -> T.
      exact (@eq_rect _ (existT _ (size dims) shape)
               (fun ds => TensorSemantics denote (@tensorType Elem (tensorTypes _ d) ds))
               T _ (dims_typeE _ _ _ shapeE)).
    apply: theoryTensorProto.
    have tnamed : tn by move: tsh; destruct tn.
    pose q := qtensor_pi (TensorProto_constructor dims (Some dt) seg fd i32 sd i64 tn
                                                  ds rd ed dl dd u64 mp).
    have qsized : tensorProtoSized q && tensorNamed q.
      rewrite /q /= /storage_of.
      case: x E Hsize xin => // E Hsize xin;
        [have HZ := DataType_float E | have HZ := DataType_int32 E | have HZ := DataType_int64 E];
        by rewrite HZ /= E Hsize dpos /=.
    exists (exist _ q qsized).
    rewrite /= /q {qsized q tnamed}.
    have Edims : dims = map (tnth (in_tuple dims)) (fintype.enum 'I_(size dims)).
      by rewrite map_tnth_enum.
    case: x E Hsize xin => // E Hsize xin;
      [move: (DataType_float E) | move: (DataType_int32 E) | move: (DataType_int64 E)] => Z;
      rewrite /= /storage_of Z /= E eqxx /= !andbT;
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
    (** X has the type of the input's declared dims **)
    have vsh : if (value_name v, value_dims v) is (Some s, Some ds)
               then infer_dims nodes inputs initialisers s == Some (map int64_to_dim ds)
               else false.
      move: (decl v); rewrite mem_cat vin => /(_ isT) /and4P [_ _].
      case Evn: (value_name v) => [s|] // _; case Evd: (value_dims v) => [ds|] // _.
      by rewrite (infer_dims_input _ _ _ _ _ _ acyc vin Evn Evd) eqxx.
    move: vsh vdims.
    rewrite /ty /vnames /= -eiE.
    case: (value_name v) => [nm|] //=.
    case: (value_dims v) => [l|] //= /eqP; rewrite -/shn => -> [vdims].
    exact (@eq_rect _ (existT _ ki dsi)
             (fun ds => TensorSemantics denote (@tensorType Elem ei ds))
             X _ (dims_typeE _ _ _ (esym vdims))).
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
(** Y has the type of the output's declared dims, which are d's **)
move: Y; rewrite /ty (sh_find _ _ _ (fun _ x => x) F) => Y.
set ov := ValueInfoProto_constructor (Some nm) ot od om in oin otype *.
move: (o_sh _ oin) otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //.
case: (value_dims ov) => [l|] //= /eqP sh /andP [_ /eqP [odims]].
have HT : tensorDims _ d = dims_type (map int64_to_dim l).
  by case: (tensorDims _ d) odims => kd dsd /= odims; exact: dims_typeE (esym odims).
have dE : d = @tensorType Elem (tensorTypes _ d) (tensorDims _ d) by clear -d; case: d.
rewrite /shn sh in Y.
exact (@eq_rect _ _ (TensorSemantics denote)
         (@eq_rect _ (dims_type (map int64_to_dim l))
            (fun ds => TensorSemantics denote (@tensorType Elem (tensorTypes _ d) ds))
            Y _ (esym HT))
         _ (esym dE)).
Defined.

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
