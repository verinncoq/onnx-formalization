From ONNXFormalization.ONNXConverter Require Import model.

From Stdlib Require Import Rdefinitions.
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
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

(********************************************)
(**************** REALS *********************)
(********************************************)

(*
Real-valued version of ONNXEvaluator/theory/onnx_evaluator.v.
The graph walk is the same as onnx_evaluator_recursive. The values on the
edges are the semantic tensors themselves, each paired with its tensor type:
  {d : TensorType RealElementType & TensorSemantics realElementTypeInterp d}
Gemm and Relu are computed directly on these with mathcomp operations.
*)

Definition realSemantics : (@RealNetworkSemantics syntax_inst R).
move=> [[inps inps_gt0] [outs outs_gt0]] [[inps' inps_gt0'] [outs' outs_gt0']] d1 d2 u
  [m /= /andP [dm wf]] /andP [in_match _] inp.
case=> o /and3P [oin /eqP oname otype] d12.
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
have Hsz' : size inps' = size inps.
  by move: in_match; rewrite all2E => /andP [/eqP].
(** the real rank-2 tensor type of a static shape (h, w), as mat_type **)
pose sem := @realElementTypeInterp R.
pose rmat_type : nat * nat -> TensorType RealElementType :=
  ltac:(exact (fun hw => @tensorType RealElementType real (existT _ 2%nat [ffun i : 'I_2 =>
    insubd 1%:posnat (if i == ord0 then hw.1 else hw.2)]))).
(** every vertex has the real matrix type of its static shape **)
pose shn := name_shape initialisers (inputs ++ outputs ++ value_info)%SEQ.
pose ty (w : vertex) := rmat_type (shn (seq.head ""%string (vnames w))).
have nodes_sh : all (node_shape_ok shn) nodes.
  by apply/allP => m /nodes_ok /andP [_ /andP []].
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
have to_mat s k (ds : {posnum nat} ^ k) (l : seq int64) :
  map (fun q : {posnum nat} => q%:num) (tval ds) = map int64_to_dim l ->
  dims_correct l -> shn s = mat_dims l ->
  'nT[R]_(ds) -> TensorSemantics sem (rmat_type (shn s)).
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
pose to_m hw (t : TensorSemantics sem (rmat_type hw)) : 'M[R]_(dimc hw.1, dimc hw.2) :=
  vec_mx (castmx (prod0 _, prod2 hw) (tensor_val t)^T).
pose of_m hw (M : 'M[R]_(dimc hw.1, dimc hw.2)) : TensorSemantics sem (rmat_type hw) :=
  @Tensor _ _ _ _ _ (castmx (esym (prod2 hw), esym (prod0 _)) (mxvec M)^T).
(** the attributes alpha and beta as reals **)
pose R_of_float32 (f : float32) : R := Binary.B2R 24 128 f.
(** broadcasting index: k if it is in range, otherwise 0 **)
have dimc_gt0 x : (0 < dimc x)%nat.
  by rewrite /dimc; case: (insubd _ _) => v /=; rewrite /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat.
pose bidx x (k : nat) : 'I_(dimc x) := insubd (Ordinal (dimc_gt0 x)) k.
(** onnx_evaluator_recursive **)
have go : forall (depth : nat) (its : seq vertex) (w : vertex),
    size its = depth -> w \in its -> {subset its <= vertices} -> acyclic_at its w ->
    TensorSemantics sem (ty w).
  elim=> [|depth IH] its w Hd win sub ac.
    by move/size0nil: Hd win => ->.
  case: w win ac => [n|t|v|v] win ac.
  - (** Node: check op_type and compute it if possible **)
    have child i w : i \in node_inputs n -> find_vertex its i = [:: w] ->
        TensorSemantics sem (ty w).
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
        (** alpha A' B', with A' and B' transposed as transA, transB say **)
        move: inner A B; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB];
          move=> /eqP inner A B;
          first [ exact (scalemx (R_of_float32 alpha) ((to_m (shn a) A)
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))))
                | exact (scalemx (R_of_float32 alpha) ((to_m (shn a) A)^T
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B))))
                | exact (scalemx (R_of_float32 alpha) ((to_m (shn a) A)
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T)))
                | exact (scalemx (R_of_float32 alpha) ((to_m (shn a) A)^T
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T))) ].
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
        (** alpha A' B' + beta C, with C broadcast to (N, P): a dimension of size 1
            always reads index 0 **)
        move: inner A B C; case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB];
          move=> /eqP inner A B C;
          first [ exact ((scalemx (R_of_float32 alpha) ((to_m (shn a) A)
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)))) +
                                (scalemx (R_of_float32 beta)
                                  (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))))%R
                | exact ((scalemx (R_of_float32 alpha) ((to_m (shn a) A)^T
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)))) +
                                (scalemx (R_of_float32 beta)
                                  (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))))%R
                | exact ((scalemx (R_of_float32 alpha) ((to_m (shn a) A)
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T))) +
                                (scalemx (R_of_float32 beta)
                                  (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))))%R
                | exact ((scalemx (R_of_float32 alpha) ((to_m (shn a) A)^T
                           *m (castmx (congr1 dimc (esym inner), erefl) (to_m (shn b) B)^T))) +
                                (scalemx (R_of_float32 beta)
                                  (\matrix_(i, j) to_m (shn c) C (bidx _ i) (bidx _ j))))%R ].
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
      exact (of_m _ (map_mx (fun x => Num.max x 0%R) (to_m (shn a) A))).
  - (** Tensor: just return itself, with its entries as reals **)
    have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor.
    have := sized t (sub _ win).
    move: (i_sh t tin) => tsh.
    case: t win ac tin tsh => dims [dt|] seg fd i32 sd i64 tn ds rd ed dl dd u64 mp
                              win ac tin tsh /andP [dpos] //.
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
    (** an entry of dtype x as a real **)
    pose to_R : denote (exist _ x xin) -> R :=
      ltac:(case: (x) (xin) => xin';
            first [ exact (fun f : float32 => R_of_float32 f)
                  | exact (fun i : int32 => IZR (Z_of_int32 i))
                  | exact (fun i : int64 => IZR (Z_of_int64 i))
                  | by exfalso; move: xin'; rewrite !inE => /or3P [] /eqP ]).
    suff T : TensorSemantics denote (@tensorType Elem (exist _ x xin) (existT _ (size dims) shape)).
      (** reshape T to the matrix type of t **)
      rewrite /ty /=.
      case Etn: tn tsh => [s|] //= /andP [dc /eqP sh].
      exact: (to_mat s _ shape dims shapeE dc sh (Tensor (map_mx to_R (tensor_val T)))).
    apply: theoryTensorProto.
    exists (qtensor_pi (TensorProto_constructor dims (Some dt) seg fd i32 sd i64 tn
                                                ds rd ed dl dd u64 mp)).
    have Edims : dims = map (tnth (in_tuple dims)) (fintype.enum 'I_(size dims)).
      by rewrite map_tnth_enum.
    case: x E Hsize xin {to_R} => // E Hsize xin;
      [move: (DataType_float E) | move: (DataType_int32 E) | move: (DataType_int64 E)] => Z;
      rewrite /= /storage_of Z /= E eqxx Hsize dpos /= !andbT;
      rewrite -map_comp; apply/eqP;
      rewrite {1}Edims;
      by rewrite -map_comp enumT; apply: eq_map => i /=; rewrite ffunE insubdK //; exact: pos i.
  - (** Input: the user inputs are positional, take the one at v's position **)
    have vin := in_inputs v (sub _ win).
    have ilt : (seq.index v inputs < size inps)%nat by rewrite Hsz index_mem.
    have ilt' : (seq.index v inputs < size inps')%nat by rewrite Hsz'.
    (** network_dim_match: the input at v's position has v's declared type **)
    have vt_ok : value_has_type (tnth (in_tuple inps) (Ordinal ilt)) v.
      move/and4P: dm => [_ _ + _]; rewrite all2E => /andP [_ /all_nthP same].
      have := same (tnth (in_tuple inps) (Ordinal ilt), v) (seq.index v inputs).
      rewrite nth_zip_cond size_zip -Hsz minnn ilt => /(_ isT) /=.
      by rewrite nth_index // -(tnth_nth _ (in_tuple inps) (Ordinal ilt)).
    (** NetworkShapesMatch: the user input at v's position has the same dims **)
    have vt_match : TensorShapesMatch (tnth (in_tuple inps) (Ordinal ilt))
                                      (tnth (in_tuple inps') (Ordinal ilt')).
      move: in_match; rewrite all2E => /andP [_ /all_nthP same].
      have := same (tnth (in_tuple inps) (Ordinal ilt), tnth (in_tuple inps') (Ordinal ilt'))
                   (seq.index v inputs).
      have imin : (seq.index v inputs < minn (size inps) (size inps'))%nat by rewrite Hsz' minnn.
      rewrite nth_zip_cond size_zip imin => /(_ isT) /=.
      by rewrite -(tnth_nth _ (in_tuple inps) (Ordinal ilt))
                 -(tnth_nth _ (in_tuple inps') (Ordinal ilt')).
    move: (inp (Ordinal ilt')) vt_ok vt_match.
    case: (tnth (in_tuple inps') (Ordinal ilt')) => ei' dsi' /= X.
    case: (tnth (in_tuple inps) (Ordinal ilt)) => ei [ki dsi] /= /andP [_ /eqP vdims] /eqP /= Ed.
    move: X; rewrite -Ed /= => X.
    (** reshape X to the matrix type of the input **)
    move: (v_sh v) vdims; rewrite mem_cat vin => /(_ isT).
    rewrite /ty /=.
    case: (value_name v) => [nm|] //=.
    case: (value_dims v) => [l|] //= /andP [dc /eqP sh] [vdims].
    exact: (to_mat nm _ dsi l (esym vdims) dc sh X).
  - (** Output **)
    by move: (sub _ win); rewrite no_output.
(** onnx_evaluator: evaluate the output vertex **)
have := outs_one o oin; rewrite -/(graph_items nodes inputs initialisers) Hv.
case: o oin oname otype => [[nm|] ot od om] oin oname otype //=.
(** model_well_formed: the output names exactly one vertex, a node **)
case F: (find_vertex vertices nm) => [|w [|? ?]] //; last by case: w F.
case: w F => // n F _.
have win := finds_in F.
have ac : acyclic_at vertices (node n).
  by move: (graph_acyclic_at (node n) acyc); rewrite Hv => /(_ win).
have Y := go (size vertices) vertices (node n) erefl win (fun _ x => x) ac.
(** reshape Y to d2: the output's declared dims are d1's, which are d2's, and its
    static shape **)
have Fg : find_vertex (graph_items nodes inputs initialisers) nm = [:: node n] by rewrite Hv.
move: Y; rewrite /ty (graph_sh_find _ _ _ _ _ _ nodes_sh Fg) => Y.
have oin' : ValueInfoProto_constructor (Some nm) ot od om \in (inputs ++ outputs)%SEQ.
  by rewrite mem_cat oin orbT.
set ov := ValueInfoProto_constructor (Some nm) ot od om in oin' otype *.
move: (v_sh _ oin') otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //.
case: (value_dims ov) => [l|] //= /andP [dc /eqP sh] /andP [_ /eqP [odims]].
case: d2 d12 => e2 dims2 /eqP /= Ed; rewrite /= -Ed.
apply: (reshape _ Y).
have /andP [h0 w0] := mat_dims_pos _ dc.
by rewrite (dims_prodE _ _ _ (esym odims) dc) /= /shn sh mat_prod.
Defined.

(* Section RealEvaluator. *)
(* Context (r : realType). *)

(* Local Open Scope ring_scope. *)

(* Local Notation realTensor := *)
(*   {d : TensorType RealElementType & TensorSemantics (@realElementTypeInterp r) d}. *)

(* Context (R_of_float32 : float32 -> r) (IZR : Z -> r). *)

(* Lemma prod_ord0 (f : 'I_0 -> nat) : \prod_(j < 0) f j = 1%nat. *)
(* Proof. by rewrite big_ord0. Qed. *)

(* Lemma prod_ord2 (h w : {posnum nat}) : *)
(*   (h%:num * w%:num)%nat = \prod_(i < 2) ([ffun i => tnth [tuple h; w] i] i)%:num. *)
(* Proof. by rewrite !big_ord_recl big_ord0 !ffunE /= GRing.mulr1. Qed. *)

(* (*tensor-to-matrix: reshape a tensor into an h x w matrix (row-major)*) *)
(* Definition as_matrix (x : realTensor) (h w : nat) : option 'M[r]_(h, w) := *)
(*   match x with *)
(*   | existT (tensorType _ (existT k dims)) t => *)
(*     match \prod_(i < k) (dims i)%:num =P (h * w)%nat with *)
(*     | ReflectT E => Some (vec_mx (castmx (prod_ord0 _, E) (tensor_val t)^T)) *)
(*     | ReflectF _ => None *)
(*     end *)
(*   end. *)

(* (*A' is A, but might be transposed, depending on trans*) *)
(* Definition as_matrix_t (x : realTensor) (trans : bool) (h w : nat) : option 'M[r]_(h, w) := *)
(*   if trans then omap (fun M => M^T) (as_matrix x w h) else as_matrix x h w. *)

(* (*matrix-to-tensor: a rank 2 tensor of shape [h; w]*) *)
(* Definition tensor_of_matrix2 (h w : {posnum nat}) (M : 'M[r]_(h%:num, w%:num)) : realTensor := *)
(*   existT _ (tensorType _ real (existT _ 2%nat [ffun i => tnth [tuple h; w] i])) *)
(*     (Tensor (castmx (prod_ord2 h w, esym (prod_ord0 _)) (mxvec M)^T)). *)

(* (*as convert_dims: scalars are 1x1, vectors 1xn, matrices hxw*) *)
(* Definition matrix_dims (x : realTensor) : option ({posnum nat} * {posnum nat}) := *)
(*   match tag x with *)
(*   | tensorType _ dims => *)
(*     match projT1 dims as k return {posnum nat} ^ k -> _ with *)
(*     | 0%nat => fun _ => Some (1%:posnat, 1%:posnat) *)
(*     | 1%nat => fun d => Some (1%:posnat, d ord0) *)
(*     | 2%nat => fun d => Some (d ord0, d ord_max) *)
(*     | _ => fun _ => None *)
(*     end (projT2 dims) *)
(*   end. *)

(* (*helper for broadcast_2d_real, as broadcast_2d_vector*) *)
(* Definition broadcast_2d_vector_real (h w hC wC : nat) (C : 'M[r]_(hC, wC)) *)
(*   : error_option 'M[r]_(h, w) := *)
(*   match hC =P 1%nat, wC =P w with *)
(*   | ReflectT E1, ReflectT E2 => Success (\matrix_(i, j) (castmx (E1, E2) C) ord0 j) (*C is a row vector*) *)
(*   | ReflectT _, ReflectF _ => Error "Broadcast: Dimension which is not one must match at least one given dimension" *)
(*   | ReflectF _, _ => *)
(*     match hC =P h, wC =P 1%nat with *)
(*     | ReflectT E1, ReflectT E2 => Success (\matrix_(i, j) (castmx (E1, E2) C) i ord0) (*C is a column vector*) *)
(*     | ReflectF _, ReflectT _ => Error "Broadcast: Dimension which is not one must match at least one given dimension" *)
(*     | _, ReflectF _ => Error "Broadcast: Vector matrices must have at least one dimension which is one" *)
(*     end *)
(*   end. *)

(* (*unidirectional broadcasting for two dimensions, as broadcast_2d*) *)
(* Definition broadcast_2d_real (h w : nat) (dims_C : seq nat) (hC wC : nat) (C : 'M[r]_(hC, wC)) *)
(*   : error_option 'M[r]_(h, w) := *)
(*   match dims_C with *)
(*   | [::] => (*C is a scalar*) *)
(*     match hC =P 1%nat, wC =P 1%nat with *)
(*     | ReflectT E1, ReflectT E2 => Success (const_mx ((castmx (E1, E2) C) ord0 ord0)) *)
(*     | _, _ => Error "Broadcast: Scalar matrices must have exactly one element" *)
(*     end *)
(*   | [:: _] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: 1%nat; _] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: _; 1%nat] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: _; _] => (*C is a matrix*) *)
(*     match hC =P h, wC =P w with *)
(*     | ReflectT E1, ReflectT E2 => Success (castmx (E1, E2) C) *)
(*     | _, _ => Error "Broadcast: Matrices must have matching shape" *)
(*     end *)
(*   | _ => Error "Broadcast: Can only broadcast scalars, vectors and matrices" *)
(*   end. *)

(* (* *)
(* Gemm: alpha *: A' *m B' + beta *: C, with C broadcast to the shape of A' *m B'. *)
(* broadcast_C receives that shape. *)
(* *) *)
(* Definition gemm_real (A B : realTensor) (broadcast_C : forall h w : nat, error_option 'M[r]_(h, w)) *)
(*   (a : list AttributeProto) : error_option realTensor := *)
(*   let '(alpha, beta, transA, transB) := get_gemm_attributes a in *)
(*   let tA := if Z_of_int64 transA is Z0 then false else true in *)
(*   let tB := if Z_of_int64 transB is Z0 then false else true in *)
(*   match matrix_dims A, matrix_dims B with *)
(*   | Some (hA, wA), Some (hB, wB) => *)
(*     let '(hA', wA') := if tA then (wA, hA) else (hA, wA) in *)
(*     let '(hB', wB') := if tB then (wB, hB) else (hB, wB) in *)
(*     match as_matrix_t A tA hA'%:num wA'%:num, as_matrix_t B tB hB'%:num wB'%:num with *)
(*     | Some A', Some B' => *)
(*       match wA'%:num =P hB'%:num with *)
(*       | ReflectT E => *)
(*         match broadcast_C hA'%:num wB'%:num with *)
(*         | Success C_b => *)
(*           Success (tensor_of_matrix2 hA' wB' *)
(*             (R_of_float32 alpha *: A' *m castmx (esym E, erefl) B' + R_of_float32 beta *: C_b)) *)
(*         | Error e => Error e *)
(*         end *)
(*       | ReflectF _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)" *)
(*       end *)
(*     | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)" *)
(*     end *)
(*   | _, _ => Error "dims list cannot be longer than two when converting into a matrix" *)
(*   end. *)

(* (*Computes Gemm for three inputs, as gemm*) *)
(* Definition real_gemm (A B C : realTensor) (a : list AttributeProto) : error_option realTensor := *)
(*   match matrix_dims C with *)
(*   | Some (hC, wC) => *)
(*     match as_matrix C hC%:num wC%:num with *)
(*     | Some C' => gemm_real A B (fun h w => broadcast_2d_real h w [:: hC%:num; wC%:num] _ _ C') a *)
(*     | None => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)" *)
(*     end *)
(*   | None => Error "dims list cannot be longer than two when converting into a matrix" *)
(*   end. *)

(* (*Computes Gemm for two inputs, as gemm_two_inputs: C is the 1x1 zero matrix*) *)
(* Definition real_gemm_two_inputs (A B : realTensor) (a : list AttributeProto) : error_option realTensor := *)
(*   gemm_real A B (fun h w => broadcast_2d_real h w [::] _ _ (0 : 'M[r]_(1, 1))) a. *)

(* (*Computes ReLU, as relu*) *)
(* Definition relu_tensor (d : TensorType RealElementType) *)
(*   : TensorSemantics (@realElementTypeInterp r) d -> TensorSemantics (@realElementTypeInterp r) d := *)
(*   match d as d return TensorSemantics _ d -> TensorSemantics _ d with *)
(*   | tensorType _ dims => fun t => Tensor (map_mx (fun x => Num.max x 0) (tensor_val t)) *)
(*   end. *)

(* Definition real_relu (X : realTensor) : error_option realTensor := *)
(*   Success (existT _ (tag X) (relu_tensor (tag X) (tagged X))). *)

(* (*initializers: the data of a TensorProto as reals, read as matrix_float32_of_tensor does*) *)
(* Definition real_data_of_tensor (t : TensorProto) : error_option (seq r) := *)
(*   match t with *)
(*   | TensorProto_constructor _ (Some data_type) _ float32_data int32_data _ int64_data _ _ raw_data _ _ _ _ _ => *)
(*     match Z_of_int32 data_type with *)
(*     | 1%Z => (*float32*) *)
(*       match float32_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match float32_of_bytes bytes with *)
(*           | Success floats => Success (map R_of_float32 floats) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type float32 must either have non-empty float_data or non-empty raw_data" *)
(*         end *)
(*       | floats => Success (map R_of_float32 floats) *)
(*       end *)
(*     | 6%Z => (*int32*) *)
(*       match int32_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match int32_of_bytes bytes with *)
(*           | Success ints => Success (map (fun i => IZR (Z_of_int32 i)) ints) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type int32 must either have non-empty int32_data or non-empty raw_data" *)
(*         end *)
(*       | ints => Success (map (fun i => IZR (Z_of_int32 i)) ints) *)
(*       end *)
(*     | 7%Z => (*int64*) *)
(*       match int64_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match int64_of_bytes bytes with *)
(*           | Success ints => Success (map (fun i => IZR (Z_of_int64 i)) ints) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type int64 must either have non-empty int64_data or non-empty raw_data" *)
(*         end *)
(*       | ints => Success (map (fun i => IZR (Z_of_int64 i)) ints) *)
(*       end *)
(*     | _ => Error "Tensor Datatype must either be float32, int32 or int64" *)
(*     end *)
(*   | _ => Error "Tensor must have a given Datatype" *)
(*   end. *)

(* Definition real_of_tensorproto (t : TensorProto) : error_option realTensor := *)
(*   match t, real_data_of_tensor t with *)
(*   | TensorProto_constructor dims _ _ _ _ _ _ _ _ _ _ _ _ _ _, Success data => *)
(*     let ds := map int64_to_dim dims in *)
(*     let pdims : seq {posnum nat} := pmap insub ds in *)
(*     if size pdims == size ds then *)
(*       let fdims : {posnum nat} ^ (size pdims) := [ffun i => tnth (in_tuple pdims) i] in *)
(*       match size data =P \prod_(i < size pdims) (fdims i)%:num with *)
(*       | ReflectT E => Success (existT _ (tensorType _ real (existT _ _ fdims)) (build_tensor fdims data E)) *)
(*       | ReflectF _ => Error "TensorProto data does not match its dims" *)
(*       end *)
(*     else Error "dim cannot be zero or negative" *)
(*   | _, Error e => Error e *)
(*   end. *)

(* (* *)
(* Recursive implementation of the real valued onnx_evaluator, case by case as *)
(* onnx_evaluator_recursive: *)
(*   - Node:    Check op_type, evaluate all input vertices and compute if possible *)
(*   - Tensor:  Return itself *)
(*   - Input:   Search in user inputs for tensor with same name, if exactly one found: return it *)
(*   - Output:  Search in vertices for vertex with same name, if exactly one found: evaluate it *)
(* *) *)
(* Fixpoint real_onnx_evaluator_recursive (depth : nat) (user_inputs : seq (string * realTensor)) *)
(*   (vertices : list vertex) (evaluate : vertex) : error_option realTensor := *)
(*   match depth with *)
(*   | O => Error "ONNX Evaluator: Run out of vertices. Maybe a circular dependency, a missing vertex, or the list of nodes is not sorted topologically" *)
(*   | S n => (*check the type of the vertex to be evaluated*) *)
(*     match evaluate with *)
(*     (*Node: check op_type and compute it if possible*) *)
(*     | node (NodeProto_constructor node_inputs node_outputs _ op_type _ _ attributes _ _ _) => match op_type with *)
(*       | Some s => *)
(*         if String.eqb s """Gemm""" then *)
(*           match node_inputs with (*check input amount*) *)
(*           | [:: node_input_A; node_input_B; node_input_C] => (*three inputs*) *)
(*             match find_vertex vertices node_input_A, find_vertex vertices node_input_B, find_vertex vertices node_input_C with *)
(*             | [:: vertex_A], [:: vertex_B], [:: vertex_C] => (*evaluate each vertex and compute gemm*) *)
(*               match *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_A, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_B, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_C *)
(*               with *)
(*               | Success A, Success B, Success C => real_gemm A B C attributes *)
(*               | Error e, _, _ => Error e *)
(*               | _, Error e, _ => Error e *)
(*               | _, _, Error e => Error e *)
(*               end *)
(*             | _, _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ *)
(*                         node_input_A ++ " or " ++ node_input_B ++ " or " ++ node_input_C)%string *)
(*             end *)
(*           | [:: node_input_A; node_input_B] => (*two inputs*) *)
(*             match find_vertex vertices node_input_A, find_vertex vertices node_input_B with *)
(*             | [:: vertex_A], [:: vertex_B] => (*evaluate each vertex and compute gemm*) *)
(*               match *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_A, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_B *)
(*               with *)
(*               | Success A, Success B => real_gemm_two_inputs A B attributes *)
(*               | Error e, _ => Error e *)
(*               | _, Error e => Error e *)
(*               end *)
(*             | _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ *)
(*                         node_input_A ++ " or " ++ node_input_B)%string *)
(*             end *)
(*           | _ => Error "Gemm must have 2-3 inputs" *)
(*           end *)
(*         else *)
(*         if String.eqb s """Relu""" then *)
(*           match node_inputs with (*check input amount*) *)
(*           | [:: node_input_name] => *)
(*             match find_vertex vertices node_input_name with *)
(*             | [:: vertex] => *)
(*               match real_onnx_evaluator_recursive n user_inputs vertices vertex with *)
(*               | Success rec => real_relu rec *)
(*               | Error e => Error e *)
(*               end *)
(*             | _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ node_input_name)%string *)
(*             end *)
(*           | _ => Error "Relu must have exactly one input" *)
(*           end *)
(*         else Error ("ONNX Evaluator: op_type of NodeProto must be a valid, implemented operation, not " ++ s)%string *)
(*       | None => Error "ONNX Evaluator: op_type of NodeProto must be non-empty" *)
(*       end *)

(*     (*Tensor: just return itself*) *)
(*     | tensor t => real_of_tensorproto t *)

(*     (*Input: search in user_inputs for tensor with same name, if exactly one found: return it*) *)
(*     | input (ValueInfoProto_constructor name_option _ _ _) => *)
(*       match name_option with *)
(*       | Some name => match filter (fun x => String.eqb name x.1) user_inputs with *)
(*         | [:: user_input] => Success user_input.2 *)
(*         | _ => Error ("ONNX Evaluator: not exactly one user input given for input vertex: " ++ name)%string *)
(*         end *)
(*       | None => Error "ONNX Evaluator: Input Vertex must define name" *)
(*       end *)

(*     (*Output: search in vertices for vertex with same name, if exactly one found: evaluate it*) *)
(*     | output (ValueInfoProto_constructor name_option _ _ _) => *)
(*       match name_option with *)
(*       | Some name => match filter (vertex_has_name name) vertices with *)
(*         | [:: v] => real_onnx_evaluator_recursive n user_inputs vertices v *)
(*         | _ => Error ("ONNX Evaluator: not exaclty one vertex (node, initializer or input) found: " ++ name)%string *)
(*         end *)
(*       | None => Error "ONNX Evaluator: Output Vertex must define name" *)
(*       end *)

(*     end *)
(*   end. *)

(* (*the computational graph, as built in onnx_evaluator*) *)
(* Definition graph_vertices (graph : GraphProto) : list vertex := *)
(*   match graph with *)
(*   | GraphProto_constructor nodes _ initializers _ _ inputs _ _ _ _ => *)
(*     map node (rev nodes) ++ map input inputs ++ map tensor initializers *)
(*   end. *)

(* (*Calls the recursive implementation of the real onnx_evaluator on a model's graph*) *)
(* Definition real_onnx_evaluator (model : ModelProto) (user_inputs : seq (string * realTensor)) *)
(*   : error_option (list realTensor) := *)
(*   match graph_of model with *)
(*   | Some graph => *)
(*     let vertices := graph_vertices graph in *)
(*     let evaluate := real_onnx_evaluator_recursive (size vertices) user_inputs vertices in *)
(*     let output_vertices := map output (graph_outputs model) in *)
(*     list_error_option_to_error_option_list (map evaluate output_vertices) [::] *)
(*   | None => Error "ONNX Evaluator: Model must define a graph" *)
(*   end. *)

(* (*the InputSemantics, named after the model's graph inputs*) *)
(* Definition real_user_inputs (graph_ins : seq ValueInfoProto) (y : NetworkType RealElementType) *)
(*   : InputSemantics (@realElementTypeInterp r) y -> seq (string * realTensor) := *)
(*   match y as y return InputSemantics (@realElementTypeInterp r) y -> seq (string * realTensor) with *)
(*   | networkType ins _ => fun inp => *)
(*     [seq (value_info_name (nth emptyValueInfoProto graph_ins i), existT _ _ (inp i)) *)
(*     | i : 'I_(size ins) <- fintype.enum 'I_(size ins)] *)
(*   end. *)

(* (*the evaluator's result at type d; errors and shape mismatches give 0*) *)
(* Definition real_result (d : TensorType RealElementType) (t : error_option realTensor) *)
(*   : TensorSemantics (@realElementTypeInterp r) d := *)
(*   match d as d return TensorSemantics (@realElementTypeInterp r) d with *)
(*   | tensorType _ dims => *)
(*     match t with *)
(*     | Success (existT (tensorType _ dims') t) => *)
(*       match dims' =P dims with *)
(*       | ReflectT E => rew [fun ds => 'nT[r]_(projT2 ds)] E in t *)
(*       | ReflectF _ => const_t 0 *)
(*       end *)
(*     | Error _ => const_t 0 *)
(*     end *)
(*   end. *)

(* End RealEvaluator. *)

(* From Stdlib Require Import Rdefinitions. *)
(* Definition R_of_float32 (f : float32) : R := Binary.B2R 24 128 f. *)

(* (* *)
(* Executes the network over R: the semantic inputs are named after the *)
(* model's graph inputs, and the requested node output is evaluated by *)
(* real_onnx_evaluator_recursive as onnx_evaluator evaluates an output vertex. *)
(* *) *)
(* Definition realSemantics : (@RealNetworkSemantics syntax_inst R) := *)
(*   fun y1 y2 d1 d2 u m _ inp out _ => *)
(*   match m as m return NodeOutput syntax_inst m u d1 -> _ with *)
(*   | exist model _ => fun out => *)
(*     let user_inputs := real_user_inputs R (graph_inputs model) y2 inp in *)
(*     match graph_of model with *)
(*     | Some graph => *)
(*       let vertices := graph_vertices graph in *)
(*       real_result R d2 (real_onnx_evaluator_recursive R R_of_float32 IZR (size vertices) user_inputs vertices (output (val out))) *)
(*     | None => real_result R d2 (Error "ONNX Evaluator: Model must define a graph") *)
(*     end *)
(*   end out. *)
