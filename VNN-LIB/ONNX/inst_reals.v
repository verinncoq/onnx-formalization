Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.

From Stdlib Require Import Rdefinitions.
From mathcomp Require Import boot algebra order reals Rstruct finmap.
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

(** * The real semantics of a model

    This is [interp_model] of inst_sem with every element type fixed to R and
    the operations those of mathcomp: the values of the names of the graph are
    tensors over R, an initialiser is read entry by entry as a real, Gemm is
    [alpha *: (A' *m B') + beta *: C] and Relu is [Num.max x 0] on every
    entry.  The semantic inputs are those of the real network type, in the
    order of the graph inputs, and the value of the requested output is read
    at the real tensor type the query gives it. *)

(** ** Values *)

(** The dims of a value, as a list. *)
Definition shapeR (v : T R) : seq nat :=
  map (fun q : {posnum nat} => q%:num) (tval (projT1 (projT2 v))).

(** A float, and an element of a supported type, as a real. *)
Definition R_of_float32 (f : float32) : R := Binary.B2R 24 128 f.

Definition real_of_elem (x : Elem) : denote x -> R :=
  match x as x0 return denote x0 -> R with
  | exist FLOAT_TensorProto _ => R_of_float32
  | exist INT32_TensorProto _ => fun i => IZR (Z_of_int32 i)
  | exist INT64_TensorProto _ => fun i => IZR (Z_of_int64 i)
  | exist _ Hx => False_rect _ (notF Hx)
  end.

(** A value of a supported element type as a real value of the same shape. *)
Definition real_value (v : {x : Elem & T (denote x)}) : T R :=
  existT (fun k => {us : {posnum nat} ^ k & 'nT[R]_(us)}) (projT1 (projT2 v))
    (existT (fun us => 'nT[R]_(us)) (projT1 (projT2 (projT2 v)))
       (Tensor (map_mx (real_of_elem (projT1 v)) (tensor_val (projT2 (projT2 (projT2 v))))))).

Lemma shapeR_real_value v : shapeR (real_value v) = shape_dims v.
Proof. by []. Qed.

(** A tensor of a real tensor type as a value, and its dims. *)
Definition tensor_value (d : TensorType RealElementType) :
  TensorSemantics (@realElementTypeInterp R) d -> T R :=
  match d as d0 return TensorSemantics (@realElementTypeInterp R) d0 -> T R with
  | tensorType _ dims => fun x =>
      existT (fun k => {us : {posnum nat} ^ k & 'nT[R]_(us)}) (projT1 dims)
        (existT (fun us => 'nT[R]_(us)) (projT2 dims) x)
  end.

Lemma shapeR_tensor_value d x :
  shapeR (tensor_value d x)
  = map (fun q : {posnum nat} => q%:num) (tval (projT2 (tensorDims _ d))).
Proof. by case: d x. Qed.

(** A value of the dims of a real tensor type, as a tensor of that type. *)
Definition value_tensor (d : TensorType RealElementType) (v : T R) :
  existT (fun k : nat => {ffun 'I_k -> {posnum nat}}) (projT1 v) (projT1 (projT2 v)) = tensorDims _ d ->
  TensorSemantics (@realElementTypeInterp R) d :=
  match d as d0 return
    existT (fun k : nat => {ffun 'I_k -> {posnum nat}}) (projT1 v) (projT1 (projT2 v)) = tensorDims _ d0 ->
    TensorSemantics (@realElementTypeInterp R) d0
  with
  | tensorType _ dims => fun E => ecast p ('nT[R]_(projT2 p)) E (projT2 (projT2 v))
  end.

(** The rank of a value is the length of its dims. *)
Lemma shapeR_rank (v : T R) : size (shapeR v) = projT1 v.
Proof. by rewrite /shapeR size_map size_tuple. Qed.

(** The dims Gemm reads a value of rank at most 2 with, transposed. *)
Lemma trans_gemm_shapeRE t (v : T R) : (size (shapeR v) <= 2)%nat ->
  let s := gemm_shape (projT1 (projT2 v)) in
  ((trans_shape t (s.1, s.2)).1%:num, (trans_shape t (s.1, s.2)).2%:num)
  = trans_dims t (mat_of_dims (shapeR v)).
Proof. by rewrite shapeR_rank => rk /=; rewrite trans_shapeE /= gemm_shapeE. Qed.

(** ** The maps of the initialisers and of the inputs *)

(** The named, sized tensors of a sequence as real values, by name. *)
Fixpoint inits_fmapR (s : seq TensorProto) :
  all (fun t => tensorNamed t && tensorProtoSized t) s -> {fmap string -> T R} :=
  match s with
  | [::] => fun _ => [fmap]
  | t :: s' => fun H =>
      (inits_fmapR s' (andP H).2).[init_name t (andP (andP H).1).1 <-
                                   real_value (tensorProto_elem t (andP (andP H).1).2)]
  end.

(** gamma with the value at every position of vs added under the name of the
    declaration at that position. *)
Definition inputs_fmapR {vs : seq ValueInfoProto}
  (Hn : forall i : 'I_(size vs), value_named (tnth (in_tuple vs) i))
  (xs : 'I_(size vs) -> T R) (gamma : {fmap string -> T R}) : {fmap string -> T R} :=
  foldr (fun i gamma => gamma.[input_name _ (Hn i) <- xs i]) gamma (ord_enum (size vs)).

Lemma inits_fmapR_dom s H t nm :
  t \in s -> tensor_name t = Some nm -> nm \in domf (inits_fmapR s H).
Proof.
elim: s H => //= t' s IH H.
rewrite inE in_fsetU in_fset1 => /orP [/eqP -> tnm | tin tnm]; last by rewrite (IH _ tin tnm) orbT.
by rewrite (init_nameP _ tnm) eqxx.
Qed.

Lemma inputs_fmapR_sub vs Hn xs gamma :
  (domf gamma `<=` domf (@inputs_fmapR vs Hn xs gamma))%fset.
Proof.
rewrite /inputs_fmapR; elim: (ord_enum _) => //= i l IH.
exact: fsubset_trans IH (fsubsetUr _ _).
Qed.

Lemma inputs_fmapR_dom vs Hn xs gamma v nm :
  v \in vs -> value_name v = Some nm -> nm \in domf (@inputs_fmapR vs Hn xs gamma).
Proof.
move=> /(tnthP (in_tuple vs)) [i ->] vnm.
rewrite -(input_nameP (Hn i) vnm) /inputs_fmapR.
have := mem_ord_enum i; elim: (ord_enum _) => //= j l IH.
rewrite inE in_fsetU in_fset1 => /orP [/eqP -> | /IH ->]; first by rewrite eqxx.
by rewrite orbT.
Qed.

Lemma inits_fmapR_fnd s H nm v :
  (inits_fmapR s H).[? nm] = Some v ->
  exists t : TensorProto,
    [/\ t \in s, tensor_name t = Some nm & exists Ht, v = real_value (tensorProto_elem t Ht)].
Proof.
elim: s H => [|t s IH] H /=; first by rewrite fnd_fmap0.
rewrite fnd_set; case: ifP => [/eqP -> [<-] | _ /IH [t' [tin tnm [Ht ->]]]].
- by exists t; split; [exact: mem_head | exact: init_nameE | exists (andP (andP H).1).2].
- by exists t'; split; [rewrite in_cons tin orbT | exact: tnm | exists Ht].
Qed.

Lemma inputs_fmapR_fnd vs Hn xs gamma nm v :
  (@inputs_fmapR vs Hn xs gamma).[? nm] = Some v ->
  (exists i, value_name (tnth (in_tuple vs) i) = Some nm /\ v = xs i) \/ gamma.[? nm] = Some v.
Proof.
rewrite /inputs_fmapR; elim: (ord_enum _) => [|i l IH] /=; first by right.
rewrite fnd_set; case: ifP => [/eqP -> [<-] | _ /IH //].
by left; exists i; split => //; exact: input_nameE.
Qed.

(** ** The value of a node *)

(** The value of a Gemm node on the values of its inputs, read as real
    matrices with the inner dims of A' and B' equal:
    [alpha *: (A' *m B') + beta *: C], with C broadcast to the result. *)
Definition interp_gemmR (A B : M2 R) (C : option (M2 R)) (attribs : seq AttributeProto)
  (Hk : (trans_shape (gemm_transB attribs) (projT1 B, projT1 (projT2 B))).1%:num
        = (trans_shape (gemm_transA attribs) (projT1 A, projT1 (projT2 A))).2%:num)
  : T R :=
  let alpha := R_of_float32 (gemm_alpha attribs) in
  let beta := R_of_float32 (gemm_beta attribs) in
  let A' := trans_mx (gemm_transA attribs) (matrix_of_ntensor (projT2 (projT2 A))) in
  let B' := castmx (Hk, erefl) (trans_mx (gemm_transB attribs) (matrix_of_ntensor (projT2 (projT2 B)))) in
  match C with
  | Some C => tensor_of_mx (alpha *: (A' *m B')
                            + beta *: bcast_mx (matrix_of_ntensor (projT2 (projT2 C))))%R
  | None => tensor_of_mx (alpha *: (A' *m B'))%R
  end.

(** The value of a Relu node on the value of its input: [Num.max x 0] on
    every entry.  Any rank. *)
Definition interp_reluR (A : T R) : T R :=
  existT (fun k => {us : {posnum nat} ^ k & 'nT[R]_(us)}) (projT1 A)
    (existT (fun us => 'nT[R]_(us)) (projT1 (projT2 A))
       (Tensor (map_mx (fun x : R => Num.max x 0%R) (tensor_val (projT2 (projT2 A)))))).

(** gamma with v bound to every name in outs. *)
Definition bind_outputsR (gamma : {fmap string -> T R}) (outs : seq string) (v : T R) :
  {fmap string -> T R} :=
  foldr (fun o gamma => gamma.[o <- v]) gamma outs.

(** What interp_gemmR needs of the values a, b and c of a Gemm node's inputs:
    a and b of rank at most 2, the inner dims of A' and B' equal, and c, if
    any, of rank at most 2. *)
Record gemm_valuesR_ok (a b : T R) (c : option (T R)) (attribs : seq AttributeProto) : Prop :=
  GemmValuesROk {
    gemmR_rank_a : (projT1 a <= 2)%nat;
    gemmR_rank_b : (projT1 b <= 2)%nat;
    gemmR_inner :
      let sa := gemm_shape (projT1 (projT2 a)) in
      let sb := gemm_shape (projT1 (projT2 b)) in
      (trans_shape (gemm_transB attribs) (sb.1, sb.2)).1%:num
      = (trans_shape (gemm_transA attribs) (sa.1, sa.2)).2%:num;
    gemmR_c : if c is Some c then (projT1 c <= 2)%nat else true
  }.

Arguments gemmR_rank_a {a b c attribs}.
Arguments gemmR_rank_b {a b c attribs}.
Arguments gemmR_inner {a b c attribs}.
Arguments gemmR_c {a b c attribs}.

(** The facts above for the values of the inputs of n in gamma. *)
Definition node_valuesR_ok (gamma : {fmap string -> T R}) (n : NodeProto) : Prop :=
  match n with
  | NodeProto_constructor [:: A; B] _ _ _ _ _ attribs _ _ _ =>
      forall (HA : A \in domf gamma) (HB : B \in domf gamma),
        gemm_valuesR_ok gamma.[HA] gamma.[HB] None attribs
  | NodeProto_constructor [:: A; B; C] _ _ _ _ _ attribs _ _ _ =>
      forall (HA : A \in domf gamma) (HB : B \in domf gamma) (HC : C \in domf gamma),
        gemm_valuesR_ok gamma.[HA] gamma.[HB] (Some gamma.[HC]) attribs
  | _ => True
  end.

(** gamma with the outputs of the node n bound to its value. The node is a
    supported operation of the right arity, gamma has all its inputs, and
    their values are as a Gemm needs. *)
Definition interp_nodeR (gamma : {fmap string -> T R}) (n : NodeProto) (Hv : valid_op n)
  (Hin : all (fun i => i \in domf gamma) (node_inputs n)) (Hok : node_valuesR_ok gamma n)
  : {fmap string -> T R} :=
match n as n0 return
  valid_op n0 -> all (fun i => i \in domf gamma) (node_inputs n0) -> node_valuesR_ok gamma n0 ->
  {fmap string -> T R}
with
| NodeProto_constructor inps outs nm (Some op) dom ov attribs doc meta dev => fun Hv Hin Hok =>
    match (op =? """Gemm""")%string as g return
      (if g then (size inps == 2%nat) || (size inps == 3%nat)
       else if (op =? """Relu""")%string then size inps == 1%nat else false) -> {fmap string -> T R}
    with
    | true => fun Hv =>
      match inps as l return
        (size l == 2%nat) || (size l == 3%nat) -> all (fun i => i \in domf gamma) l ->
        node_valuesR_ok gamma (NodeProto_constructor l outs nm (Some op) dom ov attribs doc meta dev) ->
        {fmap string -> T R}
      with
      | [:: A; B] => fun _ Hin Hok =>
          let HA := (andP Hin).1 in
          let HB := (andP (andP Hin).2).1 in
          let a := gamma.[HA] in
          let b := gamma.[HB] in
          let ok := Hok HA HB in
          bind_outputsR gamma outs
            (interp_gemmR (bcast2 a (gemmR_rank_a ok)) (bcast2 b (gemmR_rank_b ok))
               None attribs (gemmR_inner ok))
      | [:: A; B; C] => fun _ Hin Hok =>
          let HA := (andP Hin).1 in
          let HB := (andP (andP Hin).2).1 in
          let HC := (andP (andP (andP Hin).2).2).1 in
          let a := gamma.[HA] in
          let b := gamma.[HB] in
          let c := gamma.[HC] in
          let ok := Hok HA HB HC in
          bind_outputsR gamma outs
            (interp_gemmR (bcast2 a (gemmR_rank_a ok)) (bcast2 b (gemmR_rank_b ok))
               (Some (bcast2 c (gemmR_c ok))) attribs (gemmR_inner ok))
      | [::] => fun Hv _ _ => False_rect _ (notF Hv)
      | [:: _] => fun Hv _ _ => False_rect _ (notF Hv)
      | [:: _, _, _, _ & _] => fun Hv _ _ => False_rect _ (notF Hv)
      end Hv Hin Hok
    | false => fun Hv =>
      match (op =? """Relu""")%string as r return
        (if r then size inps == 1%nat else false) -> {fmap string -> T R}
      with
      | true => fun Hv =>
        match inps as l return
          size l == 1%nat -> all (fun i => i \in domf gamma) l -> {fmap string -> T R}
        with
        | [:: A] => fun _ Hin => bind_outputsR gamma outs (interp_reluR gamma.[(andP Hin).1])
        | [::] => fun Hv _ => False_rect _ (notF Hv)
        | [:: _, _ & _] => fun Hv _ => False_rect _ (notF Hv)
        end Hv Hin
      | false => fun Hv => False_rect _ (notF Hv)
      end Hv
    end Hv
| NodeProto_constructor _ _ _ None _ _ _ _ _ _ => fun Hv _ _ => False_rect _ (notF Hv)
end Hv Hin Hok.

(** ** The invariant *)

(** gamma binds every defined name to a value with the dims shn gives the
    name. *)
Definition gammaR_ok (shn : string -> option (seq nat)) (defined : seq string)
  (gamma : {fmap string -> T R}) : Prop :=
  forall s, s \in defined -> exists Hs : s \in domf gamma, shn s = Some (shapeR gamma.[Hs]).

Lemma gammaR_ok_mem {shn defined gamma} s :
  gammaR_ok shn defined gamma -> s \in defined -> s \in domf gamma.
Proof. by move=> ok /ok [Hs _]. Qed.

Lemma gammaR_ok_get {shn defined gamma} s (Hs : s \in domf gamma) :
  gammaR_ok shn defined gamma -> s \in defined -> shn s = Some (shapeR gamma.[Hs]).
Proof. by move=> ok /ok [Hs']; rewrite (bool_irrelevance Hs' Hs). Qed.

(** The inputs of a node whose inputs are defined are in gamma. *)
Lemma gammaR_ok_inputs {shn defined gamma} (n : NodeProto) :
  gammaR_ok shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  all (fun i => i \in domf gamma) (node_inputs n).
Proof. by move=> ok /allP H; apply/allP => i /H /ok [Hi _]. Qed.

(** Values whose dims Gemm accepts are as a Gemm needs. *)
Lemma gemm_valuesR_okP attrs (a b : T R) c ds :
  gemm_out_dims attrs (shapeR a) (shapeR b) (omap shapeR c) = Some ds ->
  gemm_valuesR_ok a b c attrs.
Proof.
move=> /gemm_out_dimsP.
have tAE := trans_gemm_shapeRE (gemm_transA attrs) a.
have tBE := trans_gemm_shapeRE (gemm_transB attrs) b.
move: tAE tBE; rewrite /gemm_transA /gemm_transB.
case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] /= tAE tBE [ra rb kk _ cok].
split.
- by rewrite -shapeR_rank.
- by rewrite -shapeR_rank.
- by move: kk; rewrite -(tAE ra) -(tBE rb) /gemm_transA /gemm_transB E /= => ->.
- case: c cok => [c|] //=; case: (mat_of_dims _) => h w /andP [rc _].
  by rewrite -shapeR_rank.
Qed.

(** The values of the inputs of a well typed node are as a Gemm needs. *)
Lemma node_valuesR_okP {shn defined gamma} (n : NodeProto) :
  gammaR_ok shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  node_dims_ok shn n -> node_valuesR_ok gamma n.
Proof.
move=> ok.
case: n => [[|A [|B [|C [|? ?]]]] outs nm [s|] dom ov attrs doc meta dev] //=.
- move=> /and3P [Ain Bin _]; rewrite /node_dims_ok /node_out_dims.
  case: ifP => _; last by case: ifP.
  case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //.
  case G: (gemm_out_dims _ _ _ _) => [ds|] // _ HA HB.
  have sa := gammaR_ok_get A HA ok Ain; have sb := gammaR_ok_get B HB ok Bin.
  apply: (@gemm_valuesR_okP attrs _ _ None ds).
  by move: sa sb; rewrite EA EB => -[<-] [<-].
- move=> /and4P [Ain Bin Cin _]; rewrite /node_dims_ok /node_out_dims.
  case: ifP => _; last by case: ifP.
  case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //; case EC: (shn C) => [dc|] //.
  case G: (gemm_out_dims _ _ _ _) => [ds|] // _ HA HB HC.
  have sa := gammaR_ok_get A HA ok Ain; have sb := gammaR_ok_get B HB ok Bin.
  have sc := gammaR_ok_get C HC ok Cin.
  apply: (@gemm_valuesR_okP attrs _ _ (Some _) ds).
  by move: sa sb sc; rewrite EA EB EC /= => -[<-] [<-] [<-].
Qed.

(** The names and values of gamma with v bound to outs. *)
Lemma bind_outputsR_dom gamma outs v s :
  s \in domf (bind_outputsR gamma outs v) = (s \in outs) || (s \in domf gamma).
Proof. by elim: outs => //= o outs IH; rewrite in_fsetU in_fset1 IH inE orbA. Qed.

Lemma bind_outputsR_fnd gamma outs v s :
  (bind_outputsR gamma outs v).[? s] = if s \in outs then Some v else gamma.[? s].
Proof. by elim: outs => //= o outs IH; rewrite fnd_set inE IH; case: eqP. Qed.

(** Binding a value to names that have its dims keeps the invariant. *)
Lemma bind_outputsR_ok {shn defined gamma} outs (v : T R) :
  gammaR_ok shn defined gamma -> all (fun o => shn o == Some (shapeR v)) outs ->
  gammaR_ok shn (outs ++ defined)%SEQ (bind_outputsR gamma outs v).
Proof.
move=> ok /allP Hsh s; rewrite mem_cat => sin.
have Hs : s \in domf (bind_outputsR gamma outs v).
  by rewrite bind_outputsR_dom; case/orP: sin => [-> //|/ok [Hs' _]]; rewrite Hs' orbT.
exists Hs; have := in_fnd Hs; rewrite bind_outputsR_fnd.
case: ifP sin => [so _ [<-] | _ /= sd]; first exact/eqP/Hsh.
by case: (ok s sd) => Hs' E; rewrite in_fnd => -[<-].
Qed.

(** The dims of a real matrix as a tensor, and of the value of a Gemm: the
    rows of A' and the columns of B'. *)
Lemma shapeR_tensor_of_mx (n m : {posnum nat}) (M : 'M[R]_(n%:num, m%:num)) :
  shapeR (tensor_of_mx M) = [:: n%:num; m%:num].
Proof.
rewrite /shapeR.
change (map (fun q : {posnum nat} => q%:num)
          (tval (tuple_of_finfun (finfun_of_tuple [tuple n; m]))) = [:: n%:num; m%:num]).
by rewrite finfun_of_tupleK.
Qed.

Lemma shapeR_interp_gemmR A B C attribs Hk :
  shapeR (interp_gemmR A B C attribs Hk)
  = [:: (trans_shape (gemm_transA attribs) (projT1 A, projT1 (projT2 A))).1%:num;
        (trans_shape (gemm_transB attribs) (projT1 B, projT1 (projT2 B))).2%:num].
Proof. by rewrite /interp_gemmR; case: C => [C|]; exact: shapeR_tensor_of_mx. Qed.

(** The node's outputs get the dims shn gives them, and the defined names
    keep their values. *)
Lemma interp_nodeR_ok {shn defined gamma} (n : NodeProto) Hv Hin Hok :
  gammaR_ok shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  node_dims_ok shn n ->
  gammaR_ok shn (node_outputs n ++ defined)%SEQ (interp_nodeR gamma n Hv Hin Hok).
Proof.
move=> ok.
case: n Hv Hin Hok => inps outs nm [s|] dom ov attrs doc meta dev // Hv Hin Hok.
rewrite /node_dims_ok /node_out_dims [node_inputs _]/= [node_outputs _]/=.
case Eg: (s =? """Gemm""")%string; last case Er: (s =? """Relu""")%string => //.
- move/String.eqb_eq: Eg Hv Hin Hok => -> {s}.
  case: inps => [|A [|B [|C [|? ?]]]] // Hv Hin Hok.
  + move=> /and3P [Ain Bin _].
    case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //.
    case G: (gemm_out_dims _ _ _ _) => [ds|] // /andP [_ Hsh].
    have sa := gammaR_ok_get A (andP Hin).1 ok Ain.
    have sb := gammaR_ok_get B (andP (andP Hin).2).1 ok Bin.
    have daE : da = shapeR gamma.[(andP Hin).1] by move: sa; rewrite EA => -[].
    have dbE : db = shapeR gamma.[(andP (andP Hin).2).1] by move: sb; rewrite EB => -[].
    move: G; rewrite daE dbE => /gemm_out_dimsP; case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] [ra rb _ dsE _].
    have tAE := congr1 fst (trans_gemm_shapeRE tA gamma.[(andP Hin).1] ra).
    have tBE := congr1 snd (trans_gemm_shapeRE tB gamma.[(andP (andP Hin).2).1] rb).
    apply: bind_outputsR_ok => //.
    rewrite shapeR_interp_gemmR.
    by move: Hsh; rewrite dsE -tAE -tBE /gemm_transA /gemm_transB E.
  + move=> /and4P [Ain Bin _ _].
    case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //; case EC: (shn C) => [dc|] //.
    case G: (gemm_out_dims _ _ _ _) => [ds|] // /andP [_ Hsh].
    have sa := gammaR_ok_get A (andP Hin).1 ok Ain.
    have sb := gammaR_ok_get B (andP (andP Hin).2).1 ok Bin.
    have daE : da = shapeR gamma.[(andP Hin).1] by move: sa; rewrite EA => -[].
    have dbE : db = shapeR gamma.[(andP (andP Hin).2).1] by move: sb; rewrite EB => -[].
    move: G; rewrite daE dbE => /gemm_out_dimsP; case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] [ra rb _ dsE _].
    have tAE := congr1 fst (trans_gemm_shapeRE tA gamma.[(andP Hin).1] ra).
    have tBE := congr1 snd (trans_gemm_shapeRE tB gamma.[(andP (andP Hin).2).1] rb).
    apply: bind_outputsR_ok => //.
    rewrite shapeR_interp_gemmR.
    by move: Hsh; rewrite dsE -tAE -tBE /gemm_transA /gemm_transB E.
- move/String.eqb_eq: Er Hv Hin Hok => -> {s Eg}.
  case: inps => [|A [|? ?]] // Hv Hin Hok /andP [Ain _].
  case EA: (shn A) => [da|] // /andP [_ Hsh].
  have sa := gammaR_ok_get A (andP Hin).1 ok Ain.
  apply: bind_outputsR_ok => //.
  by move: sa Hsh; rewrite EA => -[->].
Qed.

(** gamma with the values of the nodes, in list order, which [topo_sorted]
    makes a topological order. *)
Fixpoint interp_nodesR (shn : string -> option (seq nat)) (defined : seq string)
  (gamma : {fmap string -> T R}) (nodes : seq NodeProto) :
  topo_sorted defined nodes -> all (node_dims_ok shn) nodes -> gammaR_ok shn defined gamma ->
  {g : {fmap string -> T R} | gammaR_ok shn (defined_after defined nodes) g} :=
  match nodes as ns return
    topo_sorted defined ns -> all (node_dims_ok shn) ns -> gammaR_ok shn defined gamma ->
    {g : {fmap string -> T R} | gammaR_ok shn (defined_after defined ns) g}
  with
  | [::] => fun _ _ ok => exist _ gamma ok
  | n :: ns => fun Hts Hd ok =>
      let Hin := gammaR_ok_inputs n ok (andP Hts).1 in
      let Hok := node_valuesR_okP n ok (andP Hts).1 (andP Hd).1 in
      let Hv := node_dims_ok_valid_op shn n (andP Hd).1 in
      interp_nodesR shn (node_outputs n ++ defined)%SEQ (interp_nodeR gamma n Hv Hin Hok) ns
        (andP (andP (andP Hts).2).2).2 (andP Hd).2
        (interp_nodeR_ok n Hv Hin Hok ok (andP Hts).1 (andP Hd).1)
  end.

(** ** The model *)

(** The initial map satisfies the invariant when the inputs have the dims of
    their declarations. *)
Lemma gammaR_ok_initial nodes inps inits Hn (xs : 'I_(size inps) -> T R) H :
  graph_acyclic nodes inps inits ->
  (forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple inps) i)) = Some (shapeR (xs i))) ->
  gammaR_ok (infer_dims nodes inps inits)
    (pmap value_name inps ++ pmap tensor_name inits)%SEQ
    (@inputs_fmapR inps Hn xs (inits_fmapR inits H)).
Proof.
move=> ac Hxs s sin.
have Hs : s \in domf (@inputs_fmapR inps Hn xs (inits_fmapR inits H)).
  move: sin; rewrite mem_cat !mem_pmap => /orP [/mapP [v vin vs] | /mapP [t tin ts]].
  - exact: inputs_fmapR_dom vin (esym vs).
  - apply: (fsubsetP (inputs_fmapR_sub _ _ _ _)); exact: inits_fmapR_dom tin (esym ts).
exists Hs; have := in_fnd Hs.
case/inputs_fmapR_fnd => [[i [inm ->]] | /inits_fmapR_fnd [t [tin tnm [Ht ->]]]].
- have iin : tnth (in_tuple inps) i \in inps := mem_tnth i (in_tuple inps).
  have := Hxs i; case E: (value_dims _) => [ds|] //= -[<-].
  by rewrite (infer_dims_input _ _ _ _ _ _ ac iin inm E).
- by rewrite (infer_dims_initialiser _ _ _ _ _ ac tin tnm) shapeR_real_value shape_dims_tensorProto_elem.
Qed.

(** A declaration with the dims of its defined name has the dims of the
    value of that name. *)
Lemma gammaR_ok_output {shn defined gamma} (o : ValueInfoProto) (Hn : value_named o)
  (dt : option DataType_TensorProto) :
  gammaR_ok shn defined gamma ->
  [/\ input_name o Hn \in defined, value_tensor_type o = dt
    & omap (map int64_to_dim) (value_dims o) = shn (input_name o Hn)] ->
  forall Hs : input_name o Hn \in domf gamma,
    omap (map int64_to_dim) (value_dims o) = Some (shapeR gamma.[Hs]).
Proof. by move=> ok [sin _ ->] Hs; exact: (gammaR_ok_get _ Hs ok sin). Qed.

(** The real semantics of a well-formed model: the values of its graph
    outputs, with the dims of their declarations, on values of its graph
    inputs that have the dims of theirs. *)
Definition interp_modelR (m : ModelProto) (Hm : model_well_formed m)
  (xs : 'I_(size (graph_inputs m)) -> T R)
  (Hxs : forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_inputs m)) i))
                   = Some (shapeR (xs i)))
  : {f : 'I_(size (graph_outputs m)) -> T R |
       forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_outputs m)) i))
                 = Some (shapeR (f i))} :=
match m as m0 return
  model_well_formed m0 ->
  forall xs : 'I_(size (graph_inputs m0)) -> T R,
  (forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_inputs m0)) i))
             = Some (shapeR (xs i))) ->
  {f : 'I_(size (graph_outputs m0)) -> T R |
     forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_outputs m0)) i))
               = Some (shapeR (f i))}
with
| ModelProto_constructor ir [:: op] pn pv dom mv doc
    (Some (GraphProto_constructor nodes nm inits sp ds inps outs vi qa mp)) meta tr fs cfg =>
  fun Hm xs Hxs =>
    let m := ModelProto_constructor ir [:: op] pn pv dom mv doc
               (Some (GraphProto_constructor nodes nm inits sp ds inps outs vi qa mp)) meta tr fs cfg in
    let gamma := inits_fmapR inits (model_inits_ok Hm) in
    let gamma := inputs_fmapR (fun i => input_value_named Hm (mem_tnth i (in_tuple (graph_inputs m))))
                              xs gamma in
    let g := interp_nodesR (infer_dims nodes inps inits)
                           (pmap value_name inps ++ pmap tensor_name inits)%SEQ gamma nodes
                           (model_topo Hm) (model_dims Hm)
                           (gammaR_ok_initial _ _ _ _ _ _ (model_acyclic Hm) Hxs) in
    let Hn := fun i : 'I_(size (graph_outputs m)) =>
                output_value_named Hm (mem_tnth i (in_tuple (graph_outputs m))) in
    let Hs := fun i : 'I_(size (graph_outputs m)) =>
                gammaR_ok_mem (input_name (tnth (in_tuple (graph_outputs m)) i) (Hn i)) (svalP g)
                  (and3proj1 (model_outputs_ok Hm i (Hn i))) in
    exist (fun f : 'I_(size (graph_outputs m)) -> T R =>
             forall i, omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_outputs m)) i))
                       = Some (shapeR (f i)))
      (fun i : 'I_(size (graph_outputs m)) => (sval g).[Hs i])
      (fun i : 'I_(size (graph_outputs m)) =>
         gammaR_ok_output (tnth (in_tuple (graph_outputs m)) i) (Hn i) _ (svalP g)
           (model_outputs_ok Hm i (Hn i)) (Hs i))
| ModelProto_constructor _ [::] _ _ _ _ _ _ _ _ _ _ => fun Hm _ _ => False_rect _ (notF Hm)
| ModelProto_constructor _ [:: _] _ _ _ _ _ None _ _ _ _ => fun Hm _ _ => False_rect _ (notF Hm)
| ModelProto_constructor _ (_ :: _ :: _) _ _ _ _ _ _ _ _ _ _ => fun Hm _ _ => False_rect _ (notF Hm)
end Hm xs Hxs.

(** ** The boundary with the real network type *)

(** The input semantics of a real network type, one tensor per declared
    input, and the value at a position. *)
Definition input_semR (y : NetworkType RealElementType) :
  InputSemantics (@realElementTypeInterp R) y ->
  TensorsSemantics (@realElementTypeInterp R) (inputs _ y) :=
  match y with networkType _ _ => id end.

Definition real_input (y : NetworkType RealElementType)
  (inp : InputSemantics (@realElementTypeInterp R) y) (j : 'I_(size (inputs _ y))) : T R :=
  tensor_value _ (input_semR y inp j).

(** The real network type's inputs line up one-to-one with the graph inputs. *)
Lemma real_inputs_size {y1 : NetworkType Elem} {y2 : NetworkType RealElementType} {m : ModelProto} :
  network_dim_match m y1 -> NetworkShapesMatch y1 y2 ->
  size (graph_inputs m) = size (inputs _ y2).
Proof.
move=> /network_dim_match_inputs_size ->.
case: y1 y2 => [inps1 outs1] [inps2 outs2] /= /andP [+ _].
by rewrite all2E => /andP [/eqP].
Qed.

(** Inputs at the same position of network types whose shapes match have the
    same dims. *)
Lemma shapes_match_input {y1 : NetworkType Elem} {y2 : NetworkType RealElementType}
  (H12 : NetworkShapesMatch y1 y2) (j1 : 'I_(size (inputs _ y1))) (j2 : 'I_(size (inputs _ y2))) :
  j1 = j2 :> nat ->
  tensorDims _ (tnth (in_tuple (inputs _ y1)) j1) = tensorDims _ (tnth (in_tuple (inputs _ y2)) j2).
Proof.
case: y1 y2 H12 j1 j2 => [inps1 outs1] [inps2 outs2] /= /andP [+ _] j1 j2 E.
rewrite all2E => /andP [/eqP Hsz /all_nthP same].
set d1 := tnth _ j1; set d2 := tnth _ j2.
have := same (d1, d2) j1.
rewrite nth_zip_cond size_zip -Hsz minnn ltn_ord /= => /(_ isT).
rewrite -[nth d1 _ j1](tnth_nth d1 (in_tuple (sval inps1)) j1) E.
by rewrite -[nth d2 _ j2](tnth_nth d2 (in_tuple (sval inps2)) j2) => /eqP.
Qed.

(** The semantic input at the position of a graph input has the dims of its
    declaration. *)
Lemma real_input_dims {y1 : NetworkType Elem} {y2 : NetworkType RealElementType} {m : ModelProto}
  (Hd : network_dim_match m y1) (H12 : NetworkShapesMatch y1 y2)
  (inp : InputSemantics (@realElementTypeInterp R) y2) (i : 'I_(size (graph_inputs m))) :
  omap (map int64_to_dim) (value_dims (tnth (in_tuple (graph_inputs m)) i))
  = Some (shapeR (real_input y2 inp (cast_ord (real_inputs_size Hd H12) i))).
Proof.
have /andP [_ /eqP ->] := network_dim_match_input Hd i.
by rewrite /real_input shapeR_tensor_value (shapes_match_input H12 _ (cast_ord (real_inputs_size Hd H12) i)).
Qed.

(** A value with the dims of a declaration of type d1 has the shape of a real
    tensor type whose shape matches d1. *)
Lemma real_output_shape {d1 : TensorType Elem} {d2 : TensorType RealElementType}
  {o : ValueInfoProto} {v : T R} :
  value_has_type d1 o -> TensorShapesMatch d1 d2 ->
  omap (map int64_to_dim) (value_dims o) = Some (shapeR v) ->
  existT (fun k : nat => {ffun 'I_k -> {posnum nat}}) (projT1 v) (projT1 (projT2 v))
  = tensorDims _ d2.
Proof.
move=> /andP [_ /eqP ->] /eqP <- [E].
rewrite (dims_typeE (shapeR v) _ (projT1 (projT2 v)) erefl).
by case: (tensorDims _ d1) E => k sh /= E; rewrite (dims_typeE _ _ _ E).
Qed.

(** The value of the requested output over the reals, as a tensor of the
    type [d2] the query gives it: the semantic inputs are the values of the
    graph inputs, the graph is interpreted over R, and the value at the index
    of the output u is read at d2. *)
Definition realSemantics : @RealNetworkSemantics syntax_inst R :=
  fun y1 y2 d1 d2 u n H12 inp out d12 =>
  let Hd := (andP (valP n)).1 in
  let Hm := (andP (valP n)).2 in
  let res := interp_modelR (tag n) Hm
               (fun i => real_input y2 inp (cast_ord (real_inputs_size Hd H12) i))
               (real_input_dims Hd H12 inp) in
  let i := node_output_index out in
  value_tensor d2 (sval res i)
    (real_output_shape (node_output_indexP out).2 d12 (svalP res i)).

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
