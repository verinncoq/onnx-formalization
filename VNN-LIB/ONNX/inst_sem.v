
Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import boot algebra order reals Rstruct finmap.
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

(** A mathcomp tensor read from a flat list of entries, given that the list
has exactly as many entries as the tensor. **)
Definition tensor_of_seq {T : Type} {k : nat} (u : {posnum nat} ^ k) (s : seq T)
  (E : \prod_(i < k) (u i)%:num = size s) : 'nT[T]_(u) :=
  Tensor (\matrix_(i, j) tnth (in_tuple s) (cast_ord E i)).

(** A well-formed tensor of element type x stores exactly as many entries
in the data field for x as its declared shape requires. **)
Lemma well_formed_tensor_size {k : nat} (u : {posnum nat} ^ k) (x : DataType_TensorProto)
  (tp : TensorProto) :
  dims_match tp (existT _ k u) && Tensor_has_type tp x -> tensorProtoSized tp ->
  \prod_(i < k) (u i)%:num =
    let: TensorProto_constructor _ _ _ fd i32 _ i64 _ _ _ _ _ _ _ _ := tp in
    match x with
    | FLOAT_TensorProto => size fd
    | INT32_TensorProto => size i32
    | _ => size i64
    end.
Proof.
case: tp => tdims dt seg fd i32 sd i64 tn ds rd ed dl dd u64 mp /= /andP [/eqP dimsE].
case: dt => [dt|] //; case: (DataType_TensorProto_of_int32 dt) => [y|] // /eqP <- /andP [_].
have -> : \prod_(i < k) (u i)%:num = dims_prod tdims.
  rewrite dims_prodE -(big_map int64_to_dim xpredT id) dimsE big_map /=.
  by rewrite big_map big_enum.
by case: x => // /eqP.
Qed.

(* TODO: data_type is a reference to the enum DataType_TensorProto, so there
should be a check these match *)

(** A TensorProto with the declared dims and element type x, read as a
mathcomp tensor: the data field for x holds exactly the entries of the
shape by [well_formed_tensor_size]. **)
Definition tensorProto_tensor {k : nat} (dims : {posnum nat} ^ k)
  (x : DataType_TensorProto) (Hx : x \in supported_types) (tp : TensorProto)
  (Hw : dims_match tp (existT _ k dims) && Tensor_has_type tp x)
  (Hs : tensorProtoSized tp) : 'nT[denote (exist _ x Hx)]_(dims) :=
  match tp as tp0 return
    dims_match tp0 (existT _ k dims) && Tensor_has_type tp0 x -> tensorProtoSized tp0 ->
    'nT[denote (exist _ x Hx)]_(dims)
  with
  | TensorProto_constructor tdims dt seg fd i32 sd i64 tn ds rd ed dl dd u64 mp =>
    fun Hw Hs =>
    let E x0 := well_formed_tensor_size dims x0
                  (TensorProto_constructor tdims dt seg fd i32 sd i64 tn ds rd ed dl dd u64 mp) in
    match x as x0 return
      forall Hx0 : x0 \in supported_types,
      dims_match (TensorProto_constructor tdims dt seg fd i32 sd i64 tn ds rd ed dl dd u64 mp)
                 (existT _ k dims)
      && Tensor_has_type (TensorProto_constructor tdims dt seg fd i32 sd i64 tn ds rd ed dl dd u64 mp) x0 ->
      'nT[denote (exist _ x0 Hx0)]_(dims)
    with
    | FLOAT_TensorProto => fun _ Hw => tensor_of_seq dims fd (E FLOAT_TensorProto Hw Hs)
    | INT32_TensorProto => fun _ Hw => tensor_of_seq dims i32 (E INT32_TensorProto Hw Hs)
    | INT64_TensorProto => fun _ Hw => tensor_of_seq dims i64 (E INT64_TensorProto Hw Hs)
    | _ => fun Hx0 _ => False_rect _ (notF Hx0)
    end Hx Hw
  end Hw Hs.

(** Function from qTensor + predicates into mathcomp tensor **)
Definition theoryTensorProto (t : TensorType (ElementType syntax_inst)) :
  TheoryTensor syntax_inst t -> TensorSemantics denote t :=
  match t with
  | tensorType (exist x Hx) (existT k dims) => fun p =>
    match p with
    | exist (exist q Hq) Hw => tensorProto_tensor dims x Hx (qtensor_val q) Hw (andP Hq).1
    end
  end.

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
(a b : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \big[add/zero]_j (add (mul (mul a (m1 i j)) (m2 j k)) (mul b zero)).

Definition gemm_3_inputs {R} {m n p} (zero : R) (mul : R -> R -> R) (add : R -> R -> R)
(a b : R) (m1 : 'M[R]_(m, n)) (m2 : 'M[R]_(n, p)) (m3 : 'M[R]_(m, p)) : 'M[R]_(m, p) :=
  (map2_mx (fun x y => add x (mul b y)) (\matrix[mulmx_key]_(i, k) \big[add/zero]_j (mul (mul (m1 i j) a) (m2 j k))) m3).

Definition op_relu {R} {m n} (zero : R) (lt : R -> R -> bool)
                   (m1 : 'M[R]_(m, n)) : 'M[R]_(m, n) :=
  map_mx (fun x => if lt x zero then zero else x) m1.

Open Scope fmap_scope.

Definition node_has_name (n : NodeProto) : bool :=
match n with
| NodeProto_constructor _ _ m _ _ _ _ _ _ _ => isSome m
end.

Definition node_name (n : NodeProto) (Hn : node_has_name n) : string :=
match n as n0 return node_has_name n0 -> string with
| NodeProto_constructor _ _ (Some m) _ _ _ _ _ _ _ => fun _ => m
| _ => fun Hn => False_rect _ (notF Hn)
end Hn.

Definition init_name (t : TensorProto) (Ht : tensorNamed t) : string :=
match t as t0 return tensorNamed t0 -> string with
| TensorProto_constructor _ _ _ _ _ _ _ (Some s) _ _ _ _ _ _ _ => fun _ => s
| _ => fun Ht => False_rect _ (notF Ht)
end Ht.

Definition value_named (v : ValueInfoProto) : bool :=
  match v with
  | ValueInfoProto_constructor n _ _ _ => n
  end.

Definition input_name (v : ValueInfoProto) (Hv : value_named v) : string :=
match v as v0 return value_named v0 -> string with
| ValueInfoProto_constructor (Some s) _ _ _ => fun _ => s
| _ => fun Hv => False_rect _ (notF Hv)
end Hv.

#[local] Obligation Tactic := idtac.

Definition T R := {k : nat & {us : {posnum nat} ^ k & 'nT[R]_(us)}}.

Definition get_Dimension_TensorShapeProto (d : Dimension_TensorShapeProto) : option int64 :=
match d with
| Dimension_TensorShapeProto_constructor (Some (dim_value_value_Dimension_TensorShapeProto x)) _ => Some x
| _ => None
end.

(** A graph value whose tensor type can be read off its declaration: a
supported dtype and a static shape of positive dims. **)
Definition value_info_ok (v : ValueInfoProto) : bool :=
  [&& if value_tensor_type v is Some t then t \in supported_types else false,
      all (fun x => 0 < int64_to_dim x)%nat (odflt [::] (value_dims v))
    & value_dims v != None].

(** Every graph input of a well-formed model has a readable tensor type. **)
Lemma input_value_info_ok {m : ModelProto} {v : ValueInfoProto} :
  model_well_formed m -> v \in graph_inputs m -> value_info_ok v.
Proof.
case: m => ir [//|op [|//]] pn pv dom mv doc [g|//] meta tr fs cfg.
case: g => nodes nm inits sp ds inps outs vi qa mp /= /andP [_].
case/and5P => _ _ /allP decl _ _ vin.
move: (decl v); rewrite mem_cat vin => /(_ isT) /and3P [Hs Hp /and4P [_ _ _ Hd]].
by rewrite /value_info_ok Hs Hp Hd.
Qed.

(** Every graph input of a well-formed model is named. **)
Lemma input_value_named {m : ModelProto} {v : ValueInfoProto} :
  model_well_formed m -> v \in graph_inputs m -> value_named v.
Proof.
case: m => ir [//|op [|//]] pn pv dom mv doc [g|//] meta tr fs cfg.
case: g => nodes nm inits sp ds inps outs vi qa mp /= /andP [_].
case/and5P => _ _ /allP decl _ _ vin.
move: (decl v); rewrite mem_cat vin => /(_ isT) /and3P [_ _ /and4P [_ _ Hn _]].
by case: v Hn vin => [[s|] ? ? ?].
Qed.

(** Every graph output of a well-formed model is named. **)
Lemma output_value_named {m : ModelProto} {v : ValueInfoProto} :
  model_well_formed m -> v \in graph_outputs m -> value_named v.
Proof.
case: m => ir [//|op [|//]] pn pv dom mv doc [g|//] meta tr fs cfg.
case: g => nodes nm inits sp ds inps outs vi qa mp /= /andP [_].
case/and5P => _ _ /allP decl _ _ vin.
move: (decl v); rewrite mem_cat vin orbT => /(_ isT) /and3P [_ _ /and4P [_ _ Hn _]].
by case: v Hn vin => [[s|] ? ? ?].
Qed.

Lemma output_value_info_ok {m : ModelProto} {v : ValueInfoProto} :
  model_well_formed m -> v \in graph_outputs m -> value_info_ok v.
Proof.
case: m => ir [//|op [|//]] pn pv dom mv doc [g|//] meta tr fs cfg.
case: g => nodes nm inits sp ds inps outs vi qa mp /= /andP [_].
case/and5P => _ _ /allP decl _ _ vin.
move: (decl v); rewrite mem_cat vin orbT => /(_ isT) /and3P [Hs Hp /and4P [_ _ _ Hd]].
by rewrite /value_info_ok Hs Hp Hd.
Qed.
(** The tensor type of a value declared with tensor type o and dims ods.
The default 1 is never used: every dim is positive. **)
Definition value_type_tensor (o : option DataType_TensorProto) (ods : option (seq int64)) :
  [&& if o is Some t then t \in supported_types else false,
      all (fun x => 0 < int64_to_dim x)%nat (odflt [::] ods)
    & ods != None] -> Type :=
  match o, ods with
  | Some t, Some ds => fun H =>
      'nT[denote (exist _ t (andP H).1)]_([ffun i : 'I_(size ds) =>
                                            insubd 1%:posnat (int64_to_dim (tnth (in_tuple ds) i))])
  | Some _, None => fun H => False_rect _ (notF (andP (andP H).2).2)
  | None, _ => fun H => False_rect _ (notF H)
  end.

(** The tensor type declared by v. **)
Definition value_info_tensor (v : ValueInfoProto) (Hv : value_info_ok v) : Type :=
  value_type_tensor (value_tensor_type v) (value_dims v) Hv.
(** The shape a TensorProto stores in its dims field. **)
Definition tensorProto_shape (tp : TensorProto) : {k : nat & {posnum nat} ^ k} :=
  dims_type (map int64_to_dim (get_dims tp)).

(** [dims_match] on the dims of the TensorProto and the entries of the shape. **)
Lemma dims_matchE tp sh :
  dims_match tp sh =
  (map int64_to_dim (get_dims tp) == map (fun q : {posnum nat} => q%:num) (tval (projT2 sh))).
Proof. by case: tp; case: sh. Qed.

(** The entries of [dims_type ds] are the entries of ds, clipped to be positive. **)
Lemma map_dims_type ds :
  map (fun q : {posnum nat} => q%:num) (tval (projT2 (dims_type ds))) = map dimc ds.
Proof.
rewrite -[LHS]/(tval (map_tuple _ (projT2 (dims_type ds))))
        -[RHS]/(tval (map_tuple dimc (in_tuple ds))).
congr tval; apply: eq_from_tnth => i.
by rewrite !tnth_map tnth_ord_tuple dims_type_num.
Qed.

(** A sized TensorProto has its own shape. **)
Lemma dims_match_shape {tp x} : tensorProtoSized tp -> Tensor_has_type tp x ->
  dims_match tp (tensorProto_shape tp) && Tensor_has_type tp x.
Proof.
move=> /tensorProtoSized_pos dpos ->; rewrite andbT dims_matchE map_dims_type -map_comp.
by apply/eqP/esym/eq_in_map => d /(allP dpos); exact: dimc_id.
Qed.

(** A sized TensorProto has a supported element type, its data_type. **)
Lemma tensorProtoSized_dtype {tp} : tensorProtoSized tp ->
  if tensor_dtype tp is Some x then (x \in supported_types) && Tensor_has_type tp x else false.
Proof.
case: tp => dims [dt|] ? fd i32 ? i64 ? ? ? ? ? ? ? ? /= /andP [_] //.
rewrite /Tensor_has_type; case: (DataType_TensorProto_of_int32 dt) => [x|] //.
by case: x => //= _; rewrite !inE eqxx.
Qed.

(** A sized TensorProto as a tensor with its shape and element type. **)
Definition tensorProto_elem (tp : TensorProto) (Hs : tensorProtoSized tp) :
  {x : Elem & T (denote x)} :=
  match tensor_dtype tp as o return
    (if o is Some x then (x \in supported_types) && Tensor_has_type tp x else false) ->
    {x : Elem & T (denote x)}
  with
  | Some x => fun H =>
      existT _ (exist _ x (andP H).1)
        (existT _ (projT1 (tensorProto_shape tp))
           (existT _ (projT2 (tensorProto_shape tp))
              (tensorProto_tensor (projT2 (tensorProto_shape tp)) x (andP H).1 tp
                 (dims_match_shape Hs (andP H).2) Hs)))
  | None => fun H => False_rect _ (notF H)
  end (tensorProtoSized_dtype Hs).

(** The named, sized tensors of a sequence, by name. A later tensor of the
same name is shadowed by an earlier one. **)
Fixpoint inits_fmap (s : seq TensorProto) :
  all (fun t => tensorNamed t && tensorProtoSized t) s ->
  {fmap string -> {x : Elem & T (denote x)}} :=
  match s with
  | [::] => fun _ => [fmap]
  | t :: s' => fun H =>
      (inits_fmap s' (andP H).2).[init_name t (andP (andP H).1).1 <-
                                  tensorProto_elem t (andP (andP H).1).2]
  end.

(** A tensor of a declared value, with its shape and element type. **)
Definition value_type_elem (o : option DataType_TensorProto) (ods : option (seq int64)) :
  forall H, value_type_tensor o ods H -> {x : Elem & T (denote x)} :=
  match o as o0, ods as ods0 return
    forall H : [&& if o0 is Some t then t \in supported_types else false,
                   all (fun x => 0 < int64_to_dim x)%nat (odflt [::] ods0)
                 & ods0 != None],
    value_type_tensor o0 ods0 H -> {x : Elem & T (denote x)}
  with
  | Some t, Some ds => fun H x =>
      existT _ (exist _ t (andP H).1)
        (existT _ (size ds)
           (existT (fun us : {posnum nat} ^ (size ds) => 'nT[denote (exist _ t (andP H).1)]_(us))
                   _ x))
  | Some _, None => fun H => False_rect _ (notF (andP (andP H).2).2)
  | None, _ => fun H => False_rect _ (notF H)
  end.

Definition value_info_elem (v : ValueInfoProto) (Hv : value_info_ok v) :
  value_info_tensor v Hv -> {x : Elem & T (denote x)} :=
  value_type_elem (value_tensor_type v) (value_dims v) Hv.

(** gamma with the tensor at every position of vs added under the value's
name. Later positions are shadowed by earlier ones. **)
Definition inputs_fmap {vs : seq ValueInfoProto}
  (Hn : forall i : 'I_(size vs), value_named (tnth (in_tuple vs) i))
  (Hv : forall i : 'I_(size vs), value_info_ok (tnth (in_tuple vs) i))
  (xs : {dffun forall i : 'I_(size vs), value_info_tensor (tnth (in_tuple vs) i) (Hv i)})
  (gamma : {fmap string -> {x : Elem & T (denote x)}}) :
  {fmap string -> {x : Elem & T (denote x)}} :=
  foldr (fun i gamma =>
           gamma.[input_name _ (Hn i) <- value_info_elem _ (Hv i) (xs i)])
        gamma (ord_enum (size vs)).

(** The names the maps use are the declared ones. **)
Lemma init_nameP {t} Ht {nm} : tensor_name t = Some nm -> init_name t Ht = nm.
Proof. by case: t Ht => ? ? ? ? ? ? ? [s|] ? ? ? ? ? ? ? //= _ [] ->. Qed.

Lemma input_nameP {v} Hv {nm} : value_name v = Some nm -> input_name v Hv = nm.
Proof. by case: v Hv => [[s|] ? ? ?] //= _ [] ->. Qed.

(** Every initialiser is in the map under its name. **)
Lemma inits_fmap_dom s H t nm :
  t \in s -> tensor_name t = Some nm -> nm \in domf (inits_fmap s H).
Proof.
elim: s H => //= t' s IH H.
rewrite inE in_fsetU in_fset1 => /orP [/eqP -> tnm | tin tnm]; last by rewrite (IH _ tin tnm) orbT.
by rewrite (init_nameP _ tnm) eqxx.
Qed.

(** Adding the inputs keeps every name already in the map. **)
Lemma inputs_fmap_sub vs Hn Hv xs gamma :
  (domf gamma `<=` domf (@inputs_fmap vs Hn Hv xs gamma))%fset.
Proof.
rewrite /inputs_fmap; elim: (ord_enum _) => //= i l IH.
exact: fsubset_trans IH (fsubsetUr _ _).
Qed.

(** Every input is in the map under its name. **)
Lemma inputs_fmap_dom vs Hn Hv xs gamma v nm :
  v \in vs -> value_name v = Some nm -> nm \in domf (@inputs_fmap vs Hn Hv xs gamma).
Proof.
move=> /(tnthP (in_tuple vs)) [i ->] vnm.
rewrite -(input_nameP (Hn i) vnm) /inputs_fmap.
have := mem_ord_enum i; elim: (ord_enum _) => //= j l IH.
rewrite inE in_fsetU in_fset1 => /orP [/eqP -> | /IH ->]; first by rewrite eqxx.
by rewrite orbT.
Qed.

(** Every initialiser is still in the map once the inputs are added. **)
Lemma inits_inputs_fmap_dom vs Hn Hv xs s H t nm :
  t \in s -> tensor_name t = Some nm ->
  nm \in domf (@inputs_fmap vs Hn Hv xs (inits_fmap s H)).
Proof.
move=> tin tnm; apply: (fsubsetP (inputs_fmap_sub _ _ _ _ _)).
exact: inits_fmap_dom tin tnm.
Qed.

(** A shape of rank 2 is the pair of its entries. **)
Lemma shape2E (us : {posnum nat} ^ 2) : finfun_of_tuple [tuple us ord0; us ord_max] = us.
Proof.
apply/ffunP => i; rewrite ffunE (tnth_nth (us ord0)) /=.
by case: i => [[|[|?]] lt2] //=; congr (us _); exact: val_inj.
Qed.

(** A tensor of rank 2 as a matrix, and a matrix as a tensor of rank 2. **)
Definition mx_of_tensor {R} {us : {posnum nat} ^ 2} (t : 'nT[R]_(us)) :
  'M[R]_((us ord0)%:num, (us ord_max)%:num) :=
  matrix_of_ntensor (ecast u 'nT[R]_(u) (esym (shape2E us)) t).

Definition tensor_of_mx {R} {n m : {posnum nat}} (M : 'M[R]_(n%:num, m%:num)) : T R :=
  existT (fun k => {us : {posnum nat} ^ k & 'nT[R]_(us)}) 2%nat
    (existT (fun us : {posnum nat} ^ 2 => 'nT[R]_(us)) (finfun_of_tuple [tuple n; m])
            (ntensor_of_matrix M)).

(** Shapes of rank 0 and 1 are the tuples of their entries. **)
Lemma shape0E (us : {posnum nat} ^ 0) : finfun_of_tuple [tuple] = us.
Proof. by apply/ffunP => -[m lt0]; exfalso; move: lt0; rewrite ltn0. Qed.

Lemma shape1E (us : {posnum nat} ^ 1) : finfun_of_tuple [tuple us ord0] = us.
Proof.
apply/ffunP => i; rewrite ffunE (tnth_nth (us ord0)) /=.
by case: i => [[|?] lt1] //=; congr (us _); exact: val_inj.
Qed.

(** A tensor of rank 0 as a 1 by 1 matrix, and one of rank 1 as a row, as
[mat_of_dims] reads them for Gemm. **)
Definition mx_of_tensor0 {R} {us : {posnum nat} ^ 0} (t : 'nT[R]_(us)) :
  'M[R]_((1%:posnat)%:num, (1%:posnat)%:num) :=
  const_mx (tensor_nil (ecast u 'nT[R]_(u) (esym (shape0E us)) t)).

Definition mx_of_tensor1 {R} {us : {posnum nat} ^ 1} (t : 'nT[R]_(us)) :
  'M[R]_((1%:posnat)%:num, (us ord0)%:num) :=
  \matrix_(i, j) tensor_nil (nindex (ecast u 'nT[R]_(u) (esym (shape1E us)) t) j).

(** The matrix dims of a shape of rank at most 2, as [mat_of_dims]. **)
Definition gemm_shape {k : nat} : {posnum nat} ^ k -> {posnum nat} * {posnum nat} :=
  match k as k0 return {posnum nat} ^ k0 -> {posnum nat} * {posnum nat} with
  | 0%nat => fun _ => (1%:posnat, 1%:posnat)
  | 1%nat => fun us => (1%:posnat, us ord0)
  | 2%nat => fun us => (us ord0, us ord_max)
  | _ => fun _ => (1%:posnat, 1%:posnat)
  end.

(** A tensor of rank at most 2 as the matrix of those dims. **)
Definition mx_of_tensor_le2 {R} (t : T R) (H : (projT1 t <= 2)%nat) :
  'M[R]_((gemm_shape (projT1 (projT2 t))).1%:num, (gemm_shape (projT1 (projT2 t))).2%:num) :=
  match t as t0 return (projT1 t0 <= 2)%nat ->
      'M[R]_((gemm_shape (projT1 (projT2 t0))).1%:num, (gemm_shape (projT1 (projT2 t0))).2%:num)
  with
  | existT k (existT us x) =>
      match k as k0 return forall us : {posnum nat} ^ k0, 'nT[R]_(us) -> (k0 <= 2)%nat ->
          'M[R]_((gemm_shape us).1%:num, (gemm_shape us).2%:num)
      with
      | 0%nat => fun us x _ => mx_of_tensor0 x
      | 1%nat => fun us x _ => mx_of_tensor1 x
      | 2%nat => fun us x _ => mx_of_tensor x
      | _ => fun _ _ H => False_rect _ (notF H)
      end us x
  end H.

(** A tensor read as a matrix: rank 2 with its dims. **)
Definition M2 (R : Type) := {n : {posnum nat} & {m : {posnum nat} & 'nT[R]_([tuple n; m])}}.

(** A tensor of rank at most 2 broadcast to a matrix. **)
Definition bcast2 {R} (t : T R) (H : (projT1 t <= 2)%nat) : M2 R :=
  existT (fun n : {posnum nat} => {m : {posnum nat} & 'nT[R]_([tuple n; m])})
    (gemm_shape (projT1 (projT2 t))).1
    (existT (fun m : {posnum nat} => 'nT[R]_([tuple (gemm_shape (projT1 (projT2 t))).1; m]))
       (gemm_shape (projT1 (projT2 t))).2
       (ntensor_of_matrix (mx_of_tensor_le2 t H))).

(** The shape a Gemm attribute transA or transB selects, as [trans_dims]. **)
Definition trans_shape (t : int64) (hw : {posnum nat} * {posnum nat}) : {posnum nat} * {posnum nat} :=
  if Z_of_int64 t is 0%Z then hw else (hw.2, hw.1).

(** The matrix the attribute selects: M itself when it is 0, else M^T. **)
Definition trans_mx {R} {n m : {posnum nat}} (t : int64) (M : 'M[R]_(n%:num, m%:num)) :
  'M[R]_((trans_shape t (n, m)).1%:num, (trans_shape t (n, m)).2%:num) :=
  match Z_of_int64 t as z return
    'M[R]_((if z is 0%Z then (n, m) else (m, n)).1%:num, (if z is 0%Z then (n, m) else (m, n)).2%:num)
  with
  | 0%Z => M
  | _ => M^T
  end.

(** The Gemm attributes, by projection. **)
Definition gemm_alpha (attribs : seq AttributeProto) : float32 := (get_gemm_attributes attribs).1.1.1.
Definition gemm_beta (attribs : seq AttributeProto) : float32 := (get_gemm_attributes attribs).1.1.2.
Definition gemm_transA (attribs : seq AttributeProto) : int64 := (get_gemm_attributes attribs).1.2.
Definition gemm_transB (attribs : seq AttributeProto) : int64 := (get_gemm_attributes attribs).2.

(** Over an integer dtype, alpha and beta are integers: the Gemm clause of
model_well_formed. **)
Lemma gemm_int_alpha {x : DataType_TensorProto} {attribs} :
  (x == FLOAT_TensorProto) || gemm_int_attrs_ok attribs ->
  (x == FLOAT_TensorProto) || isSome (Z_of_float32 (gemm_alpha attribs)).
Proof.
rewrite /gemm_int_attrs_ok /gemm_alpha; case: (get_gemm_attributes attribs) => [[[a b] tA] tB] /=.
by case: (x == _) => //= /andP [].
Qed.

Lemma gemm_int_beta {x : DataType_TensorProto} {attribs} :
  (x == FLOAT_TensorProto) || gemm_int_attrs_ok attribs ->
  (x == FLOAT_TensorProto) || isSome (Z_of_float32 (gemm_beta attribs)).
Proof.
rewrite /gemm_int_attrs_ok /gemm_beta; case: (get_gemm_attributes attribs) => [[[a b] tA] tB] /=.
by case: (x == _) => //= /andP [].
Qed.

(** A float that is an integer, as that integer. **)
Definition Z_of_float32_int (f : float32) (H : isSome (Z_of_float32 f)) : Z :=
  match Z_of_float32 f as o return isSome o -> Z with
  | Some z => fun _ => z
  | None => fun H => False_rect _ (notF H)
  end H.

(** The zero, product and sum of a supported element type, as in op_gemm. **)
Definition elem_ops (x : Elem) :
  denote x * (denote x -> denote x -> denote x) * (denote x -> denote x -> denote x) :=
  match x as x0 return
    denote x0 * (denote x0 -> denote x0 -> denote x0) * (denote x0 -> denote x0 -> denote x0)
  with
  | exist FLOAT_TensorProto _ =>
      (Binary.B754_zero 24 128 false, b32_mult BinarySingleNaN.mode_NE, b32_plus BinarySingleNaN.mode_NE)
  | exist INT32_TensorProto _ =>
      (int32_of_Z 0, fun a b => int32_of_Z (Z_of_int32 a * Z_of_int32 b)%Z,
                     fun a b => int32_of_Z (Z_of_int32 a + Z_of_int32 b)%Z)
  | exist INT64_TensorProto _ =>
      (int64_of_Z 0, fun a b => int64_of_Z (Z_of_int64 a * Z_of_int64 b)%Z,
                     fun a b => int64_of_Z (Z_of_int64 a + Z_of_int64 b)%Z)
  | exist _ Hx => False_rect _ (notF Hx)
  end.

(** A float attribute as an element: itself over floats, and over an integer
dtype the integer it is. **)
Definition elem_of_float32 (x : Elem) (f : float32)
  (H : (sval x == FLOAT_TensorProto) || isSome (Z_of_float32 f)) : denote x :=
  match x as x0 return (sval x0 == FLOAT_TensorProto) || isSome (Z_of_float32 f) -> denote x0 with
  | exist FLOAT_TensorProto _ => fun _ => f
  | exist INT32_TensorProto _ => fun H => int32_of_Z (Z_of_float32_int f H)
  | exist INT64_TensorProto _ => fun H => int64_of_Z (Z_of_float32_int f H)
  | exist _ Hx => fun _ => False_rect _ (notF Hx)
  end H.

Lemma posnat_gt0 (m : {posnum nat}) : (0 < m%:num)%nat.
Proof. by case: m => v /=; rewrite /Itv.spec /= /Itv.nat_sem in_itv /= andbT ltz_nat. Qed.

(** Index k of a dimension m, broadcasting: 0 when k is out of range, as
for a dimension of size 1. **)
Definition bidx_pos (m : {posnum nat}) (k : nat) : 'I_m%:num :=
  match (k < m%:num)%nat as b return (k < m%:num)%nat = b -> 'I_m%:num with
  | true => fun E => Ordinal E
  | false => fun _ => Ordinal (posnat_gt0 m)
  end erefl.

(** C broadcast to the n by p output of a Gemm. **)
Definition bcast_mx {R} {h w : {posnum nat}} {n p : nat} (C : 'M[R]_(h%:num, w%:num)) : 'M[R]_(n, p) :=
  \matrix_(i, j) C (bidx_pos h i) (bidx_pos w j).

(** The value of a Gemm node on the values of its inputs, read as matrices
of the element type x, with alpha and beta integers over an integer dtype and
the inner dims of A' and B' equal. **)
Definition interp_gemm (x : Elem) (A B : M2 (denote x)) (C : option (M2 (denote x)))
  (attribs : seq AttributeProto)
  (Hint : (sval x == FLOAT_TensorProto) || gemm_int_attrs_ok attribs)
  (Hk : (trans_shape (gemm_transB attribs) (projT1 B, projT1 (projT2 B))).1%:num
        = (trans_shape (gemm_transA attribs) (projT1 A, projT1 (projT2 A))).2%:num)
  : T (denote x) :=
  let ops := elem_ops x in
  let alpha := elem_of_float32 x (gemm_alpha attribs) (gemm_int_alpha Hint) in
  let beta := elem_of_float32 x (gemm_beta attribs) (gemm_int_beta Hint) in
  let A' := trans_mx (gemm_transA attribs) (matrix_of_ntensor (projT2 (projT2 A))) in
  let B' := castmx (Hk, erefl) (trans_mx (gemm_transB attribs) (matrix_of_ntensor (projT2 (projT2 B)))) in
  match C with
  | Some C => tensor_of_mx (gemm_3_inputs ops.1.1 ops.1.2 ops.2 alpha beta A' B'
                              (bcast_mx (matrix_of_ntensor (projT2 (projT2 C)))))
  | None => tensor_of_mx (gemm_2_inputs ops.1.1 ops.1.2 ops.2 alpha beta A' B')
  end.

(** The value negatives become, and the comparison, of a supported element
type, as in op_relu. **)
Definition relu_ops (x : Elem) : denote x * (denote x -> denote x -> bool) :=
  match x as x0 return denote x0 * (denote x0 -> denote x0 -> bool) with
  | exist FLOAT_TensorProto _ =>
      (Binary.B754_zero 24 128 true,
       fun a b => if a is Binary.B754_finite true _ _ _
                  then (if Binary.Bcompare 24 128 a b is Some Lt then true else false)
                  else false)
  | exist INT32_TensorProto _ => (int32_of_Z 0, fun a b => (Z_of_int32 a <? Z_of_int32 b)%Z)
  | exist INT64_TensorProto _ => (int64_of_Z 0, fun a b => (Z_of_int64 a <? Z_of_int64 b)%Z)
  | exist _ Hx => False_rect _ (notF Hx)
  end.

(** The value of a Relu node on the value of its input: relu on every entry
of the tensor, read as its matrix of entries and cast back. Any rank. **)
Definition interp_relu (A : {x : Elem & T (denote x)}) : {x : Elem & T (denote x)} :=
  let x := projT1 A in
  let ops := relu_ops x in
  existT (fun x => T (denote x)) x
    (existT (fun k => {us : {posnum nat} ^ k & 'nT[denote x]_(us)}) (projT1 (projT2 A))
       (existT (fun us => 'nT[denote x]_(us)) (projT1 (projT2 (projT2 A)))
          (Tensor (op_relu ops.1 ops.2 (tensor_val (projT2 (projT2 (projT2 A)))))))).

(** gamma with v bound to every name in outs. **)
Definition bind_outputs (gamma : {fmap string -> {x : Elem & T (denote x)}})
  (outs : seq string) (v : {x : Elem & T (denote x)}) :
  {fmap string -> {x : Elem & T (denote x)}} :=
  foldr (fun o gamma => gamma.[o <- v]) gamma outs.

(** A matrix over the element type y as one over x. **)
Definition cast_elem {y x : Elem} (H : y = x) (v : M2 (denote y)) : M2 (denote x) :=
  existT _ (projT1 v)
    (existT _ (projT1 (projT2 v))
       (ecast z ('nT[denote z]_([tuple projT1 v; projT1 (projT2 v)])) H (projT2 (projT2 v)))).

(** What interp_gemm needs of the values a, b and c of a Gemm node's inputs:
a and b of rank at most 2 and of one element type, alpha and beta integers
over an integer dtype, the inner dims of A' and B' equal, and c, if any, of
rank at most 2 and of that element type. **)
Record gemm_values_ok (a b : {x : Elem & T (denote x)}) (c : option {x : Elem & T (denote x)}) (attribs : seq AttributeProto) : Prop :=
  GemmValuesOk {
    gemm_rank_a : (projT1 (projT2 a) <= 2)%nat;
    gemm_elem_b : projT1 b = projT1 a;
    gemm_rank_b : (projT1 (projT2 b) <= 2)%nat;
    gemm_int : (sval (projT1 a) == FLOAT_TensorProto) || gemm_int_attrs_ok attribs;
    gemm_inner :
      let sa := gemm_shape (projT1 (projT2 (projT2 a))) in
      let sb := gemm_shape (projT1 (projT2 (projT2 b))) in
      (trans_shape (gemm_transB attribs) (sb.1, sb.2)).1%:num
      = (trans_shape (gemm_transA attribs) (sa.1, sa.2)).2%:num;
    gemm_c : if c is Some c then projT1 c = projT1 a /\ (projT1 (projT2 c) <= 2)%nat else True
  }.

Arguments gemm_rank_a {a b c attribs}.
Arguments gemm_elem_b {a b c attribs}.
Arguments gemm_rank_b {a b c attribs}.
Arguments gemm_int {a b c attribs}.
Arguments gemm_inner {a b c attribs}.
Arguments gemm_c {a b c attribs}.

(** The facts above for the values of the inputs of n in gamma. **)
Definition node_values_ok (gamma : {fmap string -> {x : Elem & T (denote x)}}) (n : NodeProto) : Prop :=
  match n with
  | NodeProto_constructor [:: A; B] _ _ _ _ _ attribs _ _ _ =>
      forall (HA : A \in domf gamma) (HB : B \in domf gamma),
        gemm_values_ok gamma.[HA] gamma.[HB] None attribs
  | NodeProto_constructor [:: A; B; C] _ _ _ _ _ attribs _ _ _ =>
      forall (HA : A \in domf gamma) (HB : B \in domf gamma) (HC : C \in domf gamma),
        gemm_values_ok gamma.[HA] gamma.[HB] (Some gamma.[HC]) attribs
  | _ => True
  end.

(** gamma with the outputs of the node n bound to its value. The node is a
supported operation of the right arity, gamma has all its inputs, and their
values are as a Gemm needs. **)
Definition interp_node (gamma : {fmap string -> {x : Elem & T (denote x)}}) (n : NodeProto) (Hv : valid_op n)
  (Hin : all (fun i => i \in domf gamma) (node_inputs n)) (Hok : node_values_ok gamma n)
  : {fmap string -> {x : Elem & T (denote x)}} :=
match n as n0 return
  valid_op n0 -> all (fun i => i \in domf gamma) (node_inputs n0) -> node_values_ok gamma n0 -> {fmap string -> {x : Elem & T (denote x)}}
with
| NodeProto_constructor inps outs nm (Some op) dom ov attribs doc meta dev => fun Hv Hin Hok =>
    match (op =? """Gemm""")%string as g return
      (if g then (size inps == 2%nat) || (size inps == 3%nat)
       else if (op =? """Relu""")%string then size inps == 1%nat else false) -> {fmap string -> {x : Elem & T (denote x)}}
    with
    | true => fun Hv =>
      match inps as l return
        (size l == 2%nat) || (size l == 3%nat) -> all (fun i => i \in domf gamma) l ->
        node_values_ok gamma (NodeProto_constructor l outs nm (Some op) dom ov attribs doc meta dev) ->
        {fmap string -> {x : Elem & T (denote x)}}
      with
      | [:: A; B] => fun _ Hin Hok =>
          let HA := (andP Hin).1 in
          let HB := (andP (andP Hin).2).1 in
          let a := gamma.[HA] in
          let b := gamma.[HB] in
          let ok := Hok HA HB in
          bind_outputs gamma outs
            (existT _ (projT1 a)
               (interp_gemm (projT1 a) (bcast2 (projT2 a) (gemm_rank_a ok))
                  (cast_elem (gemm_elem_b ok) (bcast2 (projT2 b) (gemm_rank_b ok)))
                  None attribs (gemm_int ok) (gemm_inner ok)))
      | [:: A; B; C] => fun _ Hin Hok =>
          let HA := (andP Hin).1 in
          let HB := (andP (andP Hin).2).1 in
          let HC := (andP (andP (andP Hin).2).2).1 in
          let a := gamma.[HA] in
          let b := gamma.[HB] in
          let c := gamma.[HC] in
          let ok := Hok HA HB HC in
          bind_outputs gamma outs
            (existT _ (projT1 a)
               (interp_gemm (projT1 a) (bcast2 (projT2 a) (gemm_rank_a ok))
                  (cast_elem (gemm_elem_b ok) (bcast2 (projT2 b) (gemm_rank_b ok)))
                  (Some (cast_elem (proj1 (gemm_c ok)) (bcast2 (projT2 c) (proj2 (gemm_c ok)))))
                  attribs (gemm_int ok) (gemm_inner ok)))
      | [::] => fun Hv _ _ => False_rect _ (notF Hv)
      | [:: _] => fun Hv _ _ => False_rect _ (notF Hv)
      | [:: _, _, _, _ & _] => fun Hv _ _ => False_rect _ (notF Hv)
      end Hv Hin Hok
    | false => fun Hv =>
      match (op =? """Relu""")%string as r return (if r then size inps == 1%nat else false) -> {fmap string -> {x : Elem & T (denote x)}} with
      | true => fun Hv =>
        match inps as l return size l == 1%nat -> all (fun i => i \in domf gamma) l -> {fmap string -> {x : Elem & T (denote x)}} with
        | [:: A] => fun _ Hin => bind_outputs gamma outs (interp_relu gamma.[(andP Hin).1])
        | [::] => fun Hv _ => False_rect _ (notF Hv)
        | [:: _, _ & _] => fun Hv _ => False_rect _ (notF Hv)
        end Hv Hin
      | false => fun Hv => False_rect _ (notF Hv)
      end Hv
    end Hv
| NodeProto_constructor _ _ _ None _ _ _ _ _ _ => fun Hv _ _ => False_rect _ (notF Hv)
end Hv Hin Hok.

(** The dims of a value, as a list. **)
Definition shape_dims (v : {x : Elem & T (denote x)}) : seq nat :=
  map (fun q : {posnum nat} => q%:num) (tval (projT1 (projT2 (projT2 v)))).

(** gamma binds every defined name to a value of the model dtype dt with the
dims shn gives the name. **)
Definition gamma_ok (dt : option DataType_TensorProto) (shn : string -> option (seq nat))
  (defined : seq string) (gamma : {fmap string -> {x : Elem & T (denote x)}}) : Prop :=
  forall s, s \in defined -> exists Hs : s \in domf gamma,
    Some (sval (projT1 gamma.[Hs])) = dt /\ shn s = Some (shape_dims gamma.[Hs]).

(** The names defined after the nodes, as [topo_sorted] accumulates them. **)
Definition defined_after (defined : seq string) (nodes : seq NodeProto) : seq string :=
  foldl (fun d n => (node_outputs n ++ d)%SEQ) defined nodes.

(** The inputs of a node whose inputs are defined are in gamma. **)
Lemma gamma_ok_inputs {dt shn defined gamma} (n : NodeProto) :
  gamma_ok dt shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  all (fun i => i \in domf gamma) (node_inputs n).
Proof. by move=> ok /allP H; apply/allP => i /H /ok [Hi _]. Qed.

(** The rank of a value is the length of its dims. **)
Lemma shape_dims_rank (v : {x : Elem & T (denote x)}) : size (shape_dims v) = projT1 (projT2 v).
Proof. by rewrite /shape_dims size_map size_tuple. Qed.

(** The matrix dims of a shape of rank at most 2 are [mat_of_dims] of its
entries. **)
Lemma gemm_shapeE k (us : {posnum nat} ^ k) : (k <= 2)%nat ->
  ((gemm_shape us).1%:num, (gemm_shape us).2%:num)
  = mat_of_dims (map (fun q : {posnum nat} => q%:num) (tval us)).
Proof.
case: k us => [|[|[|k]]] us // _.
- by rewrite -[in RHS](shape0E us) finfun_of_tupleK.
- by rewrite -[in RHS](shape1E us) finfun_of_tupleK.
- by rewrite -[in RHS](shape2E us) finfun_of_tupleK.
Qed.

(** [trans_shape] is [trans_dims] on the dims. **)
Lemma trans_shapeE t (hw : {posnum nat} * {posnum nat}) :
  ((trans_shape t hw).1%:num, (trans_shape t hw).2%:num) = trans_dims t (hw.1%:num, hw.2%:num).
Proof. by rewrite /trans_shape /trans_dims; case: (Z_of_int64 t). Qed.

(** The dims Gemm reads a value of rank at most 2 with, transposed. **)
Lemma trans_gemm_shapeE t (v : {x : Elem & T (denote x)}) : (size (shape_dims v) <= 2)%nat ->
  let s := gemm_shape (projT1 (projT2 (projT2 v))) in
  ((trans_shape t (s.1, s.2)).1%:num, (trans_shape t (s.1, s.2)).2%:num)
  = trans_dims t (mat_of_dims (shape_dims v)).
Proof. by rewrite shape_dims_rank => rk /=; rewrite trans_shapeE /= gemm_shapeE. Qed.

(** The value gamma has for a defined name, at any proof that it has one. **)
Lemma gamma_ok_get {dt shn defined gamma} s (Hs : s \in domf gamma) :
  gamma_ok dt shn defined gamma -> s \in defined ->
  Some (sval (projT1 gamma.[Hs])) = dt /\ shn s = Some (shape_dims gamma.[Hs]).
Proof. by move=> ok /ok [Hs']; rewrite (bool_irrelevance Hs' Hs). Qed.

(** Values of the model dtype whose dims Gemm accepts are as a Gemm needs. **)
Lemma gemm_values_okP dt attrs (a b : {x : Elem & T (denote x)}) c ds :
  Some (sval (projT1 a)) = dt -> Some (sval (projT1 b)) = dt ->
  (if c is Some c' then Some (sval (projT1 c')) = dt else True) ->
  (dt == Some FLOAT_TensorProto) || gemm_int_attrs_ok attrs ->
  gemm_out_dims attrs (shape_dims a) (shape_dims b) (omap shape_dims c) = Some ds ->
  gemm_values_ok a b c attrs.
Proof.
move=> Ea Eb Ec Hi /gemm_out_dimsP.
have tAE := trans_gemm_shapeE (gemm_transA attrs) a.
have tBE := trans_gemm_shapeE (gemm_transB attrs) b.
move: tAE tBE; rewrite /gemm_transA /gemm_transB.
case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] /= tAE tBE [ra rb kk _ cok].
split.
- by rewrite -shape_dims_rank.
- by apply: val_inj; move: Eb; rewrite -Ea => -[].
- by rewrite -shape_dims_rank.
- by move: Hi; rewrite -Ea.
- by move: kk; rewrite -(tAE ra) -(tBE rb) /gemm_transA /gemm_transB E /= => ->.
- case: c Ec cok => [c|] //= Ec; case: (mat_of_dims _) => h w /andP [rc _]; split.
  + by apply: val_inj; move: Ec; rewrite -Ea => -[].
  + by rewrite -shape_dims_rank.
Qed.

(** The values of the inputs of a well typed node are as a Gemm needs. **)
Lemma node_values_okP {dt shn defined gamma} (n : NodeProto) :
  gamma_ok dt shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  node_dims_ok shn n -> (dt == Some FLOAT_TensorProto) || gemm_int_attrs_ok (get_attributes n) ->
  node_values_ok gamma n.
Proof.
move=> ok.
case: n => [[|A [|B [|C [|? ?]]]] outs nm [s|] dom ov attrs doc meta dev] //=.
- move=> /and3P [Ain Bin _]; rewrite /node_dims_ok /node_out_dims.
  case: ifP => _; last by case: ifP.
  case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //.
  case G: (gemm_out_dims _ _ _ _) => [ds|] // _ Hi HA HB.
  have [ta sa] := gamma_ok_get A HA ok Ain; have [tb sb] := gamma_ok_get B HB ok Bin.
  apply: (@gemm_values_okP dt attrs _ _ None ds) => //.
  by move: sa sb; rewrite EA EB => -[<-] [<-].
- move=> /and4P [Ain Bin Cin _]; rewrite /node_dims_ok /node_out_dims.
  case: ifP => _; last by case: ifP.
  case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //; case EC: (shn C) => [dc|] //.
  case G: (gemm_out_dims _ _ _ _) => [ds|] // _ Hi HA HB HC.
  have [ta sa] := gamma_ok_get A HA ok Ain; have [tb sb] := gamma_ok_get B HB ok Bin.
  have [tc sc] := gamma_ok_get C HC ok Cin.
  apply: (@gemm_values_okP dt attrs _ _ (Some _) ds) => //.
  by move: sa sb sc; rewrite EA EB EC /= => -[<-] [<-] [<-].
Qed.

(** The names and values of gamma with v bound to outs. **)
Lemma bind_outputs_dom gamma outs v s :
  s \in domf (bind_outputs gamma outs v) = (s \in outs) || (s \in domf gamma).
Proof. by elim: outs => //= o outs IH; rewrite in_fsetU in_fset1 IH inE orbA. Qed.

Lemma bind_outputs_fnd gamma outs v s :
  (bind_outputs gamma outs v).[? s] = if s \in outs then Some v else gamma.[? s].
Proof. by elim: outs => //= o outs IH; rewrite fnd_set inE IH; case: eqP. Qed.

(** Binding a value of the model dtype to names that have its dims keeps the
invariant. **)
Lemma bind_outputs_ok {dt shn defined gamma} outs (v : {x : Elem & T (denote x)}) :
  gamma_ok dt shn defined gamma -> Some (sval (projT1 v)) = dt ->
  all (fun o => shn o == Some (shape_dims v)) outs ->
  gamma_ok dt shn (outs ++ defined)%SEQ (bind_outputs gamma outs v).
Proof.
move=> ok Ev /allP Hsh s; rewrite mem_cat => sin.
have Hs : s \in domf (bind_outputs gamma outs v).
  by rewrite bind_outputs_dom; case/orP: sin => [-> //|/ok [Hs' _]]; rewrite Hs' orbT.
exists Hs; have := in_fnd Hs; rewrite bind_outputs_fnd.
case: ifP sin => [so _ [<-] | _ /= sd]; first by split=> //; exact/eqP/Hsh.
by case: (ok s sd) => Hs' [E1 E2]; rewrite in_fnd => -[<-].
Qed.

(** The dims of a matrix as a tensor. **)
Lemma shape_dims_tensor_of_mx (x : Elem) (n m : {posnum nat}) (M : 'M[denote x]_(n%:num, m%:num)) :
  shape_dims (existT _ x (tensor_of_mx M)) = [:: n%:num; m%:num].
Proof.
rewrite /shape_dims.
change (map (fun q : {posnum nat} => q%:num)
          (tval (tuple_of_finfun (finfun_of_tuple [tuple n; m]))) = [:: n%:num; m%:num]).
by rewrite finfun_of_tupleK.
Qed.

(** The dims of the value of a Gemm: the rows of A' and the columns of B'. **)
Lemma shape_dims_interp_gemm x A B C attribs Hint Hk :
  shape_dims (existT _ x (interp_gemm x A B C attribs Hint Hk))
  = [:: (trans_shape (gemm_transA attribs) (projT1 A, projT1 (projT2 A))).1%:num;
        (trans_shape (gemm_transB attribs) (projT1 B, projT1 (projT2 B))).2%:num].
Proof. by rewrite /interp_gemm; case: C => [C|]; exact: shape_dims_tensor_of_mx. Qed.

(** The node's outputs get the model dtype and the dims shn gives them, and
the defined names keep their values. **)
Lemma interp_node_ok {dt shn defined gamma} (n : NodeProto) Hv Hin Hok :
  gamma_ok dt shn defined gamma -> all (fun i => i \in defined) (node_inputs n) ->
  node_dims_ok shn n ->
  gamma_ok dt shn (node_outputs n ++ defined)%SEQ (interp_node gamma n Hv Hin Hok).
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
    have [ta sa] := gamma_ok_get A (andP Hin).1 ok Ain.
    have [_ sb] := gamma_ok_get B (andP (andP Hin).2).1 ok Bin.
    have daE : da = shape_dims gamma.[(andP Hin).1] by move: sa; rewrite EA => -[].
    have dbE : db = shape_dims gamma.[(andP (andP Hin).2).1] by move: sb; rewrite EB => -[].
    move: G; rewrite daE dbE => /gemm_out_dimsP; case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] [ra rb _ dsE _].
    have tAE := congr1 fst (trans_gemm_shapeE tA gamma.[(andP Hin).1] ra).
    have tBE := congr1 snd (trans_gemm_shapeE tB gamma.[(andP (andP Hin).2).1] rb).
    apply: bind_outputs_ok => //.
    rewrite shape_dims_interp_gemm.
    by move: Hsh; rewrite dsE -tAE -tBE /gemm_transA /gemm_transB E.
  + move=> /and4P [Ain Bin _ _].
    case EA: (shn A) => [da|] //; case EB: (shn B) => [db|] //; case EC: (shn C) => [dc|] //.
    case G: (gemm_out_dims _ _ _ _) => [ds|] // /andP [_ Hsh].
    have [ta sa] := gamma_ok_get A (andP Hin).1 ok Ain.
    have [_ sb] := gamma_ok_get B (andP (andP Hin).2).1 ok Bin.
    have daE : da = shape_dims gamma.[(andP Hin).1] by move: sa; rewrite EA => -[].
    have dbE : db = shape_dims gamma.[(andP (andP Hin).2).1] by move: sb; rewrite EB => -[].
    move: G; rewrite daE dbE => /gemm_out_dimsP; case E: (get_gemm_attributes attrs) => [[[al be] tA] tB] [ra rb _ dsE _].
    have tAE := congr1 fst (trans_gemm_shapeE tA gamma.[(andP Hin).1] ra).
    have tBE := congr1 snd (trans_gemm_shapeE tB gamma.[(andP (andP Hin).2).1] rb).
    apply: bind_outputs_ok => //.
    rewrite shape_dims_interp_gemm.
    by move: Hsh; rewrite dsE -tAE -tBE /gemm_transA /gemm_transB E.
- move/String.eqb_eq: Er Hv Hin Hok => -> {s Eg}.
  case: inps => [|A [|? ?]] // Hv Hin Hok /andP [Ain _].
  case EA: (shn A) => [da|] // /andP [_ Hsh].
  have [ta sa] := gamma_ok_get A (andP Hin).1 ok Ain.
  apply: bind_outputs_ok => //.
  by move: sa Hsh; rewrite EA => -[->].
Qed.

(** The model dtype: that of the first graph output, as in model_well_formed. **)
Definition outputs_dtype (outs : seq ValueInfoProto) : option DataType_TensorProto :=
  if outs is o :: _ then value_tensor_type o else None.

(** gamma with the values of the nodes, in list order, which [topo_sorted]
makes a topological order. **)
Fixpoint interp_nodes (dt : option DataType_TensorProto) (shn : string -> option (seq nat))
  (defined : seq string) (gamma : {fmap string -> {x : Elem & T (denote x)}}) (nodes : seq NodeProto) :
  topo_sorted defined nodes -> all (node_dims_ok shn) nodes ->
  all (fun n => (dt == Some FLOAT_TensorProto) || gemm_int_attrs_ok (get_attributes n)) nodes ->
  gamma_ok dt shn defined gamma ->
  {g : {fmap string -> {x : Elem & T (denote x)}} | gamma_ok dt shn (defined_after defined nodes) g} :=
  match nodes as ns return
    topo_sorted defined ns -> all (node_dims_ok shn) ns ->
    all (fun n => (dt == Some FLOAT_TensorProto) || gemm_int_attrs_ok (get_attributes n)) ns ->
    gamma_ok dt shn defined gamma ->
    {g : {fmap string -> {x : Elem & T (denote x)}} | gamma_ok dt shn (defined_after defined ns) g}
  with
  | [::] => fun _ _ _ ok => exist _ gamma ok
  | n :: ns => fun Hts Hd Hi ok =>
      let Hin := gamma_ok_inputs n ok (andP Hts).1 in
      let Hok := node_values_okP n ok (andP Hts).1 (andP Hd).1 (andP Hi).1 in
      let Hv := node_dims_ok_valid_op shn n (andP Hd).1 in
      interp_nodes dt shn (node_outputs n ++ defined)%SEQ (interp_node gamma n Hv Hin Hok) ns
        (andP (andP (andP Hts).2).2).2 (andP Hd).2 (andP Hi).2
        (interp_node_ok n Hv Hin Hok ok (andP Hts).1 (andP Hd).1)
  end.

(** The shape a declaration with dims ds gives, as [value_type_tensor]
reads it. **)
Definition value_type_shape (ds : seq int64) : {posnum nat} ^ (size ds) :=
  [ffun i : 'I_(size ds) => insubd 1%:posnat (int64_to_dim (tnth (in_tuple ds) i))].

(** Its entries are the declared dims when these are positive. **)
Lemma value_type_shapeE {ds} : all (fun x => 0 < int64_to_dim x)%nat ds ->
  map (fun q : {posnum nat} => q%:num) (tval (value_type_shape ds)) = map int64_to_dim ds.
Proof.
move=> dpos.
have pos i : Itv.spec Itv.nat_sem (Itv.Real `]0%R, +oo[) (int64_to_dim (tnth (in_tuple ds) i)).
  have := allP dpos _ (mem_tnth i (in_tuple ds)).
  by rewrite /Itv.spec /= /Itv.nat_sem in_itv /= andbT.
rewrite -[LHS]/(tval (map_tuple _ (value_type_shape ds)))
        -[RHS]/(tval (map_tuple int64_to_dim (in_tuple ds))).
congr tval; apply: eq_from_tnth => i.
by rewrite !tnth_map tnth_ord_tuple ffunE insubdK //; exact: pos.
Qed.

(** The shape of a value equals a declared shape with the same dims. **)
Lemma value_shapeE (v : {x : Elem & T (denote x)}) ds :
  all (fun x => 0 < int64_to_dim x)%nat ds -> shape_dims v = map int64_to_dim ds ->
  existT (fun k : nat => {ffun 'I_k -> {posnum nat}}) (projT1 (projT2 v)) (projT1 (projT2 (projT2 v)))
  = existT _ (size ds) (value_type_shape ds).
Proof.
move=> dpos E; rewrite (dims_typeE _ _ _ (value_type_shapeE dpos)).
exact: dims_typeE.
Qed.

(** A value of the dtype and dims a declaration with tensor type o and dims
ods gives, as the tensor type of that declaration. **)
Definition value_type_of (o : option DataType_TensorProto) (ods : option (seq int64)) :
  forall (H : [&& if o is Some t then t \in supported_types else false,
                  all (fun x => 0 < int64_to_dim x)%nat (odflt [::] ods)
                & ods != None])
         (v : {x : Elem & T (denote x)}),
  o = Some (sval (projT1 v)) -> omap (map int64_to_dim) ods = Some (shape_dims v) ->
  value_type_tensor o ods H :=
  match o as o0, ods as ods0 return
    forall H : [&& if o0 is Some t then t \in supported_types else false,
                   all (fun x => 0 < int64_to_dim x)%nat (odflt [::] ods0)
                 & ods0 != None],
    forall v : {x : Elem & T (denote x)},
    o0 = Some (sval (projT1 v)) -> omap (map int64_to_dim) ods0 = Some (shape_dims v) ->
    value_type_tensor o0 ods0 H
  with
  | Some t, Some ds => fun H v Ht Hd =>
      let Ex : projT1 v = exist _ t (andP H).1 :=
        @val_inj _ _ _ (projT1 v) (exist _ t (andP H).1) (esym (Some_inj Ht)) in
      let Es := value_shapeE v ds (andP (andP H).2).1 (esym (Some_inj Hd)) in
      ecast p ('nT[denote (exist _ t (andP H).1)]_(projT2 p)) Es
        (ecast x ('nT[denote x]_(projT1 (projT2 (projT2 v)))) Ex (projT2 (projT2 (projT2 v))))
  | Some _, None => fun H => False_rect _ (notF (andP (andP H).2).2)
  | None, _ => fun H => False_rect _ (notF H)
  end.

Definition value_info_of (o : ValueInfoProto) (Ho : value_info_ok o) (v : {x : Elem & T (denote x)})
  (Ht : value_tensor_type o = Some (sval (projT1 v)))
  (Hd : omap (map int64_to_dim) (value_dims o) = Some (shape_dims v)) : value_info_tensor o Ho :=
  value_type_of (value_tensor_type o) (value_dims o) Ho v Ht Hd.

(** A name found as a node is an output of a node of the graph. **)
Lemma find_vertex_node_output nodes inps inits s n :
  find_vertex (graph_items nodes inps inits) s = [:: node n] ->
  n \in nodes /\ s \in node_outputs n.
Proof.
move=> F; split; first by rewrite -(mem_graph_items_node nodes inps inits); exact: finds_in F.
have : node n \in find_vertex (graph_items nodes inps inits) s by rewrite F mem_head.
by rewrite find_vertexE mem_filter vertex_has_nameE => /andP [].
Qed.

(** The names defined after the nodes are their outputs and the names before. **)
Lemma mem_defined_after defined nodes s :
  s \in defined_after defined nodes = (s \in flatten (map node_outputs nodes)) || (s \in defined).
Proof.
elim: nodes defined => //= n ns IH defined.
by rewrite IH !mem_cat orbCA orbA.
Qed.

(** A defined name is in gamma, and a declaration with the dtype and dims of
its name reads the value as its tensor type. **)
Lemma gamma_ok_mem {dt shn defined gamma} s :
  gamma_ok dt shn defined gamma -> s \in defined -> s \in domf gamma.
Proof. by move=> ok /ok [Hs _]. Qed.

Lemma gamma_ok_output {dt shn defined gamma} (o : ValueInfoProto) (Hn : value_named o) :
  gamma_ok dt shn defined gamma ->
  [/\ input_name o Hn \in defined, value_tensor_type o = dt
    & omap (map int64_to_dim) (value_dims o) = shn (input_name o Hn)] ->
  forall Hs : input_name o Hn \in domf gamma,
    value_tensor_type o = Some (sval (projT1 gamma.[Hs])) /\
    omap (map int64_to_dim) (value_dims o) = Some (shape_dims gamma.[Hs]).
Proof.
move=> ok [sin Ht Hd] Hs; case: (ok _ sin) => Hs' [E1 E2].
have -> : Hs = Hs' by exact: bool_irrelevance.
by rewrite Ht Hd E2; split.
Qed.

(** * Lemmas for the initial gamma_ok **)

(** The names the maps use are the declared ones, conversely. **)
Lemma init_nameE t Ht : tensor_name t = Some (init_name t Ht).
Proof. by case: t Ht => ? ? ? ? ? ? ? [s|]. Qed.

Lemma input_nameE v Hv : value_name v = Some (input_name v Hv).
Proof. by case: v Hv => [[s|] ? ? ?]. Qed.

(** The values the maps are built from have the dtype and dims of their
protos. **)
Lemma shape_dims_tensorProto_elem t (Hs : tensorProtoSized t) :
  shape_dims (tensorProto_elem t Hs) = map int64_to_dim (get_dims t).
Proof.
rewrite /tensorProto_elem; move: (tensorProtoSized_dtype Hs).
case: (tensor_dtype t) => [x|] H //=.
rewrite /shape_dims /= /tensorProto_shape map_dims_type -map_comp.
by apply/eq_in_map => d /(allP (tensorProtoSized_pos _ Hs)) /=; exact: dimc_id.
Qed.

Lemma elem_tensorProto_elem t (Hs : tensorProtoSized t) :
  Some (sval (projT1 (tensorProto_elem t Hs))) = tensor_dtype t.
Proof.
by rewrite /tensorProto_elem; move: (tensorProtoSized_dtype Hs); case: (tensor_dtype t).
Qed.

Lemma shape_dims_value_type_elem o ods H (x : value_type_tensor o ods H) :
  omap (map int64_to_dim) ods = Some (shape_dims (value_type_elem o ods H x)).
Proof.
case: o ods H x => [t|] [ds|] H x;
  [ | by have /and3P [_ _] := H; rewrite eqxx | by have /and3P [] := H | by have /and3P [] := H].
rewrite -[RHS]/(Some (map (fun q : {posnum nat} => q%:num) (tval (value_type_shape ds)))).
by rewrite (value_type_shapeE (andP (andP H).2).1).
Qed.

Lemma shape_dims_value_info_elem v (Hv : value_info_ok v) (x : value_info_tensor v Hv) :
  omap (map int64_to_dim) (value_dims v) = Some (shape_dims (value_info_elem v Hv x)).
Proof. exact: shape_dims_value_type_elem. Qed.

Lemma elem_value_type_elem o ods H (x : value_type_tensor o ods H) :
  Some (sval (projT1 (value_type_elem o ods H x))) = o.
Proof.
by case: o ods H x => [t|] [ds|] H x;
  [ | have /and3P [_ _] := H; rewrite eqxx | have /and3P [] := H | have /and3P [] := H].
Qed.

Lemma elem_value_info_elem v (Hv : value_info_ok v) (x : value_info_tensor v Hv) :
  Some (sval (projT1 (value_info_elem v Hv x))) = value_tensor_type v.
Proof. exact: elem_value_type_elem. Qed.

(** Every value in the maps comes from a proto with that name. **)
Lemma inits_fmap_fnd s H nm v :
  (inits_fmap s H).[? nm] = Some v ->
  exists t : TensorProto, [/\ t \in s, tensor_name t = Some nm & exists Ht, v = tensorProto_elem t Ht].
Proof.
elim: s H => [|t s IH] H /=; first by rewrite fnd_fmap0.
rewrite fnd_set; case: ifP => [/eqP -> [<-] | _ /IH [t' [tin tnm [Ht ->]]]].
- by exists t; split; [exact: mem_head | exact: init_nameE | exists (andP (andP H).1).2].
- by exists t'; split; [rewrite in_cons tin orbT | exact: tnm | exists Ht].
Qed.

Lemma inputs_fmap_fnd vs Hn Hv xs gamma nm v :
  (@inputs_fmap vs Hn Hv xs gamma).[? nm] = Some v ->
  (exists i, value_name (tnth (in_tuple vs) i) = Some nm /\
             v = value_info_elem _ (Hv i) (xs i))
  \/ gamma.[? nm] = Some v.
Proof.
rewrite /inputs_fmap; elim: (ord_enum _) => [|i l IH] /=; first by right.
rewrite fnd_set; case: ifP => [/eqP -> [<-] | _ /IH //].
by left; exists i; split => //; exact: input_nameE.
Qed.

(** The initial map satisfies the invariant. **)
Lemma gamma_ok_initial nodes inps inits outs Hn Hv (xs : {dffun forall i : 'I_(size inps),
    value_info_tensor (tnth (in_tuple inps) i) (Hv i)}) H :
  graph_acyclic nodes inps inits ->
  all (fun v => value_tensor_type v == outputs_dtype outs) inps ->
  all (fun t => tensor_dtype t == outputs_dtype outs) inits ->
  gamma_ok (outputs_dtype outs) (infer_dims nodes inps inits)
    (pmap value_name inps ++ pmap tensor_name inits)%SEQ
    (@inputs_fmap inps Hn Hv xs (inits_fmap inits H)).
Proof.
move=> ac /allP idt /allP tdt s sin.
have Hs : s \in domf (@inputs_fmap inps Hn Hv xs (inits_fmap inits H)).
  move: sin; rewrite mem_cat !mem_pmap => /orP [/mapP [v vin vs] | /mapP [t tin ts]].
  - exact: inputs_fmap_dom vin (esym vs).
  - exact: inits_inputs_fmap_dom tin (esym ts).
exists Hs; have := in_fnd Hs.
case/inputs_fmap_fnd => [[i [inm ->]] | /inits_fmap_fnd [t [tin tnm [Ht ->]]]].
- have iin : tnth (in_tuple inps) i \in inps := mem_tnth i (in_tuple inps).
  split; first by rewrite elem_value_info_elem; apply/eqP/idt.
  have := shape_dims_value_info_elem _ (Hv i) (xs i).
  have := Hv i; rewrite /value_info_ok => /and3P [_ _].
  case E: (value_dims _) => [ds|] //= _ [<-].
  by rewrite (infer_dims_input _ _ _ _ _ _ ac iin inm E).
- split; first by rewrite elem_tensorProto_elem; apply/eqP/tdt.
  by rewrite (infer_dims_initialiser _ _ _ _ _ ac tin tnm) shape_dims_tensorProto_elem.
Qed.

(** * The facts interp_model reads off a well-formed model **)
Section ModelFacts.
Context {ir : option int64} {op : OperatorSetIdProto} {pn pv dom : option string}
  {mv : option int64} {doc : option string}
  {nodes : seq NodeProto} {nm : option string} {inits : seq TensorProto}
  {sp : seq SparseTensorProto} {ds : option string} {inps outs vi : seq ValueInfoProto}
  {qa : seq TensorAnnotation} {mp : seq StringStringEntryProto}
  {meta : seq StringStringEntryProto} {tr : seq TrainingInfoProto}
  {fs : seq FunctionProto} {cfg : seq DeviceConfigurationProto}.
Variable Hm : model_well_formed
  (ModelProto_constructor ir [:: op] pn pv dom mv doc
     (Some (GraphProto_constructor nodes nm inits sp ds inps outs vi qa mp)) meta tr fs cfg).

Let names := (pmap value_name inps ++ pmap tensor_name inits)%SEQ.

(** Every initialiser is named and sized. **)
Lemma model_inits_ok : all (fun t => tensorNamed t && tensorProtoSized t) inits.
Proof.
have := Hm => /= /andP [_] /and5P [_ _ _ /allP init_ok _].
apply/allP => t /init_ok /and3P [_ -> Hn]; rewrite andbT.
by case: t Hn => ? ? ? ? ? ? ? [].
Qed.

(** The graph is acyclic; the nodes are in topological order, well typed,
and integral over an integer dtype. **)
Lemma model_acyclic : graph_acyclic nodes inps inits.
Proof. by have := Hm => /= /andP [_] /and5P []. Qed.

Lemma model_topo : topo_sorted names nodes.
Proof. by have := model_acyclic => /andP []. Qed.

Lemma model_dims : all (node_dims_ok (infer_dims nodes inps inits)) nodes.
Proof. by have := Hm => /= /andP [_] /and5P [_ _ _ _ /and3P []]. Qed.

Lemma model_int :
  all (fun n => (outputs_dtype outs == Some FLOAT_TensorProto) || gemm_int_attrs_ok (get_attributes n)) nodes.
Proof. by have := Hm => /= /andP [_] /and5P [_ _ _ _ /and3P []]. Qed.

(** Inputs and initialisers have the model dtype. **)
Lemma model_inputs_dt : all (fun v => value_tensor_type v == outputs_dtype outs) inps.
Proof.
have := Hm => /= /andP [_] /and5P [_ _ /allP decl _ _].
by apply/allP => v vin; have := decl v; rewrite mem_cat vin => /(_ isT) /and3P [_ _ /and4P [_ -> _ _]].
Qed.

Lemma model_inits_dt : all (fun t => tensor_dtype t == outputs_dtype outs) inits.
Proof.
have := Hm => /= /andP [_] /and5P [_ _ _ /allP init_ok _].
by apply/allP => t /init_ok /and3P [].
Qed.

(** Every graph output is a node output, of the model dtype and of the dims
its producer gives it. **)
Lemma model_outputs_ok (i : 'I_(size outs)) (Hn : value_named (tnth (in_tuple outs) i)) :
  [/\ input_name _ Hn \in defined_after names nodes,
      value_tensor_type (tnth (in_tuple outs) i) = outputs_dtype outs
    & omap (map int64_to_dim) (value_dims (tnth (in_tuple outs) i))
      = infer_dims nodes inps inits (input_name _ Hn)].
Proof.
have := Hm => /= /andP [_] /and5P [_ /allP onode /allP decl _ /and3P [_ /allP odims _]].
set o := tnth _ _.
have oin : o \in outs by exact: mem_tnth.
have := decl o; rewrite mem_cat oin orbT => /(_ isT) /and3P [_ _ /and4P [_ /eqP Hdt _ _]].
have nameE := input_nameE o Hn.
split=> //.
- move: (onode o oin); rewrite nameE.
  case F: (find_vertex _ _) => [|[n|? |? |?] [|? ?]] // _.
  have [nin sout] := find_vertex_node_output _ _ _ _ _ F.
  rewrite mem_defined_after; apply/orP; left; apply/flattenP.
  by exists (node_outputs n) => //; apply/mapP; exists n.
- move: (odims o oin); rewrite nameE; case: (value_dims o) => [ds'|] //= /eqP ->.
  by rewrite /= -/(infer_dims nodes inps inits).
Qed.

End ModelFacts.

(** The semantics of a well-formed model: the values of its graph outputs,
with the declared tensor types, on the values of its graph inputs. **)
Definition interp_model (m : ModelProto) (Hm : model_well_formed m)
  (inputs : {dffun forall i : 'I_(size (graph_inputs m)),
               value_info_tensor (tnth (in_tuple (graph_inputs m)) i)
                 (input_value_info_ok Hm (mem_tnth i (in_tuple (graph_inputs m))))})
  : {dffun forall i : 'I_(size (graph_outputs m)),
         value_info_tensor (tnth (in_tuple (graph_outputs m)) i)
                           (output_value_info_ok Hm (mem_tnth i (in_tuple (graph_outputs m))))} :=
match m as m0 return
  forall Hm0 : model_well_formed m0,
  {dffun forall i : 'I_(size (graph_inputs m0)),
     value_info_tensor (tnth (in_tuple (graph_inputs m0)) i)
       (input_value_info_ok Hm0 (mem_tnth i (in_tuple (graph_inputs m0))))} ->
  {dffun forall i : 'I_(size (graph_outputs m0)),
     value_info_tensor (tnth (in_tuple (graph_outputs m0)) i)
       (output_value_info_ok Hm0 (mem_tnth i (in_tuple (graph_outputs m0))))}
with
| ModelProto_constructor ir [:: op] pn pv dom mv doc
    (Some (GraphProto_constructor nodes nm inits sp ds inps outs vi qa mp)) meta tr fs cfg =>
  fun Hm inputs =>
    let m := ModelProto_constructor ir [:: op] pn pv dom mv doc
               (Some (GraphProto_constructor nodes nm inits sp ds inps outs vi qa mp)) meta tr fs cfg in
    let gamma := inits_fmap inits (model_inits_ok Hm) in
    let gamma := inputs_fmap (fun i => input_value_named Hm (mem_tnth i (in_tuple (graph_inputs m))))
                             (fun i => input_value_info_ok Hm (mem_tnth i (in_tuple (graph_inputs m))))
                             inputs gamma in
    let g := interp_nodes (outputs_dtype outs) (infer_dims nodes inps inits)
                          (pmap value_name inps ++ pmap tensor_name inits)%SEQ gamma nodes
                          (model_topo Hm) (model_dims Hm) (model_int Hm)
                          (gamma_ok_initial _ _ _ _ _ _ _ _ (model_acyclic Hm) (model_inputs_dt Hm) (model_inits_dt Hm)) in
    @finfun _ (fun i : 'I_(size (graph_outputs m)) =>
                 value_info_tensor (tnth (in_tuple (graph_outputs m)) i)
                   (output_value_info_ok Hm (mem_tnth i (in_tuple (graph_outputs m)))))
      (fun i : 'I_(size (graph_outputs m)) =>
       let o := tnth (in_tuple (graph_outputs m)) i in
       let Hn := output_value_named Hm (mem_tnth i (in_tuple (graph_outputs m))) in
       let Hout := model_outputs_ok Hm i Hn in
       let Hs := gamma_ok_mem (input_name o Hn) (svalP g) (and3proj1 Hout) in
       value_info_of o (output_value_info_ok Hm (mem_tnth i (in_tuple (graph_outputs m))))
         (sval g).[Hs]
         (proj1 (gamma_ok_output o Hn (svalP g) Hout Hs))
         (proj2 (gamma_ok_output o Hn (svalP g) Hout Hs)))
| ModelProto_constructor _ [::] _ _ _ _ _ _ _ _ _ _ => fun Hm _ => False_rect _ (notF Hm)
| ModelProto_constructor _ [:: _] _ _ _ _ _ None _ _ _ _ => fun Hm _ => False_rect _ (notF Hm)
| ModelProto_constructor _ (_ :: _ :: _) _ _ _ _ _ _ _ _ _ _ => fun Hm _ => False_rect _ (notF Hm)
end Hm inputs.


(** The input semantics of a network type, one tensor per declared input. **)
Definition input_sem (y : NetworkType Elem) :
  InputSemantics denote y -> TensorsSemantics denote (inputs Elem y) :=
  match y with networkType _ _ => id end.

(** The network type's inputs line up one-to-one with the graph inputs. **)
Lemma network_dim_match_inputs_size {y : NetworkType Elem} {m : ModelProto} :
  network_dim_match m y -> size (graph_inputs m) = size (inputs Elem y).
Proof.
case: y => [[inps Hin] [outs Hout]] /= /andP [+ _].
by rewrite all2E => /andP [/eqP].
Qed.

(** The declared input at the position of a graph input has its type. **)
Lemma network_dim_match_input {y : NetworkType Elem} {m : ModelProto}
  (H : network_dim_match m y) (i : 'I_(size (graph_inputs m))) :
  value_has_type (tnth (in_tuple (inputs Elem y)) (cast_ord (network_dim_match_inputs_size H) i))
                 (tnth (in_tuple (graph_inputs m)) i).
Proof.
move: (network_dim_match_inputs_size H) => E; move: i E H.
case: y => [[inps Hin] [outs Hout]] /= i E /andP [+ _].
rewrite all2E => /andP [_ /all_nthP same].
set v := tnth _ i; set d := tnth _ _.
have := same (d, v) i.
rewrite nth_zip_cond size_zip -E minnn ltn_ord /= => /(_ isT).
rewrite -[nth d inps i](tnth_nth d (in_tuple inps) (cast_ord E i)).
by rewrite -[nth v _ i](tnth_nth v (in_tuple (graph_inputs m)) i).
Qed.

(** A value declared with the dtype and dims of a network tensor type has
that tensor type. **)
Lemma value_type_tensorE (x : DataType_TensorProto) (Hx : x \in supported_types) k
  (dims : {posnum nat} ^ k) o ods H :
  o = Some x ->
  omap (map int64_to_dim) ods = Some (map (fun q : {posnum nat} => q%:num) (tval dims)) ->
  'nT[denote (exist _ x Hx)]_(dims) = value_type_tensor o ods H.
Proof.
case: o ods H => [t|] [ds|] H // [E] [Ed]; subst t.
rewrite /value_type_tensor (bool_irrelevance (andP H).1 Hx).
have /and3P [_ dpos _] := H.
have E : existT (fun k : nat => {ffun 'I_k -> {posnum nat}}) k dims = existT _ (size ds) (value_type_shape ds).
  by rewrite (dims_typeE _ _ _ (value_type_shapeE dpos)); apply: dims_typeE; rewrite Ed.
have C (s s' : {k : nat & {ffun 'I_k -> {posnum nat}}}) :
  s = s' -> 'nT[denote (exist _ x Hx)]_(projT2 s) = 'nT[denote (exist _ x Hx)]_(projT2 s').
  by move=> ->.
exact: C E.
Qed.

Lemma value_has_type_tensor (d : TensorType Elem) (v : ValueInfoProto) (Hv : value_info_ok v) :
  value_has_type d v -> TensorSemantics denote d = value_info_tensor v Hv.
Proof.
case: d => [[x Hx] [k dims]] /andP [/eqP Et /eqP Ed].
exact: value_type_tensorE Et Ed.
Qed.

(** The semantic inputs of a network type as the inputs of the model: the
tensor at the position of each graph input, cast to its declared type. **)
Definition input_sem_to_input (y : NetworkType (ElementType syntax_inst))
  (m : well_formed_model y) (inp : InputSemantics denote y)
  : {dffun forall i : 'I_(size (graph_inputs (tag m))),
         value_info_tensor (tnth (in_tuple (graph_inputs (tag m))) i)
           (input_value_info_ok (andP (valP m)).2 (mem_tnth i (in_tuple (graph_inputs (tag m)))))} :=
  @finfun _ (fun i : 'I_(size (graph_inputs (tag m))) =>
               value_info_tensor (tnth (in_tuple (graph_inputs (tag m))) i)
                 (input_value_info_ok (andP (valP m)).2 (mem_tnth i (in_tuple (graph_inputs (tag m))))))
    (fun i : 'I_(size (graph_inputs (tag m))) =>
       let Hd := (andP (valP m)).1 in
       ecast X X (value_has_type_tensor _ _ _ (network_dim_match_input Hd i))
         (input_sem y inp (cast_ord (network_dim_match_inputs_size Hd) i))).


(** The position of a member of a sequence. **)
Definition mem_ord {A : eqType} {s : seq A} {x : A} (xin : x \in s) : 'I_(size s) :=
  Ordinal (etrans (index_mem x s) xin).

Lemma tnth_mem_ord {A : eqType} {s : seq A} {x : A} (xin : x \in s) :
  tnth (in_tuple s) (mem_ord xin) = x.
Proof. by rewrite (tnth_nth x) /= nth_index. Qed.

(** The index in the graph outputs that a node output sits at. **)
Definition node_output_index {y : NetworkType Elem} {n : well_formed_model y}
  {u : string} {d : TensorType Elem} :
  nodeOutput y n u d -> 'I_(size (graph_outputs (tag n))) :=
  match n with exist m _ => fun out => mem_ord (andP (svalP out)).1 end.

(** The graph output at that index is named u and has the type d. **)
Lemma node_output_indexP {y : NetworkType Elem} {n : well_formed_model y}
  {u : string} {d : TensorType Elem} (out : nodeOutput y n u d) :
  let v := tnth (in_tuple (graph_outputs (tag n))) (node_output_index out) in
  value_info_name v = u /\ value_has_type d v.
Proof.
case: n out => m pf [v Hv] /=; rewrite tnth_mem_ord.
by have /and3P [_ /eqP] := Hv.
Qed.

Definition modelTensorProto (y : NetworkType (ElementType syntax_inst))
  (n : Model syntax_inst y) (inp : InputSemantics denote y)
  (d : TensorType (ElementType syntax_inst)) (u : NodeOutputName syntax_inst)
  (out : NodeOutput syntax_inst n u d) : TensorSemantics denote d :=
  let Hm := (andP (valP n)).2 in
  (** the index in the graph outputs that u sits at, from out **)
  let i := node_output_index out in
  (** the interpreted outputs, as a function, at i **)
  let out_i := interp_model (tag n) Hm (input_sem_to_input y n inp) i in
  (** out_i's type is the semantics of d, since the output at i has type d **)
  let out_iE := value_has_type_tensor d _
    (output_value_info_ok Hm (mem_tnth i (in_tuple (graph_outputs (tag n)))))
    (node_output_indexP out).2 in
  ecast X X (esym out_iE) out_i.

(* TODO: Make this so that it extracts model to a maths function over mathcomp tensors and applies it to inputSemantics. Must cascade input through entire graph.
 Map model to a function over mathcomp tensor **)

(* Definition modelTensorProto (y : NetworkType (ElementType syntax_inst)) *)
(* (n : Model syntax_inst y) (inp : InputSemantics denote y) *)
(* (d : TensorType (ElementType syntax_inst)) (u : NodeOutputName syntax_inst) *)
(* (out : NodeOutput syntax_inst n u d) : TensorSemantics denote d. *)
(* Proof. *)
(* case: y n inp out => [[inps inps_gt0] [outs outs_gt0]] [m /andP [dm wf]] /= inp. *)
(* case=> o /and3P [oin /eqP oname otype]. *)
(* case: m dm wf oin => ir opset prod_name prod_vers domain model_version doc *)
(*   [[nodes name initialisers sparse_initialisers doc_string inputs outputs value_info *)
(*     quantisation metadata_props]|//] metadata training functions config dm wf oin /=. *)
(* move: dm wf oin => /= dm wf oin. *)
(* (** [vertices] of onnx_evaluator **) *)
(* move Hv: (graph_items nodes inputs initialisers) => vertices. *)
(* case/and5P: wf => acyc /allP outs_one /allP decl /allP init_ok /and3P [/allP nodes_ok /allP o_sh _]. *)
(* have vop n : node n \in vertices -> valid_op n. *)
(*   by rewrite -Hv mem_graph_items_node => /nodes_ok /node_dims_ok_valid_op. *)
(* have sized t : tensor t \in vertices -> tensorProtoSized t. *)
(*   by rewrite -Hv mem_graph_items_tensor => /init_ok /and3P []. *)
(* have in_inputs i : input i \in vertices -> i \in inputs. *)
(*   by rewrite -Hv mem_graph_items_input. *)
(* have no_output v : output v \in vertices = false. *)
(*   by rewrite -Hv output_notin_graph_items. *)
(* have Hsz : size inps = size inputs. *)
(*   by move/andP: dm => [+ _]; rewrite all2E => /andP [/eqP]. *)
(* (** every vertex has the tensor type of its name's declared dims, in the dtype of d **) *)
(* pose shn := infer_dims nodes inputs initialisers. *)
(* pose ty (w : vertex) := @tensorType Elem (tensorTypes _ d) *)
(*   (dims_type (odflt [::] (shn (seq.head ""%string (vnames w))))). *)
(* have nodes_sh : all (node_dims_ok shn) nodes by apply/allP. *)
(* (** the graph dtype is the dtype of d **) *)
(* have dtE : (if outputs is o' :: _ then value_tensor_type o' else None) = *)
(*            Some (tag (tensorTypes _ d)). *)
(*   move: (decl o); rewrite mem_cat oin orbT => /(_ isT) /and3P [_ _ /and4P [_ /eqP <- _ _]]. *)
(*   by case/andP: otype => /eqP. *)
(* have elemE (x : Elem) : Some (tag x) = Some (tag (tensorTypes _ d)) -> x = tensorTypes _ d. *)
(*   by move=> [] /val_inj. *)
(* (** every vertex found under a name has that name's dims **) *)
(* have sh_find its i w : {subset its <= vertices} -> find_vertex its i = [:: w] -> *)
(*     shn (seq.head ""%string (vnames w)) = shn i. *)
(*   by move=> sub F; apply: (graph_dims_find nodes inputs initialisers _ _ _ _ nodes_sh _ F); rewrite Hv. *)
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
(*       move/String.eqb_eq: sG => sE; subst s. *)
(*       case: ins win ac child found => [|a [|b [|c [|? ?]]]] //= win ac child found _. *)
(*       * (** two inputs **) *)
(*         have ina : a \in [:: a; b] by rewrite inE eqxx. *)
(*         have inb : b \in [:: a; b] by rewrite !inE eqxx orbT. *)
(*         case Fa: (find_vertex its a) => [|va [|? ?]]; *)
(*           try by exfalso; case: (found a ina) => ?; rewrite Fa. *)
(*         case Fb: (find_vertex its b) => [|vb [|? ?]]; *)
(*           try by exfalso; case: (found b inb) => ?; rewrite Fb. *)
(*         (** node_dims_ok: a and b are matrices with matching inner dimension, and the *)
(*             output is declared as [N; P] **) *)
(*         have Nn : node_dims_ok shn (NodeProto_constructor [:: a; b] n_outs n_name (Some """Gemm""") *)
(*                                        n_dom n_ov attrs n_doc n_meta n_x). *)
(*           by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*         move: (child a va ina Fa) (child b vb inb Fb). *)
(*         rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) /vnames /node_outputs. *)
(*         case/node_dims_ok_gemm2: Nn => da [db [ds [-> -> /gemm_out_dimsP + ->]]]. *)
(*         case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB] [sa sb inner -> _] A B. *)
(*         apply: (@tensor_of_mx _ _ (mx_shape_num (dim_pos (trans_dims tA (mat_of_dims da)).1) *)
(*                                  (dim_pos (trans_dims tB (mat_of_dims db)).2))). *)
(*         pose ops := gemm_ops alpha. *)
(*         (** transpose A and B as transA, transB say, then A' * B' **) *)
(*         move: inner A B; rewrite /trans_dims. *)
(*         case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB] inner A B; *)
(*           first [ exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B))) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B))) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T)) *)
(*                 | exact (gemm_2_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 (tensor_mx _ sa A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T)) ]. *)
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
(*         have Nn : node_dims_ok shn (NodeProto_constructor [:: a; b; c] n_outs n_name (Some """Gemm""") *)
(*                                        n_dom n_ov attrs n_doc n_meta n_x). *)
(*           by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*         move: (child a va ina Fa) (child b vb inb Fb) (child c vc inc Fc). *)
(*         rewrite /ty (sh_find _ _ _ sub Fa) (sh_find _ _ _ sub Fb) (sh_find _ _ _ sub Fc). *)
(*         rewrite /vnames /node_outputs. *)
(*         case/node_dims_ok_gemm3: Nn => da [db [dc [ds [-> -> -> /gemm_out_dimsP + ->]]]]. *)
(*         case: (get_gemm_attributes attrs) => [[[alpha beta] tA] tB] [sa sb inner -> cok] A B C. *)
(*         have sc : (size dc <= 2)%nat by move: cok; case: (mat_of_dims dc) => ? ? /andP []. *)
(*         apply: (@tensor_of_mx _ _ (mx_shape_num (dim_pos (trans_dims tA (mat_of_dims da)).1) *)
(*                                  (dim_pos (trans_dims tB (mat_of_dims db)).2))). *)
(*         pose ops := gemm_ops alpha. *)
(*         pose beta' := (gemm_ops beta).2. *)
(*         (** C broadcast to (N, P): a dimension of size 1 always reads index 0 **) *)
(*         move: inner A B; rewrite /trans_dims. *)
(*         case: (Z_of_int64 tA) => [|pA|pA]; case: (Z_of_int64 tB) => [|pB|pB] inner A B; *)
(*           first [ exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)) *)
(*                            (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)) *)
(*                            (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A) *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T) *)
(*                            (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j))) *)
(*                 | exact (gemm_3_inputs ops.1.1.1 ops.1.1.2 ops.1.2 ops.2 beta' (tensor_mx _ sa A)^T *)
(*                            (castmx (congr1 dimc (esym inner), erefl) (tensor_mx _ sb B)^T) *)
(*                            (\matrix_(i, j) tensor_mx _ sc C (bidx _ i) (bidx _ j))) ]. *)
(*     + case: ifP => // sR. *)
(*       (** Relu: the same dims as its input, whatever the rank **) *)
(*       move/String.eqb_eq: sR => sE; subst s. *)
(*       case: ins win ac child found => [|a [|? ?]] //= win ac child found _. *)
(*       have ina : a \in [:: a] by rewrite inE eqxx. *)
(*       case Fa: (find_vertex its a) => [|va [|? ?]]; *)
(*         try by exfalso; case: (found a ina) => ?; rewrite Fa. *)
(*       have Nn : node_dims_ok shn (NodeProto_constructor [:: a] n_outs n_name (Some """Relu""") *)
(*                                      n_dom n_ov attrs n_doc n_meta n_x). *)
(*         by apply: (allP nodes_sh); move: (sub _ win); rewrite -Hv mem_graph_items_node. *)
(*       move: (child a va ina Fa); rewrite /ty (sh_find _ _ _ sub Fa) /vnames /node_outputs. *)
(*       move/node_dims_ok_relu: Nn => -> A. *)
(*       exact (@Tensor _ _ _ _ _ (op_relu relu_ops.1 relu_ops.2 (tensor_val A))). *)
(*   - (** Tensor: just return itself **) *)
(*     have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor. *)
(*     have := sized t (sub _ win). *)
(*     have tsh : if tensor_name t is Some s *)
(*                then infer_dims nodes inputs initialisers s == Some (map int64_to_dim (get_dims t)) *)
(*                else false. *)
(*       move: (init_ok t tin) => /and3P [_ _]; case E: (tensor_name t) => [s|] // _. *)
(*       by rewrite (infer_dims_initialiser _ _ _ _ _ acyc tin E) eqxx. *)
(*     move: (init_ok t tin) => /and3P [/eqP tdt _ _]. *)
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
(*       (** T has the type of t's dims **) *)
(*       have xE : exist _ x xin = tensorTypes _ d. *)
(*         by apply: elemE; rewrite -dtE -tdt /= E. *)
(*       move: T; rewrite xE /ty /vnames /=. *)
(*       case Etn: tn tsh => [s|] //= /eqP; rewrite -/shn => -> T. *)
(*       exact (@eq_rect _ (existT _ (size dims) shape) *)
(*                (fun ds => TensorSemantics denote (@tensorType Elem (tensorTypes _ d) ds)) *)
(*                T _ (dims_typeE _ _ _ shapeE)). *)
(*     apply: theoryTensorProto. *)
(*     have tnamed : tn by move: tsh; destruct tn. *)
(*     pose q := qtensor_pi (TensorProto_constructor dims (Some dt) seg fd i32 sd i64 tn *)
(*                                                   ds rd ed dl dd u64 mp). *)
(*     have qsized : tensorProtoSized q && tensorNamed q. *)
(*       rewrite /q /= /storage_of. *)
(*       case: x E Hsize xin => // E Hsize xin; *)
(*         [have HZ := DataType_float E | have HZ := DataType_int32 E | have HZ := DataType_int64 E]; *)
(*         by rewrite HZ /= E Hsize dpos /=. *)
(*     exists (exist _ q qsized). *)
(*     rewrite /= /q {qsized q tnamed}. *)
(*     have Edims : dims = map (tnth (in_tuple dims)) (fintype.enum 'I_(size dims)). *)
(*       by rewrite map_tnth_enum. *)
(*     case: x E Hsize xin => // E Hsize xin; *)
(*       [move: (DataType_float E) | move: (DataType_int32 E) | move: (DataType_int64 E)] => Z; *)
(*       rewrite /= /storage_of Z /= E eqxx /= !andbT; *)
(*       rewrite -map_comp; apply/eqP; *)
(*       rewrite {1}Edims; *)
(*       by rewrite -map_comp enumT; apply: eq_map => i /=; rewrite ffunE insubdK //; exact: pos i. *)
(*   - (** Input: the user inputs are positional, take the one at v's position **) *)
(*     have vin := in_inputs v (sub _ win). *)
(*     have ilt : (seq.index v inputs < size inps)%nat by rewrite Hsz index_mem. *)
(*     (** network_dim_match: the input at v's position has v's declared type **) *)
(*     have vt_ok : value_has_type (tnth (in_tuple inps) (Ordinal ilt)) v. *)
(*       move/andP: dm => [+ _]; rewrite all2E => /andP [_ /all_nthP same]. *)
(*       have := same (tnth (in_tuple inps) (Ordinal ilt), v) (seq.index v inputs). *)
(*       rewrite nth_zip_cond size_zip -Hsz minnn ilt => /(_ isT) /=. *)
(*       by rewrite nth_index // -(tnth_nth _ (in_tuple inps) (Ordinal ilt)). *)
(*     move: (inp (Ordinal ilt)) vt_ok. *)
(*     case: (tnth (in_tuple inps) (Ordinal ilt)) => ei [ki dsi] /= X /andP [/eqP vdt /eqP vdims]. *)
(*     have eiE : ei = tensorTypes _ d. *)
(*       apply: elemE; rewrite -vdt -dtE. *)
(*       by move: (decl v); rewrite mem_cat vin => /(_ isT) /and3P [_ _ /and4P [_ /eqP]]. *)
(*     (** X has the type of the input's declared dims **) *)
(*     have vsh : if (value_name v, value_dims v) is (Some s, Some ds) *)
(*                then infer_dims nodes inputs initialisers s == Some (map int64_to_dim ds) *)
(*                else false. *)
(*       move: (decl v); rewrite mem_cat vin => /(_ isT) /and3P [_ _ /and4P [_ _]]. *)
(*       case Evn: (value_name v) => [s|] // _; case Evd: (value_dims v) => [ds|] // _. *)
(*       by rewrite (infer_dims_input _ _ _ _ _ _ acyc vin Evn Evd) eqxx. *)
(*     move: vsh vdims. *)
(*     rewrite /ty /vnames /= -eiE. *)
(*     case: (value_name v) => [nm|] //=. *)
(*     case: (value_dims v) => [l|] //= /eqP; rewrite -/shn => -> [vdims]. *)
(*     exact (@eq_rect _ (existT _ ki dsi) *)
(*              (fun ds => TensorSemantics denote (@tensorType Elem ei ds)) *)
(*              X _ (dims_typeE _ _ _ (esym vdims))). *)
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
(* (** Y has the type of the output's declared dims, which are d's **) *)
(* move: Y; rewrite /ty (sh_find _ _ _ (fun _ x => x) F) => Y. *)
(* set ov := ValueInfoProto_constructor (Some nm) ot od om in oin otype *. *)
(* move: (o_sh _ oin) otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //. *)
(* case: (value_dims ov) => [l|] //= /eqP sh /andP [_ /eqP [odims]]. *)
(* have HT : tensorDims _ d = dims_type (map int64_to_dim l). *)
(*   by case: (tensorDims _ d) odims => kd dsd /= odims; exact: dims_typeE (esym odims). *)
(* have dE : d = @tensorType Elem (tensorTypes _ d) (tensorDims _ d) by clear -d; case: d. *)
(* rewrite /shn sh in Y. *)
(* exact (@eq_rect _ _ (TensorSemantics denote) *)
(*          (@eq_rect _ (dims_type (map int64_to_dim l)) *)
(*             (fun ds => TensorSemantics denote (@tensorType Elem (tensorTypes _ d) ds)) *)
(*             Y _ (esym HT)) *)
(*          _ (esym dE)). *)
(* Defined. *)

Definition tle (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_le (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) <= (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) <= (\val t2 ij.1 ij.2)].
Defined.

Definition tlt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_lt (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) < (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) < (\val t2 ij.1 ij.2)].
Defined.

Definition tge (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_ge (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) >= (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) >= (\val t2 ij.1 ij.2)].
Defined.

Definition tgt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof.
case: d => [[/= [] //= Px]] [k dims] /= t1 t2.
exact: [forall ij, binary_gt (\val t1 ij.1 ij.2) (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) > (\val t2 ij.1 ij.2)].
exact: [forall ij, (\val t1 ij.1 ij.2) > (\val t2 ij.1 ij.2)].
Defined.

Definition teq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Proof. case: d => [[/= [] //= Px]] [k dims] /= t1 t2; exact: (t1 == t2). Qed.

Definition tneq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d :=
  fun t1 t2 =>
  negb (teq d t1 t2).

Definition tneg (d : TensorType (ElementType syntax_inst)) : TensorOp1 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t.
exact: (@Tensor _ _ dims _ float32 (map_mx (b32_mult BinarySingleNaN.mode_NE default_minus_one) (\val t))).
exact: (@Tensor _ _ dims _ int32 (map_mx (fun h1 => int32_of_Z (- (Z_of_int32 h1))) (\val t))).
exact: (@Tensor _ _ dims _ int64 (map_mx (fun h1 => int64_of_Z (- (Z_of_int64 h1))) (\val t))).
Defined.

Definition tadd (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
case: d => [[[]]] //= type_in [k dims] t u.
exact: (@Tensor _ _ dims _ float32 (map2_mx (b32_plus BinarySingleNaN.mode_NE) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int32 (map2_mx (fun h1 h2 => int32_of_Z
                                                       ((Z_of_int32 h2) + (Z_of_int32 h1))) (\val t) (\val u))).
exact: (@Tensor _ _ dims _ int64 (map2_mx (fun h1 h2 => int64_of_Z ((Z_of_int64 h1) + (Z_of_int64 h2))) (\val t) (\val u))).
Defined.

(** TODO: The zero_tensor needs to be reshaped **)
Definition tmul (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
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
      le := tle;
      lt := tlt;
      ge := tge;
      gt := tgt;
      eq := teq;
      neq := tneq;
      neg := tneg;
      add := tadd;
      mul := tmul;
  |}.
