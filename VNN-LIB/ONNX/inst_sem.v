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

(* --- Converting between the mathcomp tensor interface and TensorProto ---
   'nT[R]_(dims) is definitionally a column vector 'M[R]_(prod dims, 1)
   (the covariant-dims product is empty, i.e. 1 -- `rewrite big_ord0` is
   what exposes that), so building/reading one is just building/reading a
   flat, row-major list of length \prod_i (dims i)%:num. NB: bare `enum`
   is ambiguous once ONNXEvaluator.onnx_evaluator is imported (it also
   exports a constructor literally named `enum`, from the ProtobufConverter
   IR type, which takes a string -- hence `fintype.enum` everywhere below. *)

(* Definition build_tensor {R : eqType} {k : nat} (dims : {posnum nat}^k) *)
(*   (data : seq R) (H : size data = \prod_(i < k) (dims i)%:posnum) : 'nT[R]_(dims). *)
(* Proof. *)
(* apply: Tensor; rewrite big_ord0. *)
(* exact: (\col_i tnth (in_tuple data) (cast_ord (esym H) i)). *)
(* Defined. *)

(* Definition read_tensor {R : eqType} {k : nat} (dims : {posnum nat}^k) (t : 'nT[R]_(dims)) *)
(*   : seq R := *)
(*   let cols_eq : \prod_(j < 0) ([tuple] j)%:posnum = 1%R := big_ord0 _ _ _ _ in *)
(*   [seq val t i (cast_ord (esym cols_eq) ord0) | i <- fintype.enum 'I_(\prod_(l < k) (dims l)%:num)]. *)

(* Definition int32_zero : int32 := (Byte.x00, Byte.x00, Byte.x00, Byte.x00). *)
(* Definition int64_zero : int64 := *)
(*   (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00). *)

(* Definition nat_to_int64 (n : nat) : int64 := int64_of_Z (Z.of_nat n). *)

(* Definition dims_of_shape {k : nat} (dims : {posnum nat}^k) : list int64 := *)
(*   [seq nat_to_int64 (dims i)%:num | i <- fintype.enum 'I_k]. *)

(* Definition string_to_bytes (s : string) : bytes := *)
(*   odflt nil (bytes_of_string (list_ascii_of_string s)). *)

(* (* ONNX's numeric DataType codes (1=FLOAT, 6=INT32, 7=INT64, 8=STRING, *)
(*    11=DOUBLE, 13=UINT64 -- the ones op_gemm.v/op_relu.v already match on). *) *)
(* Definition Semantics_to_TensorProto (d : TensorType Elem) *)
(*   : TensorSemantics denote d -> qTensor. *)
(* Proof. *)
(* case: d => [[x Px] [k dims]] /=. *)
(* case: x Px => //= Px v. *)
(* - exact: (\pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 1) None *)
(*             (read_tensor dims v) nil nil nil None None None nil None nil nil nil)). *)
(* - exact: \pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 6) None *)
(*             nil (read_tensor dims v) nil nil None None None nil None nil nil nil). *)
(* - exact: \pi_qTensor (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 7) None *)
(*             nil nil nil (read_tensor dims v) None None None nil None nil nil nil). *)
(* Defined. *)

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

(* TODO: Make this so that it extracts model to a maths function over mathcomp tensors and applies it to inputSemantics. Must cascade input through entire graph.
 Map model to a function over mathcomp tensor **)
Definition modelTensorProto (y : NetworkType (ElementType syntax_inst))
(n : Model syntax_inst y) (inp : InputSemantics denote y)
(d : TensorType (ElementType syntax_inst)) (u : NodeOutputName syntax_inst)
(out : NodeOutput syntax_inst n u d) : TensorSemantics denote d.
Admitted.

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
