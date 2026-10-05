From ONNXFormalization.ONNXConverter Require Import model.

From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.

Definition supported_types : seq DataType_TensorProto :=
  [:: FLOAT_TensorProto; INT32_TensorProto; INT64_TensorProto].

Definition Elem : eqType := { x in supported_types }.

Definition nodeOutput (y : NetworkType Elem) (m : ModelProto) (s : string)
(d : TensorType Elem) : eqType :=
  NodeProto.


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

Definition node_output_names (n : NodeProto) : list string :=
  match n with
  | NodeProto_constructor _ outp _ _ _ _ _ _ _ _ => outp
  end.

(* the NodeProto that actually computes the named output u, if any *)
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
Definition mOutputs (y : NetworkType Elem) (m : ModelProto) :
  {dffun forall i : 'I_(size (outputs Elem y)),
{u : string & nodeOutput y m u (tnth (in_tuple (outputs Elem y)) i)}} :=
  finfun (fun i : 'I_(size (outputs Elem y)) =>
    let u := nth ""%string (map value_info_name (graph_outputs m)) (nat_of_ord i) in
    existT _ u (producing_node m u)).

Definition is_iso (y1 y2 : NetworkType Elem) (m1 : ModelProto)
(H : NetworkShapesMatch y1 y2) (m2 : ModelProto) : bool :=
match m1, m2 with
| ModelProto_constructor _ _ _ _ _ _ _ x _ _ _ _,
  ModelProto_constructor _ _ _ _ _ _ _ x' _ _ _ _ =>
    match x, x' with
    | Some y, Some y' =>
        match y, y' with
        | GraphProto_constructor n _ _ _ _ _ _ _ _ _,
          GraphProto_constructor n' _ _ _ _ _ _ _ _ _ => n == n'
        end
    | _, _ => false
    end
end.

Definition is_eq (y1 y2 : NetworkType Elem) (m1 : ModelProto)
(H : NetworkTypesMatch y1 y2) (m2 : ModelProto) : bool :=
  m1 == m2.

Definition int64_to_dim (i : int64) : nat := Z.to_nat (Z_of_int64 i).

(* does p's actual dims list match the declared shape d? *)
Definition dims_match (p : TensorProto) (d : {k : nat & {posnum nat} ^ k}) : bool :=
  match p, d with
  | TensorProto_constructor dims _ _ _ _ _ _ _ _ _ _ _ _ _ _, existT _ shape =>
      map int64_to_dim dims == map (fun q : {posnum nat} => q%:num) (tval shape)
  end.

Definition sized_tensor (t : TensorType Elem) : eqType :=
  { p : TensorProto | dims_match p (tensorDims _ t) }.

Definition syntax_inst : NetworkTheorySyntax :=
  {|
      ElementType := Elem;
      TheoryTensor := sized_tensor; (* fun=> TensorProto; *)
      Model := fun=>ModelProto;
      NodeOutputName := string; (* TODO: Check this is correct *)
      NodeOutput := nodeOutput;
      modelOutputs := mOutputs;
      iso := is_iso;
  |}.

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

Definition theoryTensorProto : forall t : TensorType (ElementType syntax_inst), TheoryTensor syntax_inst t -> TensorSemantics denote t.
Proof.
rewrite /=.
case.
move=> /= [x H] [k dims] t.
case: t.
case.
move=> /= t_dims data_type segment float int32 string int64 name doc_string raw_data
           external_data data_location double_data uint64_data metadata_props matches.
case: x H => //= H.
(* Each branch builds the tensor as a column vector: TensorSemantics for a
   purely-contravariant tensor 'nT[R]_(dims) is definitionally a matrix
   'M[R]_(\prod_i (dims i)%:num, 1) (the covariant-dims product is empty,
   hence 1 -- that's what `rewrite big_ord0` makes visible), so a flat,
   row-major TensorProto data list of length \prod_i (dims i)%:num is
   exactly a column vector of that shape. Nothing here proves the data
   list actually has that length, so out-of-range positions fall back to
   an arbitrary default (zero, or the empty string) via `nth`. *)
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth (Binary.B754_zero 24 128 false) float i).
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth (Byte.x00, Byte.x00, Byte.x00, Byte.x00) int32 i).
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) int64 i).
Defined.



(* --- Converting between the mathcomp tensor interface and TensorProto ---
   'nT[R]_(dims) is definitionally a column vector 'M[R]_(prod dims, 1)
   (the covariant-dims product is empty, i.e. 1 -- `rewrite big_ord0` is
   what exposes that), so building/reading one is just building/reading a
   flat, row-major list of length \prod_i (dims i)%:num. NB: bare `enum`
   is ambiguous once ONNXEvaluator.onnx_evaluator is imported (it also
   exports a constructor literally named `enum`, from the ProtobufConverter
   IR type, which takes a string -- hence `fintype.enum` everywhere below. *)

Definition build_tensor {R : eqType} (default : R) {k : nat} (dims : {posnum nat}^k)
  (data : seq R) : 'nT[R]_(dims).
Proof.
apply: Tensor; rewrite big_ord0.
exact: (\col_i nth default data i).
Defined.

Definition read_tensor {R : eqType} {k : nat} (dims : {posnum nat}^k) (t : 'nT[R]_(dims))
  : seq R :=
  let cols_eq : \prod_(j < 0) ([tuple] j)%:posnum = 1%R := big_ord0 _ _ _ _ in
  [seq val t i (cast_ord (esym cols_eq) ord0) | i <- fintype.enum 'I_(\prod_(l < k) (dims l)%:num)].

Definition default_TensorProto : TensorProto :=
  TensorProto_constructor nil None None nil nil nil nil None None None nil None nil nil nil.

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
Definition Semantics_to_TensorProto (d : TensorType Elem) : TensorSemantics denote d -> TensorProto.
Proof.
case: d => [[x Px] [k dims]] /=.
case: x Px => //= Px v.
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 1) None
            (read_tensor dims v) nil nil nil None None None nil None nil nil nil).
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 6) None
            nil (read_tensor dims v) nil nil None None None nil None nil nil nil).
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 7) None
            nil nil nil (read_tensor dims v) None None None nil None nil nil nil).
Defined.

Definition TensorProto_to_Semantics (d : TensorType Elem) (t : TensorProto) : TensorSemantics denote d.
Proof.
case: d => [[x Px] [k dims]] /=.
case: t => [_ _ _ float_data int32_data string_data int64_data _ _ _ _ _ double_data uint64_data _].
case: x Px => //= Px.
- exact: (build_tensor (Binary.B754_zero 24 128 false : float32) dims float_data).
- exact: (build_tensor int32_zero dims int32_data).
- exact: (build_tensor int64_zero dims int64_data).
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
pose idx := seq.index u (map value_info_name (graph_outputs model)).
pose out_tp := match onnx_evaluator model user_inputs with
  | Success outs => nth default_TensorProto outs idx
  | Error _ => default_TensorProto
  end.
exact: (TensorProto_to_Semantics d out_tp).
Defined.

(* ONNX's numeric DataType codes for the *entire* enum (not just
   supported_types) -- same numbering op_gemm.v/op_relu.v and
   Semantics_to_TensorProto above already rely on for the six supported
   constructors (1/6/7/8/11/13), extended here to all 24. *)
Definition int32_of_DataType_TensorProto (x : DataType_TensorProto) : option int32 :=
  int32_of_Z (Z.of_nat (match x with
  | UNDEFINED_TensorProto => 0
  | FLOAT_TensorProto => 1
  | UINT8_TensorProto => 2
  | INT8_TensorProto => 3
  | UINT16_TensorProto => 4
  | INT16_TensorProto => 5
  | INT32_TensorProto => 6
  | INT64_TensorProto => 7
  | STRING_TensorProto => 8
  | BOOL_TensorProto => 9
  | FLOAT16_TensorProto => 10
  | DOUBLE_TensorProto => 11
  | UINT32_TensorProto => 12
  | UINT64_TensorProto => 13
  | COMPLEX64_TensorProto => 14
  | COMPLEX128_TensorProto => 15
  | BFLOAT16_TensorProto => 16
  | FLOAT8E4M3FN_TensorProto => 17
  | FLOAT8E4M3FNUZ_TensorProto => 18
  | FLOAT8E5M2_TensorProto => 19
  | FLOAT8E5M2FNUZ_TensorProto => 20
  | UINT4_TensorProto => 21
  | INT4_TensorProto => 22
  | FLOAT4E2M1_TensorProto => 23
  end)).

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

(* the two are genuine inverses: encoding then decoding always recovers
   the original constructor *)
Lemma DataType_TensorProto_int32_roundtrip (x : DataType_TensorProto) :
  obind DataType_TensorProto_of_int32 (int32_of_DataType_TensorProto x) = Some x.
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
move=> /(Semantics_to_TensorProto d) t.
have := neg_tensor t.
case.
move=> t'.
exact: (TensorProto_to_Semantics d t').
move=> _.
exact: (TensorProto_to_Semantics d (zero_tensor t)).
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
move=> /(Semantics_to_TensorProto d) t1 /(Semantics_to_TensorProto d) t2.
have := add_tensor t1 t2.
case => t.
exact: (TensorProto_to_Semantics d t).
exact: (TensorProto_to_Semantics d (zero_tensor t1)).
Qed.

(** TODO: The zero_tensor needs to be reshaped **)
Definition TensorProto_mul (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
move=> /(Semantics_to_TensorProto d) t1 /(Semantics_to_TensorProto d) t2.
have := matmul_tensor t1 t2.
case => t.
exact: (TensorProto_to_Semantics d t).
exact: (TensorProto_to_Semantics d (zero_tensor t1)).
Qed.

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
