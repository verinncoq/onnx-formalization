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

Definition model_well_formed (m : ModelProto) : bool :=
  (graph_of m).

Lemma isSuccess_map {T1 T2} (f : T1 -> error_option T2) (xs : seq T1)
  : isSuccess (escapeSequenceExtractor.list_error_option_to_error_option_list (ListDef.map f xs)) = all isSuccess (map f xs).
elim: xs => //= x xs IHxs.
case: (f x) => //= t.
rewrite -IHxs.
by case: (escapeSequenceExtractor.list_error_option_to_error_option_list (ListDef.map f xs)).
Qed.

Lemma isSuccess_map' {T1 T2} (f : T1 -> error_option T2) (xs : seq T1) (ys : seq T2)
  : isSuccess (list_error_option_to_error_option_list (ListDef.map f xs) ys) = all isSuccess (map f xs).
elim: xs ys => //= x xs IHxs ys.
by case: (f x) => //= t.
Qed.

Definition valid_op (n : NodeProto) (items : seq vertex) : bool :=
  let: NodeProto_constructor ins _ _ op _ _ _ _ _ _ := n in
  if op is Some s then
    if (s =? """Gemm""")%string then
      if ins is [:: i1; i2] then
        (size (find_vertex items i1) == 1%N) && (size (find_vertex items i2) == 1%N)
      else if ins is [:: i1; i2; i3] then
             ( size (find_vertex items i1) == 1%N) &&
               (size (find_vertex items i2) == 1%N) &&
               (size (find_vertex items i3) == 1%N)
           else false
    else if (s =? """Relu""")%string then
           if ins is [:: i] then size (find_vertex items i) == 1%N else false
         else false
  else false.

Variant valid_op_spec (n : NodeProto) (items : seq vertex) : Prop :=
  | VGemm2 i1 i2 v1 v2 outs a b c d e f g of
      n = NodeProto_constructor [:: i1; i2] outs a (Some """Gemm""") b c d e f g &
      find_vertex items i1 = [:: v1] &
      find_vertex items i2 = [:: v2]
  | VGemm3 i1 i2 i3 v1 v2 v3 outs a b c d e f g of
      n = NodeProto_constructor [:: i1; i2; i3] outs a (Some """Gemm""") b c d e f g &
      find_vertex items i1 = [:: v1] &
      find_vertex items i2 = [:: v2] &
      find_vertex items i3 = [:: v3]
  | VRelu i v outs a b c d e f g of
      n = NodeProto_constructor [:: i] outs a (Some """Relu""") b c d e f g &
      find_vertex items i = [:: v].

Lemma valid_opP n items : valid_op n items -> valid_op_spec n items.
Proof.
case: n => ins outs a [s|] b c d e f g //=.
case: (String.eqb_spec s """Gemm""") => [->|_].
- case: ins => [|i1 [|i2 [|i3 [|? ?]]]] //=.
  + case E1: (find_vertex items i1) => [|v1 [|? ?]] //=.
    case E2: (find_vertex items i2) => [|v2 [|? ?]] //= _.
    by eapply VGemm2; [reflexivity | exact: E1 | exact: E2].
  + case E1: (find_vertex items i1) => [|v1 [|? ?]] //=.
    case E2: (find_vertex items i2) => [|v2 [|? ?]] //=.
    case E3: (find_vertex items i3) => [|v3 [|? ?]] //= _.
    by eapply VGemm3; [reflexivity | exact: E1 | exact: E2 | exact: E3].
- case: (String.eqb_spec s """Relu""") => [->|_] //.
  case: ins => [|i [|? ?]] //=.
  case E: (find_vertex items i) => [|v [|? ?]] //= _.
  by eapply VRelu; [reflexivity | exact: E].
Qed.

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

Lemma mem_app {T : eqType} (x : T) (s1 s2 : seq T) :
  (x \in (s1 ++ s2)%list) = (x \in s1) || (x \in s2).
Proof. by rewrite app_cat mem_cat. Qed.

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

Lemma match_Z0_if (A : Type) (z : Z) (a b : A) :
  match z with Z0 => a | _ => b end = if (z =? 0)%Z then a else b.
Proof. by case: z. Qed.

Lemma isSuccessP (T : Type) (x : error_option T) :
  isSuccess x -> exists a, x = Success a.
Proof. by case: x => // a _; exists a. Qed.

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

Lemma list_product_float_success (xs ys : seq float32)
  : size xs = size ys -> isSuccess (list_product_float32 xs ys).
Proof.
elim: xs ys => //= [ys /esym /size0nil -> // | x xs IHxs ys sizes].
case: ys sizes => //= y ys /eq_add_S /(IHxs ys).
by case: (list_product_float32 xs ys).
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

Lemma repeat_is_nseq {T} (n : nat) (t : T) : ListDef.repeat t n = nseq n t.
Proof.
by elim: n => //= n ->.
Qed.

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

Lemma gemm_float32_success (m1 m2 m3 : matrix float32) (alpha beta : float32)
  (transA transB : int64) (dims_c : seq nat) :
  broadcastable_matrix (shape m1).1 (shape m1).2 dims_c m3 ->
  all2 (fun xs ys => size xs == size ys) m1 m2 ->
  isSuccess (gemm_float32 m1 m2 m3 alpha beta transA transB dims_c).
Proof.


Lemma gemm_two_success (t t' : TensorProto) (a : seq AttributeProto)
  : tensors_match [:: t; t'] -> tensorProtoSized t -> tensorProtoSized t'
    -> isSuccess (gemm_two_inputs t t' a).
Proof.
case/tensors_match2P=> dtype Hdtype1 Hdtype2.
move=> Ht Ht'.
case/tensorProtoSizedP: (Ht) => dims1 dtype1 seg1 float321 int321 bytes1 int641 name1 doc1 raw_data1 ext1 loc1 double1 uint641 meta1 /[dup] Hist -> /= datatype1 sized1 sizes1;
case/tensorProtoSizedP: (Ht') => dims2 dtype2 seg2 float322 int322 bytes2 int642 name2 doc2 raw_data2 ext2 loc2 double2 uint642 meta2 /[dup] Hist' -> /= datatype2 sized2 sizes2 => //=;
move: Hdtype1;
rewrite -Hdtype2 Hist Hist' /= datatype1 datatype2 // => _;
rewrite /gemm_two_inputs;
case: (get_gemm_attributes a) => [[[alpha beta] transA] transB].
rewrite (DataType_float datatype1).
rewrite (DataType_float datatype2).
suff convert_dims1 : dims_correct dims1; last admit.
have := (matrix_float_success _ Ht).
rewrite Hist.
move=> /(_ convert_dims1 datatype1).
rewrite -Hist.
case/isSuccessP=> x ->.
suff convert_dims2 : dims_correct dims2; last admit.
have := (matrix_float_success _ Ht').
rewrite Hist'.
move=> /(_ convert_dims2 datatype2).
rewrite -Hist'.
case/isSuccessP=> x' ->.
by case/isSuccessP: (gemm_float32_correct x x'
                    [:: [:: Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE 0 0
                           false]] alpha beta transA transB [::]) => x0 ->.
rewrite (DataType_int32 datatype1).
rewrite (DataType_int32 datatype2).
suff convert_dims1 : dims_correct dims1; last admit.
have := (matrix_int32_success _ Ht).
rewrite Hist.
move=> /(_ convert_dims1 datatype1).
rewrite -Hist.
case/isSuccessP=> x ->.
suff convert_dims2 : dims_correct dims2; last admit.
have := (matrix_int32_success _ Ht').
rewrite Hist'.
move=> /(_ convert_dims2 datatype2).
rewrite -Hist'.
case/isSuccessP=> x' ->.
admit.
rewrite (DataType_int64 datatype1).
rewrite (DataType_int64 datatype2).
suff convert_dims1 : dims_correct dims1; last admit.
have := (matrix_int64_success _ Ht).
rewrite Hist.
move=> /(_ convert_dims1 datatype1).
rewrite -Hist.
case/isSuccessP=> x ->.
suff convert_dims2 : dims_correct dims2; last admit.
have := (matrix_int64_success _ Ht').
rewrite Hist'.
move=> /(_ convert_dims2 datatype2).
rewrite -Hist'.
case/isSuccessP=> x' ->.
Admitted.

Lemma gemm_three_success (t0 t1 t2 : TensorProto) (a : seq AttributeProto) :
  tensors_match [:: t0; t1; t2] -> tensorProtoSized t0 -> tensorProtoSized t1 ->
  tensorProtoSized t2 ->
  isSuccess (gemm t0 t1 t2 a).
Proof.
case/tensors_matchP => //= dtype _ /and4P [/eqP Hdtype0 /eqP Hdtype1 /eqP Hdtype2 _].
move=> Ht0 Ht1 Ht2.
case/tensorProtoSizedP: (Ht0) => dims0 dtype0 seg0 float320 int320 bytes0 int640 name0 doc0 raw_data0 ext0 loc0 double0 uint640 meta0 /[dup] Hist0 -> /= datatype0 sized0 sizes0;
case/tensorProtoSizedP: (Ht1) => dims1 dtype1 seg1 float321 int321 bytes1 int641 name1 doc1 raw_data1 ext1 loc1 double1 uint641 meta1 /[dup] Hist1 -> /= datatype1 sized1 sizes1;
case/tensorProtoSizedP: (Ht2) => dims2 dtype2 seg2 float322 int322 bytes2 int642 name2 doc2 raw_data2 ext2 loc2 double2 uint642 meta2 /[dup] Hist2 -> /= datatype2 sized2 sizes2 => //=;
have := eq_trans Hdtype0 (esym Hdtype1);
have := eq_trans Hdtype0 (esym Hdtype2) => //=;
rewrite Hist0 Hist1 Hist2 /= datatype0 datatype1 datatype2 // => _ _.
rewrite /gemm.
rewrite -!Hist0 -!Hist1 -!Hist2.
case: (get_gemm_attributes a) => [[[alpha beta] transA] transB].
rewrite (DataType_float datatype0).
rewrite (DataType_float datatype1).
rewrite (DataType_float datatype2).
suff dims_correct0: dims_correct (get_dims t0); last admit.
have:= (matrix_float_success t0 Ht0 dims_correct0).
rewrite [X in tensor_dtype X]Hist0 /= datatype0 => /(_ erefl).
case/isSuccessP=> x0 ->.
suff dims_correct1: dims_correct (get_dims t1); last admit.
have:= (matrix_float_success t1 Ht1 dims_correct1).
rewrite [X in tensor_dtype X]Hist1 /= datatype1 => /(_ erefl).
case/isSuccessP=> x1 ->.
suff dims_correct2: dims_correct (get_dims t2); last admit.
have:= (matrix_float_success t2 Ht2 dims_correct2).
rewrite [X in tensor_dtype X]Hist2 /= datatype2 => /(_ erefl).
case/isSuccessP=> x2 ->.
suff: dims_correct dims2; last admit.
case/dims_correctP => [-> | h -> | w h -> ] /=.
by case/isSuccessP: (gemm_float32_correct x0 x1 x2 alpha beta transA transB [:: 1%nat; 1%nat]) => x ->.
case: (Z_of_int64 h) => // h' _.
by case/isSuccessP: (gemm_float32_correct x0 x1 x2 alpha beta transA transB [:: 1%nat; Pos.to_nat h']) => x ->.
case: (Z_of_int64 w) => // w' _.
case: (Z_of_int64 h) => // h' _.
by case/isSuccessP: (gemm_float32_correct x0 x1 x2 alpha beta transA transB [:: Pos.to_nat w'; Pos.to_nat h']) => x ->.


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

Lemma well_formed_computes (m : ModelProto) (xs : seq TensorProto)
  : model_well_formed m -> isSuccess (onnx_evaluator m xs).
Proof.
move=> H.
rewrite /onnx_evaluator.
case: m H => _ _ _ _ _ _ _ [[nodes _ initialisers _ _ inputs outputs _ _ _]|//] _ _ _ _ _ /=.
rewrite isSuccess_map.
rewrite all_map.
apply/allP => /= x _.
rewrite length_size !listmap_map !app_cat.
move H: ([seq node x0 | x0 <- List.rev nodes] ++
           [seq input x0 | x0 <- inputs] ++ [seq tensor x0 | x0 <- initialisers])%SEQ => items.
rewrite /=.
move H': (size items) => k.
elim: k x items {H'} nodes inputs initialisers H => //= [|k IHk x items nodes inputs initialisers H].
admit. (** One of the inputs must be non-empty **)
case: x IHk => /=.
- (** node **)
  move=> n.
  suff: valid_op n items; last admit. (** the operation must be valid **)
  case/valid_opP => //=.
  { (** Gemm 2 inputs **)
    move=> nin1 nin2 x y nout nname nop ndomain noverload nattrib ndoc nmeta -> /=.
    move=> findx findy IHk.
    rewrite findx findy.
    move/finds_in: findx.
    rewrite -H.
    by rewrite !mem_cat=> /or3P [];
      move=> /mapP => [[/= z zin zeqx]];
      rewrite H;
      case/isSuccessP: (IHk x items nodes inputs initialisers H) => t // ->;
      case/isSuccessP: (IHk y items nodes inputs initialisers H) => t' // ->;
      apply/gemm_two_success.
  }
  { (** Gemm 3 inputs **)
    move=> nin1 nin2 nin3 x y z nout nname nop ndomain noverload nattrib ndoc nmeta -> /=.
    move=> findx findy findz IHk.
    rewrite findx findy findz.
    move/finds_in: findx.
    rewrite -H.
    rewrite !mem_cat=> /or3P [];
      move=> /mapP => [[/= a ain aeqx]];
      rewrite H;
      case/isSuccessP: (IHk x items nodes inputs initialisers H) => [x' ->];
      case/isSuccessP: (IHk y items nodes inputs initialisers H) => [y' ->];
      case/isSuccessP: (IHk z items nodes inputs initialisers H) => [z' ->];
      by apply/gemm_three_success.
  }
  { (** Relu **)
    move=> nin x nout nname nop ndomain noverload nattrib ndoc nmeta -> /=.
    move=> findx IHk.
    rewrite findx.
    case/isSuccessP: (IHk x items nodes inputs initialisers H) => [x' ->].
    by apply/relu_success.
  }
- by []. (** tensor **)
- move=> v IHk. (** Input **)
  case: v => name _ _ _.
  suff: name; last admit. (** The name exists **)
  case: name => // name _.
  suff: exists x, List.filter (tensor_has_name name) xs =[:: x]; last admit. (** there is a tensor with the correct name **)
  by move=> [x ->].
- move=> v IHk. (** Output **)
  case: v => name _ _ _.
  suff: name; last admit. (** The name exists **)
  case: name => // name _.
  suff: exists x, List.filter (vertex_has_name name) items =[:: x]; last admit. (** there is a tensor with the correct name **)
  move=> [x ->].
  by apply/IHk/H.
Qed.


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
