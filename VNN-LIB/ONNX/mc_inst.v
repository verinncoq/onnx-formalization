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
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.

(** This is seemingly not actually used. Instead, the type of the tensor takes in
 many datatypes as options/lists (so they can be empty). This is not compatible
 with the interface, which expects the entire tensor to be typed under a single
 coherent type. **)

Definition DataType_TensorProtoEq : rel DataType_TensorProto :=
  fun t1 t2 =>
    match t1, t2 with
    | UNDEFINED_TensorProto, UNDEFINED_TensorProto => true
    | FLOAT_TensorProto, FLOAT_TensorProto => true
    | UINT8_TensorProto, UINT8_TensorProto => true
    | INT8_TensorProto, INT8_TensorProto => true
    | UINT16_TensorProto, UINT16_TensorProto => true
    | INT16_TensorProto, INT16_TensorProto => true
    | INT32_TensorProto, INT32_TensorProto => true
    | INT64_TensorProto, INT64_TensorProto => true
    | STRING_TensorProto, STRING_TensorProto => true
    | BOOL_TensorProto, BOOL_TensorProto => true
    | FLOAT16_TensorProto, FLOAT16_TensorProto => true
    | DOUBLE_TensorProto, DOUBLE_TensorProto => true
    | UINT32_TensorProto, UINT32_TensorProto => true
    | UINT64_TensorProto, UINT64_TensorProto => true
    | COMPLEX64_TensorProto, COMPLEX64_TensorProto => true
    | COMPLEX128_TensorProto, COMPLEX128_TensorProto => true
    | BFLOAT16_TensorProto, BFLOAT16_TensorProto => true
    | FLOAT8E4M3FN_TensorProto, FLOAT8E4M3FN_TensorProto => true
    | FLOAT8E4M3FNUZ_TensorProto, FLOAT8E4M3FNUZ_TensorProto => true
    | FLOAT8E5M2_TensorProto, FLOAT8E5M2_TensorProto => true
    | FLOAT8E5M2FNUZ_TensorProto, FLOAT8E5M2FNUZ_TensorProto => true
    | UINT4_TensorProto, UINT4_TensorProto => true
    | INT4_TensorProto, INT4_TensorProto => true
    | FLOAT4E2M1_TensorProto, FLOAT4E2M1_TensorProto => true
    | _, _ => false
    end.

Definition DataType_TensorProtoEqP : Equality.axiom DataType_TensorProtoEq.
Proof.
move=> xs ys.
by apply: (iffP idP) => [| ->];
case: xs;
case: ys.
Qed.

HB.instance Definition _ := hasDecEq.Build DataType_TensorProto DataType_TensorProtoEqP.

Section Byte.

Definition byteEqP : Equality.axiom Byte.eqb.
Proof.
move=> b0 b1.
apply: (iffP idP) => [H | ->].
  by rewrite (byte_dec_bl _ _ H).
by rewrite byte_dec_lb.
Qed.

HB.instance Definition _ := hasDecEq.Build byte byteEqP.

HB.instance Definition _ := Choice.copy byte (pcan_type Byte.of_to_nat).

Fact byte_display : Order.disp_t.
Proof. exact. Qed.

Definition lt_byte : rel byte :=
  fun x y => (to_nat x) < (to_nat y).

Definition le_byte : rel byte :=
  fun x y => (to_nat x) <= (to_nat y).

Lemma byte_lt_def (x y : byte) : lt_byte x y = le_byte x y && ~~ le_byte y x.
Proof.
rewrite /le_byte /lt_byte.
rewrite -ltNge.
case H: (x == y).
move/eqP: H ->.
by rewrite ltxx Bool.andb_false_r.
move/negP: H => /negP H.
rewrite le_eqVlt.
suff -> : (to_nat x == to_nat y) = false.
by rewrite /= andbb.
apply/negP => /eqP.
rewrite -to_of_nat_iff.
rewrite of_to_nat.
move => /Some_inj/esym H'.
move: H.
by rewrite H' => /eqP.
Qed.

Lemma byte_refl : reflexive le_byte.
Proof.
move=> x.
apply/le_refl.
Qed.

Lemma byte_le_trans : transitive le_byte.
Proof.
move=> x y z y_le_x x_le_z.
by apply/(le_trans y_le_x).
Qed.

HB.instance Definition _ := Order.isPreorder.Build byte_display
                                               byte
                                               byte_lt_def
                                               byte_refl
                                               byte_le_trans.

End Byte.

Section Binary.
Context (prec emax : Z).

Definition binaryEq : rel (Binary.binary_float prec emax) :=
  fun f1 f2 =>
    match f1, f2 with
    | Binary.B754_zero s, Binary.B754_zero s' => s == s'
    | Binary.B754_infinity s, Binary.B754_infinity s' => s == s'
    | Binary.B754_nan s m e, Binary.B754_nan s' m' e' => (s == s') && (m =? m')%positive
    | Binary.B754_finite s m e x, Binary.B754_finite s' m' e' x' => (s == s') && (m =? m')%positive && (Z.eqb e e') (* && x == x' *)
    | _, _ => false
    end.

Lemma binaryEq_sym (f1 : (Binary.binary_float prec emax)) : binaryEq f1 f1.
Proof.
  case f1=> //= s /=.
  - by move=> ? ?; apply/andP; split; last apply/Pos.eqb_eq.
  - move=> m e _.
    apply/andP.
    split.
      apply/andP.
      split.
        by apply/eqP.
      by apply/Pos.eqb_eq.
    by apply/Z.eqb_eq.
Qed.

Definition binaryEqP : Equality.axiom binaryEq.
Proof.
move=> f1 f2.
apply: (iffP idP).
 case f1; case f2 => //=.
 - by move=> s s' /= /eqP ->.
 - by move=> s s' /= /eqP ->.
 - move=> s pl e s' pl' e'.
   move=> /andP [/eqP -> /Peqb_true_eq H].
   move: H e e' => -> e e'.
   by rewrite (bool_irrelevance e e').
 - move=> s pl e x s' pl' e' x' /= /andP [/andP [/eqP ->]] /Peqb_true_eq H /Zeq_bool_eq H'.
   move: x x'.
   rewrite !H' => x x'.
   move: e e' x x' {H'}.
   rewrite H => e e' x x'.
   by rewrite (bool_irrelevance x x').
 - move=> ->.
   case: f2 => //=.
   move=> s pl e.
   by rewrite eqxx Pos.eqb_refl.
   move=> s pl e x.
   by rewrite eqxx Pos.eqb_refl Z.eqb_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build (Binary.binary_float prec emax)
                            binaryEqP.

End Binary.

Definition stringEqP : Equality.axiom String.eqb.
Proof.
  move=> s1 s2.
  apply: (iffP idP).
  by move=> /eqb_eq.
  by move=> /eqb_eq.
Qed.

HB.instance Definition _ := hasDecEq.Build string stringEqP.

Definition Segment_TensorProtoEq : rel Segment_TensorProto :=
  fun s1 s2 =>
    match s1, s2 with
    | Segment_TensorProto_constructor b1 e1, Segment_TensorProto_constructor b2 e2 =>
        (b1 == b2) && (e1 == e2)
    end.

Definition Segment_TensorProtoEqP : Equality.axiom Segment_TensorProtoEq.
Proof.
move=> [b1 e1] [b2 e2].
rewrite /Segment_TensorProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build Segment_TensorProto Segment_TensorProtoEqP.

Definition DataLocation_TensorProtoEq : rel DataLocation_TensorProto :=
  fun d1 d2 =>
    match d1, d2 with
    | DEFAULT_TensorProto, DEFAULT_TensorProto => true
    | EXTERNAL_TensorProto, EXTERNAL_TensorProto => true
    | _, _ => false
    end.

Definition DataLocation_TensorProtoEqP : Equality.axiom DataLocation_TensorProtoEq.
Proof.
move=> xs ys.
by apply: (iffP idP) => [| ->]; case: xs; case: ys.
Qed.

HB.instance Definition _ := hasDecEq.Build DataLocation_TensorProto DataLocation_TensorProtoEqP.

Definition StringStringEntryProtoEq : rel StringStringEntryProto :=
  fun s1 s2 =>
    match s1, s2 with
    | StringStringEntryProto_constructor k1 v1, StringStringEntryProto_constructor k2 v2 =>
        (k1 == k2) && (v1 == v2)
    end.

Definition StringStringEntryProtoEqP : Equality.axiom StringStringEntryProtoEq.
Proof.
move=> [k1 v1] [k2 v2].
rewrite /StringStringEntryProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build StringStringEntryProto StringStringEntryProtoEqP.

Definition TensorProtoEq : rel TensorProto :=
  fun t1 t2 =>
    match t1, t2 with
    | TensorProto_constructor dims1 dt1 seg1 fd1 i32d1 sd1 i64d1 n1 ds1 rd1 ed1 dl1 dd1 u64d1 mp1,
      TensorProto_constructor dims2 dt2 seg2 fd2 i32d2 sd2 i64d2 n2 ds2 rd2 ed2 dl2 dd2 u64d2 mp2 =>
        [&& dims1 == dims2, dt1 == dt2, seg1 == seg2, fd1 == fd2, i32d1 == i32d2,
          sd1 == sd2, i64d1 == i64d2, n1 == n2, ds1 == ds2, rd1 == rd2,
          ed1 == ed2, dl1 == dl2, dd1 == dd2, u64d1 == u64d2 & mp1 == mp2]
    end.

Definition TensorProtoEqP : Equality.axiom TensorProtoEq.
Proof.
  move=> [dims1 dt1 seg1 fd1 i32d1 sd1 i64d1 n1 ds1 rd1 ed1 dl1 dd1 u64d1 mp1]
           [dims2 dt2 seg2 fd2 i32d2 sd2 i64d2 n2 ds2 rd2 ed2 dl2 dd2 u64d2 mp2].
  rewrite /TensorProtoEq.
  apply: (iffP idP).
  - move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP->
                                                                                  /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP->
                                                                                                                                                         /andP[/eqP-> /andP[/eqP-> /eqP ->]]]]]]]]]]]]]].
    by [].
  - move=> [-> -> -> -> -> -> -> -> -> -> -> -> -> -> ->].
    by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build TensorProto TensorProtoEqP.

Definition dim_SimpleShardedDimProtoEq : rel dim_SimpleShardedDimProto :=
  fun x y =>
    match x, y with
    | dim_value_dim_SimpleShardedDimProto a, dim_value_dim_SimpleShardedDimProto b => a == b
    | dim_param_dim_SimpleShardedDimProto a, dim_param_dim_SimpleShardedDimProto b => a == b
    | _, _ => false
    end.

Definition dim_SimpleShardedDimProtoEqP : Equality.axiom dim_SimpleShardedDimProtoEq.
Proof.
move=> x y.
apply: (iffP idP).
- case: x y => [a|a] [b|b] //= /eqP ->; done.
- move=> <-.
  by case: x => a /=; rewrite eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build dim_SimpleShardedDimProto dim_SimpleShardedDimProtoEqP.

Definition value_Dimension_TensorShapeProtoEq : rel value_Dimension_TensorShapeProto :=
  fun x y =>
    match x, y with
    | dim_value_value_Dimension_TensorShapeProto a, dim_value_value_Dimension_TensorShapeProto b => a == b
    | dim_param_value_Dimension_TensorShapeProto a, dim_param_value_Dimension_TensorShapeProto b => a == b
    | _, _ => false
    end.

Definition value_Dimension_TensorShapeProtoEqP : Equality.axiom value_Dimension_TensorShapeProtoEq.
Proof.
move=> x y.
apply: (iffP idP).
- case: x y => [a|a] [b|b] //= /eqP ->; done.
- move=> <-.
  by case: x => a /=; rewrite eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build value_Dimension_TensorShapeProto value_Dimension_TensorShapeProtoEqP.

Definition OperatorSetIdProtoEq : rel OperatorSetIdProto :=
  fun t1 t2 =>
    match t1, t2 with
    | OperatorSetIdProto_constructor dm ver, OperatorSetIdProto_constructor dm2 ver2 =>
        (dm == dm2) && (ver == ver2)
    end.

Definition OperatorSetIdProtoEqP : Equality.axiom OperatorSetIdProtoEq.
Proof.
move=> [dm ver] [dm2 ver2].
rewrite /OperatorSetIdProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build OperatorSetIdProto OperatorSetIdProtoEqP.

Definition IntIntListEntryProtoEq : rel IntIntListEntryProto :=
  fun t1 t2 =>
    match t1, t2 with
    | IntIntListEntryProto_constructor k v, IntIntListEntryProto_constructor k2 v2 =>
        (k == k2) && (v == v2)
    end.

Definition IntIntListEntryProtoEqP : Equality.axiom IntIntListEntryProtoEq.
Proof.
move=> [k v] [k2 v2].
rewrite /IntIntListEntryProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build IntIntListEntryProto IntIntListEntryProtoEqP.

Definition SimpleShardedDimProtoEq : rel SimpleShardedDimProto :=
  fun t1 t2 =>
    match t1, t2 with
    | SimpleShardedDimProto_constructor d ns, SimpleShardedDimProto_constructor d2 ns2 =>
        (d == d2) && (ns == ns2)
    end.

Definition SimpleShardedDimProtoEqP : Equality.axiom SimpleShardedDimProtoEq.
Proof.
move=> [d ns] [d2 ns2].
rewrite /SimpleShardedDimProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build SimpleShardedDimProto SimpleShardedDimProtoEqP.

Definition ShardedDimProtoEq : rel ShardedDimProto :=
  fun t1 t2 =>
    match t1, t2 with
    | ShardedDimProto_constructor ax ss, ShardedDimProto_constructor ax2 ss2 =>
        (ax == ax2) && (ss == ss2)
    end.

Definition ShardedDimProtoEqP : Equality.axiom ShardedDimProtoEq.
Proof.
move=> [ax ss] [ax2 ss2].
rewrite /ShardedDimProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build ShardedDimProto ShardedDimProtoEqP.

Definition DeviceConfigurationProtoEq : rel DeviceConfigurationProto :=
  fun t1 t2 =>
    match t1, t2 with
    | DeviceConfigurationProto_constructor nm nd dv,
      DeviceConfigurationProto_constructor nm2 nd2 dv2 =>
        [&& nm == nm2, nd == nd2 & dv == dv2]
    end.

Definition DeviceConfigurationProtoEqP : Equality.axiom DeviceConfigurationProtoEq.
Proof.
move=> [nm nd dv] [nm2 nd2 dv2].
rewrite /DeviceConfigurationProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /eqP ->]].
  by [].
- move=> [-> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build DeviceConfigurationProto DeviceConfigurationProtoEqP.

Definition TensorAnnotationEq : rel TensorAnnotation :=
  fun t1 t2 =>
    match t1, t2 with
    | TensorAnnotation_constructor tn qp, TensorAnnotation_constructor tn2 qp2 =>
        (tn == tn2) && (qp == qp2)
    end.

Definition TensorAnnotationEqP : Equality.axiom TensorAnnotationEq.
Proof.
move=> [tn qp] [tn2 qp2].
rewrite /TensorAnnotationEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build TensorAnnotation TensorAnnotationEqP.

Definition SparseTensorProtoEq : rel SparseTensorProto :=
  fun t1 t2 =>
    match t1, t2 with
    | SparseTensorProto_constructor vl ix dm,
      SparseTensorProto_constructor vl2 ix2 dm2 =>
        [&& vl == vl2, ix == ix2 & dm == dm2]
    end.

Definition SparseTensorProtoEqP : Equality.axiom SparseTensorProtoEq.
Proof.
move=> [vl ix dm] [vl2 ix2 dm2].
rewrite /SparseTensorProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /eqP ->]].
  by [].
- move=> [-> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build SparseTensorProto SparseTensorProtoEqP.

Definition Dimension_TensorShapeProtoEq : rel Dimension_TensorShapeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | Dimension_TensorShapeProto_constructor vl dn,
      Dimension_TensorShapeProto_constructor vl2 dn2 =>
        (vl == vl2) && (dn == dn2)
    end.

Definition Dimension_TensorShapeProtoEqP : Equality.axiom Dimension_TensorShapeProtoEq.
Proof.
move=> [vl dn] [vl2 dn2].
rewrite /Dimension_TensorShapeProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build Dimension_TensorShapeProto Dimension_TensorShapeProtoEqP.

Definition TensorShapeProtoEq : rel TensorShapeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | TensorShapeProto_constructor d, TensorShapeProto_constructor d2 => d == d2
    end.

Definition TensorShapeProtoEqP : Equality.axiom TensorShapeProtoEq.
Proof.
move=> [d] [d2].
rewrite /TensorShapeProtoEq /=.
apply: (iffP eqP) => [->|[->]] //.
Qed.

HB.instance Definition _ := hasDecEq.Build TensorShapeProto TensorShapeProtoEqP.

Definition Tensor_TypeProtoEq : rel Tensor_TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | Tensor_TypeProto_constructor et sh, Tensor_TypeProto_constructor et2 sh2 =>
        (et == et2) && (sh == sh2)
    end.

Definition Tensor_TypeProtoEqP : Equality.axiom Tensor_TypeProtoEq.
Proof.
move=> [et sh] [et2 sh2].
rewrite /Tensor_TypeProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build Tensor_TypeProto Tensor_TypeProtoEqP.

Definition Sequence_TypeProtoEq : rel Sequence_TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | Sequence_TypeProto_constructor et, Sequence_TypeProto_constructor et2 => et == et2
    end.

Definition Sequence_TypeProtoEqP : Equality.axiom Sequence_TypeProtoEq.
Proof.
move=> [et] [et2].
rewrite /Sequence_TypeProtoEq /=.
apply: (iffP eqP) => [->|[->]] //.
Qed.

HB.instance Definition _ := hasDecEq.Build Sequence_TypeProto Sequence_TypeProtoEqP.

Definition Map_TypeProtoEq : rel Map_TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | Map_TypeProto_constructor kt vt, Map_TypeProto_constructor kt2 vt2 =>
        (kt == kt2) && (vt == vt2)
    end.

Definition Map_TypeProtoEqP : Equality.axiom Map_TypeProtoEq.
Proof.
move=> [kt vt] [kt2 vt2].
rewrite /Map_TypeProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build Map_TypeProto Map_TypeProtoEqP.

Definition Optional_TypeProtoEq : rel Optional_TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | Optional_TypeProto_constructor et, Optional_TypeProto_constructor et2 => et == et2
    end.

Definition Optional_TypeProtoEqP : Equality.axiom Optional_TypeProtoEq.
Proof.
move=> [et] [et2].
rewrite /Optional_TypeProtoEq /=.
apply: (iffP eqP) => [->|[->]] //.
Qed.

HB.instance Definition _ := hasDecEq.Build Optional_TypeProto Optional_TypeProtoEqP.

Definition SparseTensor_TypeProtoEq : rel SparseTensor_TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | SparseTensor_TypeProto_constructor et sh, SparseTensor_TypeProto_constructor et2 sh2 =>
        (et == et2) && (sh == sh2)
    end.

Definition SparseTensor_TypeProtoEqP : Equality.axiom SparseTensor_TypeProtoEq.
Proof.
move=> [et sh] [et2 sh2].
rewrite /SparseTensor_TypeProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build SparseTensor_TypeProto SparseTensor_TypeProtoEqP.

Definition value_TypeProtoEq : rel value_TypeProto :=
  fun x y =>
    match x, y with
    | tensor_type_value_TypeProto a, tensor_type_value_TypeProto b => a == b
    | sequence_type_value_TypeProto a, sequence_type_value_TypeProto b => a == b
    | map_type_value_TypeProto a, map_type_value_TypeProto b => a == b
    | optional_type_value_TypeProto a, optional_type_value_TypeProto b => a == b
    | sparse_tensor_type_value_TypeProto a, sparse_tensor_type_value_TypeProto b => a == b
    | _, _ => false
    end.

Definition value_TypeProtoEqP : Equality.axiom value_TypeProtoEq.
Proof.
move=> x y.
apply: (iffP idP).
- case: x y => [a|a|a|a|a] [b|b|b|b|b] //= /eqP ->; done.
- move=> <-.
  by case: x => a /=; rewrite eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build value_TypeProto value_TypeProtoEqP.

Definition TypeProtoEq : rel TypeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | TypeProto_constructor vl dn, TypeProto_constructor vl2 dn2 =>
        (vl == vl2) && (dn == dn2)
    end.

Definition TypeProtoEqP : Equality.axiom TypeProtoEq.
Proof.
move=> [vl dn] [vl2 dn2].
rewrite /TypeProtoEq.
apply: (iffP idP).
- by move=> /andP [/eqP -> /eqP ->].
- by move=> [-> ->]; apply/andP.
Qed.

HB.instance Definition _ := hasDecEq.Build TypeProto TypeProtoEqP.

Definition AttributeType_AttributeProtoEq : rel AttributeType_AttributeProto :=
  fun x y =>
    match x, y with
    | UNDEFINED_AttributeProto, UNDEFINED_AttributeProto => true
    | FLOAT_AttributeProto, FLOAT_AttributeProto => true
    | INT_AttributeProto, INT_AttributeProto => true
    | STRING_AttributeProto, STRING_AttributeProto => true
    | TENSOR_AttributeProto, TENSOR_AttributeProto => true
    | GRAPH_AttributeProto, GRAPH_AttributeProto => true
    | SPARSE_TENSOR_AttributeProto, SPARSE_TENSOR_AttributeProto => true
    | TYPE_PROTO_AttributeProto, TYPE_PROTO_AttributeProto => true
    | FLOATS_AttributeProto, FLOATS_AttributeProto => true
    | INTS_AttributeProto, INTS_AttributeProto => true
    | STRINGS_AttributeProto, STRINGS_AttributeProto => true
    | TENSORS_AttributeProto, TENSORS_AttributeProto => true
    | GRAPHS_AttributeProto, GRAPHS_AttributeProto => true
    | SPARSE_TENSORS_AttributeProto, SPARSE_TENSORS_AttributeProto => true
    | TYPE_PROTOS_AttributeProto, TYPE_PROTOS_AttributeProto => true
    | _, _ => false
    end
.

Definition AttributeType_AttributeProtoEqP : Equality.axiom AttributeType_AttributeProtoEq.
Proof.
move=> xs ys.
by apply: (iffP idP) => [| ->]; case: xs; case: ys.
Qed.

HB.instance Definition _ := hasDecEq.Build AttributeType_AttributeProto AttributeType_AttributeProtoEqP.

Definition AttributeProtoEq : rel AttributeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | AttributeProto_constructor nm ra ds ty f i s t st tp fs is_ ss ts sts tps,
      AttributeProto_constructor nm2 ra2 ds2 ty2 f2 i2 s2 t2 st2 tp2 fs2 is_2 ss2 ts2 sts2 tps2 =>
        [&& nm == nm2, ra == ra2, ds == ds2, ty == ty2, f == f2, i == i2, s == s2,
            t == t2, st == st2, tp == tp2, fs == fs2, is_ == is_2, ss == ss2,
            ts == ts2, sts == sts2 & tps == tps2]
    end.

Definition AttributeProtoEqP : Equality.axiom AttributeProtoEq.
Proof.
move=> [nm ra ds ty f i s t st tp fs is_ ss ts sts tps]
       [nm2 ra2 ds2 ty2 f2 i2 s2 t2 st2 tp2 fs2 is_2 ss2 ts2 sts2 tps2].
rewrite /AttributeProtoEq.
apply: (iffP idP).
- repeat move=> /andP[/eqP->].
  by move=> /eqP->.
- move=> [-> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build AttributeProto AttributeProtoEqP.

Definition ValueInfoProtoEq : rel ValueInfoProto :=
  fun t1 t2 =>
    match t1, t2 with
    | ValueInfoProto_constructor nm ty ds mp,
      ValueInfoProto_constructor nm2 ty2 ds2 mp2 =>
        [&& nm == nm2, ty == ty2, ds == ds2 & mp == mp2]
    end.

Definition ValueInfoProtoEqP : Equality.axiom ValueInfoProtoEq.
Proof.
move=> [nm ty ds mp] [nm2 ty2 ds2 mp2].
rewrite /ValueInfoProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /eqP ->]]].
  by [].
- move=> [-> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build ValueInfoProto ValueInfoProtoEqP.

Definition ShardingSpecProtoEq : rel ShardingSpecProto :=
  fun t1 t2 =>
    match t1, t2 with
    | ShardingSpecProto_constructor tn dv im sd,
      ShardingSpecProto_constructor tn2 dv2 im2 sd2 =>
        [&& tn == tn2, dv == dv2, im == im2 & sd == sd2]
    end.

Definition ShardingSpecProtoEqP : Equality.axiom ShardingSpecProtoEq.
Proof.
move=> [tn dv im sd] [tn2 dv2 im2 sd2].
rewrite /ShardingSpecProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /eqP ->]]].
  by [].
- move=> [-> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build ShardingSpecProto ShardingSpecProtoEqP.

Definition NodeDeviceConfigurationProtoEq : rel NodeDeviceConfigurationProto :=
  fun t1 t2 =>
    match t1, t2 with
    | NodeDeviceConfigurationProto_constructor ci ss ps,
      NodeDeviceConfigurationProto_constructor ci2 ss2 ps2 =>
        [&& ci == ci2, ss == ss2 & ps == ps2]
    end.

Definition NodeDeviceConfigurationProtoEqP : Equality.axiom NodeDeviceConfigurationProtoEq.
Proof.
move=> [ci ss ps] [ci2 ss2 ps2].
rewrite /NodeDeviceConfigurationProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /eqP ->]].
  by [].
- move=> [-> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build NodeDeviceConfigurationProto NodeDeviceConfigurationProtoEqP.

Definition NodeProtoEq : rel NodeProto :=
  fun t1 t2 =>
    match t1, t2 with
    | NodeProto_constructor inp outp nm ot dm ov att ds mp dc,
      NodeProto_constructor inp2 outp2 nm2 ot2 dm2 ov2 att2 ds2 mp2 dc2 =>
        [&& inp == inp2, outp == outp2, nm == nm2, ot == ot2, dm == dm2,
            ov == ov2, att == att2, ds == ds2, mp == mp2 & dc == dc2]
    end.

Definition NodeProtoEqP : Equality.axiom NodeProtoEq.
Proof.
move=> [inp outp nm ot dm ov att ds mp dc] [inp2 outp2 nm2 ot2 dm2 ov2 att2 ds2 mp2 dc2].
rewrite /NodeProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP->
    /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /eqP ->]]]]]]]]].
  by [].
- move=> [-> -> -> -> -> -> -> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build NodeProto NodeProtoEqP.

Definition GraphProtoEq : rel GraphProto :=
  fun t1 t2 =>
    match t1, t2 with
    | GraphProto_constructor nd nm it si ds inp outp vi qa mp,
      GraphProto_constructor nd2 nm2 it2 si2 ds2 inp2 outp2 vi2 qa2 mp2 =>
        [&& nd == nd2, nm == nm2, it == it2, si == si2, ds == ds2,
            inp == inp2, outp == outp2, vi == vi2, qa == qa2 & mp == mp2]
    end.

Definition GraphProtoEqP : Equality.axiom GraphProtoEq.
Proof.
move=> [nd nm it si ds inp outp vi qa mp] [nd2 nm2 it2 si2 ds2 inp2 outp2 vi2 qa2 mp2].
rewrite /GraphProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /andP[/eqP->
    /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /eqP ->]]]]]]]]].
  by [].
- move=> [-> -> -> -> -> -> -> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build GraphProto GraphProtoEqP.

Definition FunctionProtoEq : rel FunctionProto :=
  fun t1 t2 =>
    match t1, t2 with
    | FunctionProto_constructor nm inp outp att ap nd ds oi dm ov vi mp,
      FunctionProto_constructor nm2 inp2 outp2 att2 ap2 nd2 ds2 oi2 dm2 ov2 vi2 mp2 =>
        [&& nm == nm2, inp == inp2, outp == outp2, att == att2, ap == ap2, nd == nd2,
            ds == ds2, oi == oi2, dm == dm2, ov == ov2, vi == vi2 & mp == mp2]
    end.

Definition FunctionProtoEqP : Equality.axiom FunctionProtoEq.
Proof.
move=> [nm inp outp att ap nd ds oi dm ov vi mp]
       [nm2 inp2 outp2 att2 ap2 nd2 ds2 oi2 dm2 ov2 vi2 mp2].
rewrite /FunctionProtoEq.
apply: (iffP idP).
- repeat move=>/andP[/eqP->].
  by move=>/eqP->.
- move=> [-> -> -> -> -> -> -> -> -> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build FunctionProto FunctionProtoEqP.

Definition TrainingInfoProtoEq : rel TrainingInfoProto :=
  fun t1 t2 =>
    match t1, t2 with
    | TrainingInfoProto_constructor iz al ib ub,
      TrainingInfoProto_constructor iz2 al2 ib2 ub2 =>
        [&& iz == iz2, al == al2, ib == ib2 & ub == ub2]
    end.

Definition TrainingInfoProtoEqP : Equality.axiom TrainingInfoProtoEq.
Proof.
move=> [iz al ib ub] [iz2 al2 ib2 ub2].
rewrite /TrainingInfoProtoEq.
apply: (iffP idP).
- move=> /andP[/eqP-> /andP[/eqP-> /andP[/eqP-> /eqP ->]]].
  by [].
- move=> [-> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build TrainingInfoProto TrainingInfoProtoEqP.

Definition ModelProtoEq : rel ModelProto :=
  fun t1 t2 =>
    match t1, t2 with
    | ModelProto_constructor iv oi pn pv dm mv ds gr mp ti fn cf,
      ModelProto_constructor iv2 oi2 pn2 pv2 dm2 mv2 ds2 gr2 mp2 ti2 fn2 cf2 =>
        [&& iv == iv2, oi == oi2, pn == pn2, pv == pv2, dm == dm2, mv == mv2,
            ds == ds2, gr == gr2, mp == mp2, ti == ti2, fn == fn2 & cf == cf2]
    end.

Definition ModelProtoEqP : Equality.axiom ModelProtoEq.
Proof.
move=> [iv oi pn pv dm mv ds gr mp ti fn cf]
       [iv2 oi2 pn2 pv2 dm2 mv2 ds2 gr2 mp2 ti2 fn2 cf2].
rewrite /ModelProtoEq.
apply: (iffP idP).
- repeat move=>/andP[/eqP->].
  by move=>/eqP->.
- move=> [-> -> -> -> -> -> -> -> -> -> -> ->].
  by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build ModelProto ModelProtoEqP.
