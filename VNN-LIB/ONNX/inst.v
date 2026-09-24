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
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator.
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
    end
.

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

HB.about Order.Preorder.
HB.about Order.isPreorder.

Definition binary_lt : rel (Binary.binary_float prec emax) :=
  fun x y =>
    match x, y with
    | Binary.B754_zero s, Binary.B754_zero s' => s && ~~ s'
    | Binary.B754_infinity s, Binary.B754_infinity s' => s && ~~ s'
    | Binary.B754_nan s m e, Binary.B754_nan s' m' e' => s && ~~ s'
    | Binary.B754_finite s m e x, Binary.B754_finite s' m' e' x' => (s == s') && (m =? m')%positive && (e <? e')
    | _, _ => false
    end.

Definition binary_le : rel (Binary.binary_float prec emax) :=
  fun x y => (y == x) || binary_lt x y.

Lemma binary_lt_def (x y : (Binary.binary_float prec emax)) : binary_lt x y
                                                       = binary_le x y
                                                         && ~~ (binary_le y x).
Proof.
case: x;
case: y => //=.
- move=> s s'.
  by case: s; case: s' => //=.
- move=> s s'.
  by case: s; case: s' => //=.
- move=> s m e s' m' e'.
  case: s; case: s' => //=;
  by rewrite /binary_le /= !Bool.orb_false_r eq_sym andbN.
- move=> s m e x s' m' e' x'.
  case: s; case: s' => //=.
  case H: (m' =? m)%positive => //=; last first.
  rewrite /binary_le.
  rewrite /binary_lt //=.
  rewrite H /= Bool.orb_false_r.
  rewrite Pos.eqb_sym H /= Bool.orb_false_r eq_sym.
  by rewrite andbN.
  rewrite /binary_le.
  rewrite /binary_lt /= H Pos.eqb_sym H /=.
  rewrite negb_or.
  case H': (e' <? e) => /=.
  symmetry.
  apply/and3P; split.
  by apply/orP; right.
  apply/eqP.
  case => _ H''.
  move: H'.
  by rewrite H'' => /Z.ltb_lt /Z.lt_irrefl.
  move /Z.ltb_lt: H' => /Z.lt_le_incl.
  rewrite -Z.nlt_ge => H'.
  by apply/negP/Z.ltb_lt.
  symmetry.
  apply/negP.
  rewrite Bool.orb_false_r.
  move=> /and3P [H0 H1 H2].
  move: H' H2 => /Z.ltb_ge H' /negbTE/Z.ltb_ge H2.
  move: x x' H0 H1.
  rewrite (Z.le_antisymm _ _ H' H2) => x x' /eqP -> /eqP.
  by apply.
  case H0: (m' =? m)%positive => /=.
  rewrite /binary_le /= H0 Pos.eqb_sym H0.
  rewrite !Bool.andb_true_l.
  rewrite negb_or.
  case H1: (e' <? e) => //=.
  symmetry.
  apply/and3P; split.
  by apply/orP; right.
  apply/eqP.
  case => _ H2.
  move: H1.
  rewrite H2.
  by rewrite Z.ltb_irrefl.
  move /Z.ltb_lt: H1 => /Z.lt_le_incl.
  rewrite -Z.nlt_ge => H1.
  by apply/negP/Z.ltb_lt.
  symmetry.
  apply/negP.
  rewrite Bool.orb_false_r.
  move=> /and3P [H2 H3 H4].
  move: H1 H4 => /Z.ltb_ge H1 /negbTE/Z.ltb_ge H4.
  move: x x' H2 H3.
  rewrite (Z.le_antisymm _ _ H1 H4) => x x' /eqP -> /eqP.
  by apply.
  symmetry.
  rewrite /binary_le /=.
  rewrite negb_or.
  apply/negP => /and3P [H1 H2 H3].
  move: H1 {H3}.
  rewrite H0 => /=.
  rewrite Bool.orb_false_r => H1.
  move/negP: H0.
  apply.
  move/eqP: H1.
  case => -> _.
  by rewrite Pos.eqb_refl.
Qed.

Lemma binary_refl : reflexive binary_le.
Proof.
case=> //= s.
apply/orP.
by left.
apply/orP.
by left.
move=> m e.
by rewrite /binary_le /= eqxx.
move=> m e x.
apply/orP.
by left.
Qed.

Lemma binary_lt_trans : transitive binary_lt.
Proof.
move=> x y z.
case: x;
case: y;
case: z => //=.
- by case; case; case.
- by case; case; case.
- move=> s1 m1 e1 s2 m2 e2 s3 m3 e3.
  by case: s1; case: s2; case: s3.
- move=> s1 m1 e1 x1 s2 m2 e2 x2 s3 m3 e3 x3.
  move=> /andP [/andP [/eqP -> /Pos.eqb_eq ->] /Z.ltb_lt H1].
  move=> /andP [/andP [/eqP -> /Pos.eqb_eq ->] /Z.ltb_lt H2].
  apply/andP.
  split.
  apply/andP.
  split => //.
  by apply/Pos.eqb_eq.
  apply/Z.ltb_lt.
  by transitivity e3.
Qed.

Lemma binary_le_trans : transitive binary_le.
Proof.
move=> x y z.
case: x;
case: y;
case: z => //=.
- by case;case;case.
- by case;
  case;
  case.
- move=> s1 m1 e1 s2 m2 e2 s3 m3 e3.
  rewrite /binary_le.
  case H1: s1; case H2: s2; case H3: s3 => //=;
  by rewrite !Bool.orb_false_r => /eqP -> /eqP ->.
- move=> s1 m1 e1 x1 s2 m2 e2 x2 s3 m3 e3 x3.
  rewrite /binary_le.
  move=> /orP [/eqP -> /orP [/eqP -> |] |].
  - by apply/orP; rewrite eq_refl; left.
  - by move=> H; apply/orP; right.
  - move=> H /orP [/eqP -> | H'].
    by apply/orP; right.
  apply/orP;
  right.
  by apply (binary_lt_trans _ _ _ H).
Qed.

Fact float64_display : Order.disp_t.
Proof. exact. Qed.

Definition Z_key (z : Z) : bool * nat :=
  match z with
  | Z0 => (false, 0%nat)
  | Zpos p => (false, Pos.to_nat p)
  | Zneg p => (true, Pos.to_nat p)
  end.

Definition Z_of_key (k : bool * nat) : Z :=
  match k with
  | (false, n) => Z.of_nat n
  | (true, n) => Z.opp (Z.of_nat n)
  end.

Lemma Z_keyK : cancel Z_key Z_of_key.
Proof. case=> [|p|p] //=; by rewrite positive_nat_Z. Qed.

Definition binary_key (f : Binary.binary_float prec emax)
  : bool * nat + (bool * nat + (bool * nat * (bool * nat) + bool * nat * (bool * nat))) :=
  match f with
  | Binary.B754_zero s => inl (s, 0%nat)
  | Binary.B754_infinity s => inr (inl (s, 0%nat))
  | Binary.B754_nan s pl _ => inr (inr (inl (s, Pos.to_nat pl, Z_key 0)))
  | Binary.B754_finite s m e _ => inr (inr (inr (s, Pos.to_nat m, Z_key e)))
  end.

Definition binary_of_key
  (k : bool * nat + (bool * nat + (bool * nat * (bool * nat) + bool * nat * (bool * nat))))
  : Binary.binary_float prec emax :=
  match k with
  | inl (s, _) => Binary.B754_zero prec emax s
  | inr (inl (s, _)) => Binary.B754_infinity prec emax s
  | inr (inr (inl (s, pn, _))) =>
    let pl := Pos.of_nat pn in
    match Bool.bool_dec (Binary.nan_pl prec pl) true with
    | left Heq => Binary.B754_nan prec emax s pl Heq
    | right _ => Binary.B754_zero prec emax false
    end
  | inr (inr (inr (s, mn, ek))) =>
    let m := Pos.of_nat mn in
    let e := Z_of_key ek in
    match Bool.bool_dec (SpecFloat.bounded prec emax m e) true with
    | left Heq => Binary.B754_finite prec emax s m e Heq
    | right _ => Binary.B754_zero prec emax false
    end
  end.

Lemma binary_keyK : cancel binary_key binary_of_key.
Proof.
case=> [s|s|s pl H|s m e H] //=.
- rewrite Pos2Nat.id.
  case: (Bool.bool_dec (Binary.nan_pl prec pl) true) => [Heq|Hne].
  - by rewrite (bool_irrelevance H Heq).
  - by rewrite H in Hne.
- rewrite Pos2Nat.id Z_keyK.
  case: (Bool.bool_dec (SpecFloat.bounded prec emax m e) true) => [Heq|Hne].
  - by rewrite (bool_irrelevance H Heq).
  - by rewrite H in Hne.
Qed.



HB.instance Definition _ := Choice.copy (Binary.binary_float prec emax) (can_type binary_keyK).

HB.instance Definition _ := Order.isPreorder.Build float64_display
                                               (Binary.binary_float prec emax)
                                               binary_lt_def
                                               binary_refl
                                               binary_le_trans.
End Binary.

Definition stringEqP : Equality.axiom String.eqb.
Proof.
  move=> s1 s2.
  apply: (iffP idP).
  by move=> /eqb_eq.
  by move=> /eqb_eq.
Qed.

HB.instance Definition _ := hasDecEq.Build string stringEqP.

Definition supported_types : seq DataType_TensorProto :=
  [:: FLOAT_TensorProto; INT32_TensorProto; INT64_TensorProto;
   STRING_TensorProto; DOUBLE_TensorProto; UINT64_TensorProto].

Definition Elem : eqType := { x in supported_types }.

Axiom TEMP : {k : nat & {posnum nat} ^ k} -> seq int64.

(* Definition Tensor (t : TensorType Elem) : TensorProto := *)
(*   match t with *)
(*   | tensorType tensorTypes tensorDims => *)
(*       match tensorTypes with *)
(*       | exist x Px => *)
(*           match x as x0 return (x0 \in supported_types) -> TensorProto with *)
(*           | FLOAT_TensorProto => fun=> *)
(*                                   TensorProto_constructor *)
(*                                     (TEMP tensorDims) (*dims*) *)
(*                                     (int32_of_Z 0) (* TODO: data_type*) *)
(*                                     None (* TODO: segment*) *)
(*                                     (denote tensorTypes) (*float_data*) *)
(*                                     nil (*int32_data*) *)
(*                                     nil (*string_data*) *)
(*                                     nil (*int64_data*) *)
(*                                     None (* TODO: name*) *)
(*                                     None (* TODO: doc_string*) *)
(*                                     None (*raw_data*) *)
(*                                     nil (* TODO: external_data*) *)
(*                                     nil (* TODO: data_location*) *)
(*                                     nil (*double_data*) *)
(*                                     nil (*uint64_data*) *)
(*                                     nil (* TODO: metadata_props*) *)


(*           | INT32_TensorProto => fun=> list int32 *)
(*           | INT64_TensorProto => fun=> list int64 *)
(*           | STRING_TensorProto => fun=> option string *)
(*           | DOUBLE_TensorProto => fun=> list float64 *)
(*           | UINT64_TensorProto => fun=> list uint64 *)
(*           | _ => fun Px => False_rect TensorProto (notF Px) *)
(*           end *)
(*       end *)
(*   end. *)
  (* denote (val (tensorTypes _ t)). *)

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
Given a declared output type d of the network shape y, together with a
proof that d is one of y's declared outputs, this looks up the model's
actual list of graph outputs (ModelProto -> GraphProto -> list ValueInfoProto)
at the same position d occupies in y's output list, and pairs that output's
name with the NodeProto that produces it.
*)

(* TODO: Check this and everything it relies on *)
Definition mOutputs (y : NetworkType Elem) (m : ModelProto)
(d : TensorType Elem) (H : d \in outputs Elem y)
  : {u : string & nodeOutput y m u d} :=
  let i := seq.index d (outputs Elem y) in
  let u := nth ""%string (map value_info_name (graph_outputs m)) i in
  existT _ u (producing_node m u).


(** TODO: This is not correct, it checks the graphs are the same, not the structure of the graph **)
Definition is_iso (y1 y2 : NetworkType Elem) (m1 : ModelProto)
(H : NetworkShapesMatch y1 y2) (m2 : ModelProto) : bool :=
match m1, m2 with
| ModelProto_constructor _ _ _ _ _ _ _ x _ _ _ _,
  ModelProto_constructor _ _ _ _ _ _ _ x' _ _ _ _ => x == x'
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
      equal := is_eq;
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

Definition test : forall t : TensorType (ElementType syntax_inst), TheoryTensor syntax_inst t -> TensorSemantics denote t.
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
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth ""%string (map string_of_bytes string) i).
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth (Binary.B754_zero 53 1024 false) double_data i).
- apply: Tensor; rewrite big_ord0.
  exact: (\col_i nth (Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00, Byte.x00) uint64_data i).
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
  let cols_eq : \prod_(j < 0) ([tuple] j)%:posnum = 1%N := big_ord0 _ _ _ _ in
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
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 8) None
            nil nil (map string_to_bytes (read_tensor dims v)) nil None None None nil None nil nil nil).
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 11) None
            nil nil nil nil None None None nil None (read_tensor dims v) nil nil).
- exact: (TensorProto_constructor (dims_of_shape dims) (int32_of_Z 13) None
            nil nil nil nil None None None nil None nil (read_tensor dims v) nil).
Defined.

Definition TensorProto_to_Semantics (d : TensorType Elem) (t : TensorProto) : TensorSemantics denote d.
Proof.
case: d => [[x Px] [k dims]] /=.
case: t => [_ _ _ float_data int32_data string_data int64_data _ _ _ _ _ double_data uint64_data _].
case: x Px => //= Px.
- exact: (build_tensor (Binary.B754_zero 24 128 false : float32) dims float_data).
- exact: (build_tensor int32_zero dims int32_data).
- exact: (build_tensor int64_zero dims int64_data).
- exact: (build_tensor ""%string dims (map string_of_bytes string_data)).
- exact: (build_tensor (Binary.B754_zero 53 1024 false : float64) dims double_data).
- exact: (build_tensor int64_zero dims uint64_data).
Defined.

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
Definition test2 (y : NetworkType (ElementType syntax_inst))
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

Definition tensor_le (t1 t2 : TensorProto) : bool :=
match t1, t2 with
| TensorProto_constructor dims1 data_type1 segment1 float_data1 int32_data1 string_data1 int64_data1 name1 _ raw1 ext1 _ double_data1 uint64_data1 _,
  TensorProto_constructor dims2 data_type2 segment2 float_data2 int32_data2 string_data2 int64_data2 name2 _ raw2 ext2 _ double_data2 uint64_data2 _ =>
    if opt_eq data_type1 data_type2 then false else
    match data_type1 with
    | None => false
    | Some data_type =>
             match Z_of_int32 data_type with
             (* | 1 => (float_data1 <= float_data2)%O (** Some FLOAT_TensorProto **) *)
             | 1 => s_all2 (binary_le 24 128) float_data1 float_data2
             | 6 => (int32_data1 <= int32_data2)%O (** Some INT32_TensorProto **)
             | 7 => (int64_data1 <= int64_data2)%O (** Some INT64_TensorProto **)
             | 8 => (string_data1 <= string_data2)%O (** Some STRING_TensorProto **) (** TODO: Check if the naive string le is correct **)
             (* | 11 =>  (double_data1 <= double_data2)%O (** Some DOUBLE_TensorProto **) *)
             | 11 => s_all2 (binary_le 53 1024) double_data1 double_data2
             | 13 => (uint64_data1 <= uint64_data2)%O (** Some UINT64_TensorProto **)
             | _ => false
             end%Z
    end
end.

Lemma TensorProto_le (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

Lemma TensorProto_lt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

Lemma TensorProto_ge (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

Lemma TensorProto_gt (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

Lemma TensorProto_eq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

Lemma TensorProto_neq (d : TensorType (ElementType syntax_inst)) : TensorComp denote d.
Admitted.

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

Definition minus_one : float32 := b32_of_bits 3212836864.

(** TODO: Desirable but not required **)
Lemma gemm_correct (d : TensorType (ElementType syntax_inst))
(t1 t2 t3 : TensorSemantics denote d)
  : exists t : TensorProto, gemm (Semantics_to_TensorProto d t1)
                       (Semantics_to_TensorProto d t2)
                       (Semantics_to_TensorProto d t3) [::] = Success t.
Admitted.


Definition TensorProto_neg (d : TensorType (ElementType syntax_inst)) : TensorOp1 denote d.
Proof.
move=> /(Semantics_to_TensorProto d) t.
(** The attribute setting beta = -1 **)
have attrib := AttributeProto_constructor (Some "beta") None None (Some FLOAT_AttributeProto) (Some minus_one) None None None None None nil nil nil nil nil nil.
have := gemm (zero_tensor t) (zero_tensor t) t [:: attrib].
case.
move=> t'.
exact: (TensorProto_to_Semantics d t).
move=> _.
exact: (TensorProto_to_Semantics d (zero_tensor t)).
Defined.

Definition TensorProto_add (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
move=> /(Semantics_to_TensorProto d) t1 /(Semantics_to_TensorProto d) t2.
have := gemm (t1) (zero_tensor t1) t2 [::].
case => t.
exact: (TensorProto_to_Semantics d t).
exact: (TensorProto_to_Semantics d (zero_tensor t1)).
Qed.

(** TODO: The zero_tensor needs to be reshaped **)
Definition TensorProto_mul (d : TensorType (ElementType syntax_inst)) : TensorOp2 denote d.
Proof.
move=> /(Semantics_to_TensorProto d) t1 /(Semantics_to_TensorProto d) t2.
have := gemm t1 t2 (zero_tensor t2) [::].
case => t.
exact: (TensorProto_to_Semantics d t).
exact: (TensorProto_to_Semantics d (zero_tensor t1)).
Qed.

Definition semantics_inst : NetworkTheorySemantics syntax_inst :=
  {|
      elementType := denote;
      theoryTensor := test;
      model := test2;
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
