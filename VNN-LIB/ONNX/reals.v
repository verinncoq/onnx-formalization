From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics.

From mathcomp Require Import boot algebra order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.

Import EqNotations.

Record RealElementType : Set := real {}.

Definition RealElementTypeEq : rel RealElementType := fun _ _ => true.

Definition RealElementTypeEqP : Equality.axiom RealElementTypeEq.
Proof.
  move=> x y.
  by apply: (iffP idP);
  case: x;
  case: y.
Qed.

HB.instance Definition _ := hasDecEq.Build RealElementType RealElementTypeEqP.

Definition RealTheoryTensor (t : TensorType RealElementType) : eqType
  := 'nT[RealElementType]_(projT2 (tensorDims _ t)).

Record RealModel {n : NetworkTheorySyntax} (networkType : NetworkType RealElementType) :=
  realModel {
      runtimeNetworkType : NetworkType (ElementType n);
      runtimeNetwork : Model n runtimeNetworkType;
      sameShape : NetworkShapesMatch runtimeNetworkType networkType
    }.

Definition RealNodeOutputName := NodeOutputName.

Record RealNodeOutput {d} y (network : RealModel y) (name : RealNodeOutputName d) (nodeType : TensorType RealElementType) :=
  realNodeOutput {
      runtimeNodeType : TensorType (ElementType d);
      runtimeNode : NodeOutput d (runtimeNetwork y network) name runtimeNodeType;
      sameShapeOutput : TensorShapesMatch runtimeNodeType nodeType
    }.

Definition RealNodeOutputEq {d} y (network : RealModel y)
  (name : RealNodeOutputName d) (nodeType : TensorType RealElementType)
  : rel (RealNodeOutput y network name nodeType) :=
  fun a b =>
    match a, b with
    | realNodeOutput t1 m1 H1,
      realNodeOutput t2 m2 H2 =>
        match t1 =P t2 with
      | ReflectT e => rew [NodeOutput d (runtimeNetwork y network) name] e in m1 == m2
        | ReflectF _ => false
        end
    end.

Lemma RealNodeOutputEqP {d} y (network : RealModel y)
  (name : RealNodeOutputName d) (nodeType : TensorType RealElementType)
  : Equality.axiom (RealNodeOutputEq y network name nodeType).
Proof.
move=> a b.
apply: (iffP idP) => [| <-]; last first.
case: a => t1 m1 H1 /=.
case: eqP => H //.
by rewrite (eq_axiomK H).
rewrite /RealNodeOutputEq.
case: a => t1 m1 H1.
case: b => t2 m2 H2.
case: eqP => // H.
destruct H.
move=> /eqP /= ->.
by rewrite (bool_irrelevance H1 H2).
Qed.

HB.instance Definition _ {d} y (network : RealModel y)
  (name : RealNodeOutputName d) (nodeType : TensorType RealElementType)
:= hasDecEq.Build (RealNodeOutput y network name nodeType) (RealNodeOutputEqP y network name nodeType).

Definition realModelOutputs {n} {y} (m : @RealModel n y) :
    {dffun forall i : 'I_(size (outputs _ y)),
         {u : NodeOutputName n & RealNodeOutput y m u (tnth (in_tuple (outputs _ y)) i)}}.
Proof.
case: y m => inps outs [[runtimeInts runtimeOuts] runtimeNetwork sameShape] /=.
refine (finfun (fun i => _)).
  have /= := (modelOutputs n runtimeNetwork).
  have /andP:= sameShape => [[_]].
rewrite  all2E => /andP [/eqP H allH].
pose i' := cast_ord (esym H) i.
move=> /(_ i') [x].
move=> H'.
exists x.
apply/realNodeOutput.
exact: H'.
rewrite /RealNodeOutput.
rewrite /i'.
case: i i' {H'} => j lt_j /= i'.
have x0 := tnth (in_tuple outs) (Ordinal lt_j).
have y0 := tnth (in_tuple runtimeOuts) i'.
rewrite (tnth_nth x0) (tnth_nth y0) /=.
move/(all_nthP (y0, x0)): allH => /(_ j).
rewrite size_zip /minn ifF ?H ?ltnn // => /(_ lt_j) /=.
by rewrite nth_zip.
Defined.

Lemma all2Trans {A B C : Type}
  {rAB : A -> B -> bool} {rBC : B -> C -> bool} {rCA : C -> A -> bool}
  (trans : forall {a} {b} {c}, rAB a b -> rBC b c -> rCA c a)
  {s1 : seq A} {s2 : seq B} {s3 : seq C} :
    all2 rAB s1 s2 -> all2 rBC s2 s3 -> all2 rCA s3 s1.
Proof.
  elim: s1 s2 s3 => [|a s1 IH] [|b s2] [|c s3] //= /andP[hab h12] /andP[hbc h23].
  by rewrite (trans _ _ _ hab hbc) (IH _ _ h12 h23).
Qed.

Lemma all2Sym {A B : Type}
  {rAB : A -> B -> bool} {rBA : B -> A -> bool}
  (sym : forall {a} {b}, rAB a b = rBA b a)
  {s1 : seq A} {s2 : seq B} :
    all2 rAB s1 s2 = all2 rBA s2 s1.
Proof.
  elim: s1 s2 => [|a s1 IH] [|b s2] //=.
  rewrite (sym a b).
  by case: (rBA b a) => /=.
Qed.

Lemma TensorShapesMatchTrans {t1 t2 t3 : eqType} {x1 : TensorType t1}
  {x2 : TensorType t2} {x3 : TensorType t3}
  : TensorShapesMatch x1 x2 -> TensorShapesMatch x2 x3 -> TensorShapesMatch x3 x1.
Proof.
rewrite /TensorShapesMatch.
by move=> /eqP -> /eqP ->.
Qed.

Lemma TensorShapesMatchSym {t1 t2 : eqType} {x1 : TensorType t1}
  {x2 : TensorType t2} : TensorShapesMatch x1 x2 = TensorShapesMatch x2 x1.
Proof.
  rewrite /TensorShapesMatch.
  by rewrite eq_sym.
Qed.

Lemma NetworkShapesMatchTrans {t1 t2 t3 : eqType} {y1 : NetworkType t1}
  {y2 : NetworkType t2} {y3 : NetworkType t3}
  : NetworkShapesMatch y1 y2 -> NetworkShapesMatch y2 y3 -> NetworkShapesMatch y3 y1.
Proof.
  case: y1 => in1 out1.
  case: y2 => in2 out2.
  case: y3 => in3 out3 /=.
  move=> /andP[i12 o12] /andP[i23 o23].
  by rewrite (all2Trans (@TensorShapesMatchTrans t1 t2 t3) i12 i23)
       (all2Trans (@TensorShapesMatchTrans t1 t2 t3) o12 o23).
Qed.

Lemma NetworkShapesMatchSym {t1 t2 : eqType} {y1 : NetworkType t1}
  {y2 : NetworkType t2} : NetworkShapesMatch y1 y2 = NetworkShapesMatch y2 y1.
Proof.
  case: y1 => [[in1 Hin1] [out1 Hout1]].
  case: y2 => [[in2 Hin2] [out2 Hout2]] /=.
  by rewrite !(all2Sym (@TensorShapesMatchSym t1 t2)).
Qed.

Section RealModelEq.
Context {n : NetworkTheorySyntax} {d : NetworkType RealElementType}.

Definition RealModelEq : rel (@RealModel n d) :=
  fun x y =>
    match x, y with
    | realModel t1 m1 sameShape1,
      realModel t2 m2 sameShape2 =>
        match t1 =P t2 with
        | ReflectT e => rew [Model n] e in m1 == m2
        | ReflectF e => false
        end
    end.

Definition RealModelEqP : Equality.axiom RealModelEq.
Proof.
move=> x y.
apply: (iffP idP).
case: x => /= t1 m1 H1.
case: y => /= t2 m2 H2.
case: eqP => //= H /eqP H'.
destruct H.
move: H'.
rewrite /= => ->.
by rewrite (bool_irrelevance H1 H2).
move=> ->.
case: y => t m H.
rewrite /RealModelEq.
case: eqP => //=.
move=> H'.
by rewrite (eq_axiomK H').
Qed.

HB.instance Definition _ := hasDecEq.Build (@RealModel n d) RealModelEqP.

End RealModelEq.

Definition realIso {n} {y1 y2} (m1 : @RealModel n y1)
  (H : NetworkShapesMatch y1 y2) (m2 : @RealModel n y2) : bool :=
match m1, m2 with
| realModel runtimeNetworkType1 runtimeNetwork1 sameShape1,
  realModel runtimeNetworkType2 runtimeNetwork2 sameShape2 =>
    iso n runtimeNetwork1 (NetworkShapesMatchTrans sameShape2 (NetworkShapesMatchTrans sameShape1 H)) runtimeNetwork2
end.

Definition realSyntax {n} : NetworkTheorySyntax :=
  {|
    ElementType := RealElementType;
    TheoryTensor := RealTheoryTensor;
    Model := RealModel;
    NodeOutputName := RealNodeOutputName n;
    NodeOutput := RealNodeOutput;
    modelOutputs := @realModelOutputs n;
    iso := @realIso n
  |}.
