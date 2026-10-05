From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics.

From mathcomp Require Import boot algebra order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Rdefinitions.
From mathcomp Require Import Rstruct.

Import EqNotations.
Section RealSyntax.
Context {n : NetworkTheorySyntax} {theorySemantics : NetworkTheorySemantics n}.

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
  := 'nT[R]_(projT2 (tensorDims _ t)).

Record RealModel (networkType : NetworkType RealElementType) :=
  realModel {
      runtimeNetworkType : NetworkType (ElementType n);
      runtimeNetwork : Model n runtimeNetworkType;
      sameShape : NetworkShapesMatch runtimeNetworkType networkType
    }.

Arguments realModel {networkType} {runtimeNetworkType} runtimeNetwork sameShape.

Definition RealNodeOutputName := NodeOutputName n.

Record RealNodeOutput y (network : RealModel y) (name : RealNodeOutputName) (nodeType : TensorType RealElementType) :=
  realNodeOutput {
      runtimeNodeType : TensorType (ElementType n);
      runtimeNode : NodeOutput n (runtimeNetwork y network) name runtimeNodeType;
      sameShapeOutput : TensorShapesMatch runtimeNodeType nodeType
    }.

Arguments realNodeOutput y network name nodeType {runtimeNodeType} runtimeNode sameShapeOutput.

Definition RealNodeOutputEq y (network : RealModel y)
  (name : RealNodeOutputName) (nodeType : TensorType RealElementType)
  : rel (RealNodeOutput y network name nodeType) :=
  fun a b =>
    match a, b with
    | realNodeOutput t1 m1 H1,
      realNodeOutput t2 m2 H2 =>
        match t1 =P t2 with
      | ReflectT e => rew [NodeOutput n (runtimeNetwork y network) name] e in m1 == m2
        | ReflectF _ => false
        end
    end.

Lemma RealNodeOutputEqP y (network : RealModel y)
  (name : RealNodeOutputName) (nodeType : TensorType RealElementType)
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

HB.instance Definition _ y (network : RealModel y)
  (name : RealNodeOutputName) (nodeType : TensorType RealElementType)
:= hasDecEq.Build (RealNodeOutput y network name nodeType) (RealNodeOutputEqP y network name nodeType).

Definition realModelOutputs y (m : RealModel y) :
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
Context {d : NetworkType RealElementType}.

Definition RealModelEq : rel (RealModel d) :=
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

HB.instance Definition _ := hasDecEq.Build (RealModel d) RealModelEqP.

End RealModelEq.

Definition realIso y1 y2 (m1 : RealModel y1)
  (H : NetworkShapesMatch y1 y2) (m2 : RealModel y2) : bool :=
match m1, m2 with
| realModel runtimeNetworkType1 runtimeNetwork1 sameShape1,
  realModel runtimeNetworkType2 runtimeNetwork2 sameShape2 =>
    iso n runtimeNetwork1 (NetworkShapesMatchTrans sameShape2 (NetworkShapesMatchTrans sameShape1 H)) runtimeNetwork2
end.

Definition realSyntax : NetworkTheorySyntax :=
  {|
    ElementType := RealElementType;
    TheoryTensor := RealTheoryTensor;
    Model := RealModel;
    NodeOutputName := RealNodeOutputName;
    NodeOutput := RealNodeOutput;
    modelOutputs := realModelOutputs;
    iso := realIso
  |}.

Definition realElementTypeInterp (real : RealElementType) : eqType := R.

Definition RealNetworkSemantics : Type :=
  forall {n y1 y2 d1 d2 u} (m : Model n y1), NetworkShapesMatch y1 y2 ->
                                        InputSemantics realElementTypeInterp y2 ->
                                        NodeOutput n m u d1 ->
                                        TensorShapesMatch d1 d2 ->
                                        TensorSemantics realElementTypeInterp d2.

Definition realTheoryTensor {t} (x : RealTheoryTensor t)
  : TensorSemantics realElementTypeInterp t.
Proof.
  rewrite /TensorSemantics.
  case: t x.
  move=> ? ? x; exact: x.
Qed.

Definition realModelInterp (realNetwork : RealNetworkSemantics) {y}
  (m : RealModel y) (inp : InputSemantics realElementTypeInterp y)
  {d} {u} (out : (RealNodeOutput y m u d))
  : TensorSemantics realElementTypeInterp d.
  Proof.
case: m out => runtimeNetworkType runtimeNetwork sameShape /=.
case=> runtimeNodeType runtimeNode sameNodeShape.
apply (realNetwork _ _ _ _ _ _ runtimeNetwork sameShape inp runtimeNode sameNodeShape).
Qed.

Definition test : ElementType realSyntax := real.

Section TensorPOrder.

Import Order.POrderTheory.
Local Open Scope order_scope.

Context (d : Order.disp_t) (R : porderType d).
Context {l k : nat} (u_ : {posnum nat} ^ k) (d_ : {posnum nat} ^ l).

Definition le_t (t u : 'T[R]_(u_, d_)) :=
  [forall ij, (\val t ij.1 ij.2) <= (\val u ij.1 ij.2)].

Definition lt_t (t u : 'T[R]_(u_, d_)) := (u != t) && le_t t u.

Let lt_t_def : forall x y, lt_t x y = (y != x) && le_t x y.
Proof. by []. Qed.

Let le_t_refl : reflexive le_t.
Proof. by move=> x; exact /forallP. Qed.

Let le_t_anti : antisymmetric le_t.
Proof.
  move=> x y /andP[/forallP le_t_xy /forallP le_t_yx].
  apply/val_inj/matrixP=> i j; apply /le_anti/andP.
  exact (conj (le_t_xy (i, j)) (le_t_yx (i, j))).
Qed.

Let le_t_trans : transitive le_t.
Proof.
  move=> x y z /forallP le_t_yx /forallP le_t_xz.
  apply/forallP=> ij; exact /le_trans.
Qed.

HB.instance Definition _ := Order.isPOrder.Build
                              d 'T[R]_(u_, d_) lt_t_def le_t_refl le_t_anti le_t_trans.

End TensorPOrder.

Definition tensor_le (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d :=
match d with
| tensorType tensorTypes tensorDims => Order.le
end.

Definition tensor_lt (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d :=
match d with
| tensorType tensorTypes tensorDims => Order.lt
end.

Definition tensor_ge (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d :=
match d with
| tensorType tensorTypes tensorDims => Order.ge
end.

Definition tensor_gt (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d :=
match d with
| tensorType tensorTypes tensorDims => Order.gt
end.

Definition tensor_eq (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d :=
  match d with
  | tensorType tensorTypes tensorDims => eq_op
  end.

Definition tensor_neq (d : TensorType (ElementType realSyntax))
  : TensorComp realElementTypeInterp d := fun x1 x2 => ~~ tensor_eq d x1 x2.

Definition tensor_neg (d : TensorType (ElementType realSyntax))
  : TensorOp1 realElementTypeInterp d.
Proof.
  case: d => types [k dims].
  exact: Algebra.opp.
Qed.

Definition tensor_add (d : TensorType (ElementType realSyntax))
  : TensorOp2 realElementTypeInterp d.
Proof.
  case: d => types [k dims].
  exact: Algebra.add.
Qed.

Definition tensor_mul (d : TensorType (ElementType realSyntax))
  : TensorOp2 realElementTypeInterp d.
Proof.
  case: d => types [k dims].
  exact: GRing.mul.
Qed.

Definition realSemantics (realNetworkSemantics : RealNetworkSemantics)
  : NetworkTheorySemantics realSyntax
  := @Build_NetworkTheorySemantics realSyntax
    realElementTypeInterp
    (@realTheoryTensor)
    (@realModelInterp realNetworkSemantics)
    tensor_le
    tensor_lt
    tensor_ge
    tensor_gt
    tensor_eq
    tensor_neq
    tensor_neg
    tensor_add
    tensor_mul.

End RealSyntax.
