From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference tensor.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics.
From ONNXFormalization.VNNLIB.Core Require Import Syntax.

Open Scope ring_scope.

(* Parameter G : NetworkDeclarations. *)
(* Parameter n : NetworkTheorySyntax. *)
(* Parameter n' : NetworkTheorySemantics n. *)

Section Decls.
Context {n : NetworkTheorySyntax} {n' : NetworkTheorySemantics n}.

Definition InputValues (d : NetworkDeclaration) :=
  TensorsSemantics (elementType _ n') (typeOfInputs d).

(* Indexed by the hidden declarations rather than their mapped types, so   *)
(* that a value can be built directly from a hiddenNodeMapping.            *)
Definition HiddenValues (d : NetworkDeclaration) :=
  forall i : 'I_(size (hiddenDeclarations d)),
    TensorSemantics (elementType n n')
      (hiddenType (tnth (in_tuple (hiddenDeclarations d)) i)).

Definition OutputValues (d : NetworkDeclaration) :=
  TensorsSemantics (elementType n n') (typeOfOutputs d).

Record NetworkVariableValues (d : NetworkDeclaration) :=
  variableValues {
      inputs : InputValues d;
      hidden : HiddenValues d;
      outputs : OutputValues d;
    }.

Definition createNetworkVariableValues {d} (impl : NetworkImplementation d)
    (ia : InputAssignment d) : NetworkVariableValues d :=
  let: networkImplementation network hiddenNodeMapping := impl in
  let inputs : InputValues d := fun i => theoryTensor n n' (ia i) in
  variableValues d inputs
    (fun i => Semantics.model n n' network inputs (hiddenNodeMapping i))
    (fun i => Semantics.model n n' network inputs
       (projT2 (modelOutputs n network (mem_tnth i (in_tuple (typeOfOutputs d)))))).

Definition Environment (G : NetworkDeclarations) : Type :=
  forall i : 'I_(size G), NetworkVariableValues (tnth (in_tuple G) i).

Definition createEnvironment {G} (xs : NetworkImplementations G) (ys : InputAssignments G) : Environment G :=
  fun i => createNetworkVariableValues (xs i) (ys i).

Fixpoint lookupNetwork {G} {P : NetworkDeclaration -> Type} {Q : @NetworkPredicate n}
    (PG : forall i : 'I_(size G), P (tnth (in_tuple G) i)) (QG : has Q G) :
    {d : NetworkDeclaration & P d * Q d}.
Proof.
case: G PG QG => //= d G PG.
case E: (Q d) => /= QG.
have Pd : P d by have := PG ord0; rewrite (tnth_nth d).
by exists d.
apply: (lookupNetwork G P Q _ QG) => i.
by have := PG (lift ord0 i); rewrite !(tnth_nth d).
Qed.

Section Decls.
Context (G : NetworkDeclarations) (D : Environment G).

Definition constant (t : ElementType n) : eqType :=
  TensorSemantics (elementType n n') (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])).

Definition inputVar {t} (e : InputElementVariable G t) : constant t.
Proof.
case: e => shape inputNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: inputNode.
rewrite /InputVariable => [[/= d /andP [dinG H]]].
have H' : has (HasInputDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[inputs _ _]] ] := lookupNetwork D H'.
rewrite /HasInputDeclarationMatching => a.
pose T0 := {| tensorTypes := t; tensorDims := shape |}.
have ilt : (seq.index T0 (typeOfInputs d') < size (typeOfInputs d'))%N.
  by rewrite index_mem.
by have := inputs (Ordinal ilt); rewrite (tnth_nth T0) /= nth_index.
Qed.

Definition hiddenVar {t} (e : HiddenElementVariable G t) : constant t.
Proof.
case: e => shape hiddenNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: hiddenNode.
rewrite /HiddenVariable => [[/= d /andP [dinG H]]].
have H' : has (HasHiddenDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[_ hidden _]] ] := lookupNetwork D H'.
rewrite /HasHiddenDeclarationMatching => a.
pose T0 := {| tensorTypes := t; tensorDims := shape |}.
have ilt : (seq.index T0 (typeOfHiddenNodes d') < size (hiddenDeclarations d'))%N.
  by rewrite -[size (hiddenDeclarations d')](size_map (@hiddenType n)) index_mem.
pose h0 := tnth (in_tuple (hiddenDeclarations d')) (Ordinal ilt).
have := hidden (Ordinal ilt).
by rewrite (tnth_nth h0) -(nth_map h0 (hiddenType h0)) ?nth_index //.
Qed.

Definition outputVar {t} (e : OutputElementVariable G t) : constant t.
Proof.
case: e => shape outputNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: outputNode.
rewrite /OutputVariable => [[/= d /andP [dinG H]]].
have H' : has (HasOutputDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[_ _ outputs]] ] := lookupNetwork D H'.
rewrite /HasOutputDeclarationMatching => a.
pose T0 := {| tensorTypes := t; tensorDims := shape |}.
have ilt : (seq.index T0 (typeOfOutputs d') < size (typeOfOutputs d'))%N.
  by rewrite index_mem.
by have := outputs (Ordinal ilt); rewrite (tnth_nth T0) /= nth_index.
Qed.

Fixpoint arithExpr {t : ElementType n} (e : ArithExpr G t) {struct e} : constant t :=
  let d := (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])) in
  let fix arithExprList {t} (op : constant t -> constant t -> constant t) (e : constant t) (es : seq (ArithExpr G t)) {struct es} : constant t :=
    match es with
    | [::] => e
    | x :: xs => op (arithExpr x) (arithExprList op e xs)
    end in
  match e with
  | Syntax.constant a => theoryTensor n n' a
  | Syntax.inputVar x => inputVar x
  | Syntax.hiddenVar x => hiddenVar x
  | Syntax.outputVar x => outputVar x
  | negate x => @neg n n' d (arithExpr x)
  | add x xs => arithExprList (@Semantics.add n n' d) (arithExpr x) xs
  | sub x xs => @neg n n' d (arithExprList (@Semantics.add n n' d) (@neg n n' d (arithExpr x)) xs)
  | mul x xs => arithExprList (@Semantics.mul n n' d) (arithExpr x) xs
  end.

Definition compExpr {t} (e : CompExpr G t) : bool :=
  let d := (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])) in
  match e with
  | greaterThan x y => @ge n n' d (arithExpr x) (arithExpr y)
  | lessThan x y => @lt n n' d (arithExpr x) (arithExpr y)
  | greaterEqual x y => @ge n n' d (arithExpr x) (arithExpr y)
  | lessEqual x y => @le n n' d (arithExpr x) (arithExpr y)
  | notEqual x y => @neq n n' d (arithExpr x) (arithExpr y)
  | equal x y => @eq n n' d (arithExpr x) (arithExpr y)
  end.

Fixpoint boolExpr (e : BoolExpr G) : bool :=
  let fix boolExprList (op : bool -> bool -> bool) (e : bool) (xs : seq (BoolExpr G)) : bool :=
    match xs with
    | [::] => e
    | x :: xs => op (boolExpr x) (boolExprList op e xs)
    end in
  match e with
  | literal x => x
  | comparason t' x => compExpr x
  | and x xs => boolExprList andb (boolExpr x) xs
  | or x xs => boolExprList orb (boolExpr x) xs
  end.

Definition assertion (a : Assertion G) : bool :=
 match a with
 | assert x => boolExpr x
 end.

Definition assertionList (xs : seq (Assertion G)) : bool :=
  all assertion xs.

Definition QuerySemantics : Type :=
  forall (q : Query), @QueryModels n q -> Prop.

End Decls.

Definition query : QuerySemantics :=
  fun q m =>
match q, m with
| query networks assertions _, queryModels models _ =>
    exists (assignment : InputAssignments networks),
    assertionList networks (createEnvironment models assignment) assertions
end.

End Decls.
