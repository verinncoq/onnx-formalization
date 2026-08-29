From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference tensor.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax.

Open Scope ring_scope.

Section Semantics.

Context {ElementType : eqType} (interp : ElementType -> eqType).

Local Notation "[[ e ]]" := (interp e).

Definition TensorSemantics (n : TensorType ElementType) :=
match n with
| tensorType tensorTypes tensorDims => 'nT[[[tensorTypes]]]_(projT2 tensorDims)
end.

(* Semantics of a list of tensor types: one tensor per position. *)
Definition TensorsSemantics (ds : seq (TensorType ElementType)) : Type :=
  forall i : 'I_(size ds), TensorSemantics (tnth (in_tuple ds) i).

Definition InputSemantics (n : NetworkType ElementType) : Type :=
match n with
| networkType inputTypes _ => TensorsSemantics inputTypes
end.

Definition TensorOp1 (n : TensorType ElementType) :=
TensorSemantics n -> TensorSemantics n.

Definition TensorOp2 (n : TensorType ElementType) :=
TensorSemantics n -> TensorSemantics n -> TensorSemantics n.

Definition TensorComp (n : TensorType ElementType) :=
TensorSemantics n -> TensorSemantics n -> bool.

Definition NetworkSemantics (inputTypes : seq1 (TensorType ElementType))
                                (outputType : TensorType ElementType) : Type :=
TensorsSemantics inputTypes -> TensorSemantics outputType.

End Semantics.

Section NetworkTheorySemantics.
Record NetworkTheorySemantics (syn : NetworkTheorySyntax) := {
    elementType : ElementType syn -> eqType;
    theoryTensor : forall {t}, TheoryTensor syn t -> TensorSemantics elementType t;
    model : forall {y} (n : Model syn y), InputSemantics elementType y
            -> forall {d u}, NodeOutput syn n u d -> TensorSemantics elementType d;
    le : forall {d}, TensorComp elementType d;
    lt : forall {d}, TensorComp elementType d;
    ge : forall {d}, TensorComp elementType d;
    gt : forall {d}, TensorComp elementType d;
    eq : forall {d}, TensorComp elementType d;
    neq : forall {d}, TensorComp elementType d;
    neg : forall {d}, TensorOp1 elementType d;
    add : forall {d}, TensorOp2 elementType d;
    mul : forall {d}, TensorOp2 elementType d
}.
End NetworkTheorySemantics.
