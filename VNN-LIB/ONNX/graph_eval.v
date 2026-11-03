Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.
From Stdlib Require Import Rdefinitions Reals.
From mathcomp Require Import boot algebra order reals Rstruct.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Core Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst well_formed_model.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_gemm.
Import Order.TTheory.
Open Scope order_scope.
Close Scope Z_scope.
Open Scope string_scope.

(** * An evaluator of ONNX graphs over mathcomp matrices and tensors

    [graph_eval] walks the graph exactly as [onnx_evaluator_recursive]
    does: same vertices, same lookups, same fuel.  The values on the edges
    are tagged with their dims; a value of rank at most two is a matrix, a
    higher rank one a mathcomp tensor.  Every branch the ONNX evaluator
    answers with [Error] answers [None].  The element theory, what Gemm and
    Relu compute and how an initialiser is read, is a parameter.

    Everything but the matrix operations computes: on a closed model, [cbv]
    with the matrix operations kept folded normalises [model_eval] to the
    matrix expression the model denotes ([toy_sem] at the end). *)

(** ** Values *)

(** The type of a value of dims [ds]: a scalar is a 1 x 1 matrix, a vector a
    row, as [mat_of_dims] reads them for Gemm. *)
Definition TV (T : Type) (ds : seq nat) : Type :=
  match ds with
  | [::] => 'M[T]_(1, 1)
  | [:: w] => 'M[T]_(1, w)
  | [:: h; w] => 'M[T]_(h, w)
  | _ => 'nT[T]_(projT2 (dims_type ds))
  end.

Section Values.
Context {T : Type}.

(** A value on an edge: its dims and its data. *)
Definition tv := {ds : seq nat & TV T ds}.
Definition mk (ds : seq nat) (v : TV T ds) : tv := existT _ ds v.

(** A value as a matrix, with the matrix dims Gemm reads: [None] above
    rank two. *)
Definition val_mx (v : tv) : option {hw : nat * nat & 'M[T]_(hw.1, hw.2)} :=
  let: existT ds t := v in
  match ds as ds0 return TV T ds0 -> option {hw : nat * nat & 'M[T]_(hw.1, hw.2)} with
  | [::] => fun M => Some (existT _ (1, 1) M)
  | [:: w] => fun M => Some (existT _ (1, w) M)
  | [:: h; w] => fun M => Some (existT _ (h, w) M)
  | _ => fun _ => None
  end t.

(** An entrywise map on a value of any rank. *)
Definition map_tv (f : T -> T) (v : tv) : tv :=
  let: existT ds t := v in
  mk ds (match ds as ds0 return TV T ds0 -> TV T ds0 with
         | [::] | [:: _] | [:: _; _] => fun M => map_mx f M
         | _ => fun t => @Tensor _ _ _ _ _ (map_mx f (tensor_val t))
         end t).
End Values.
Arguments mk {T}.

(** ** Computable equality of dimensions

    [nat_eqd m n] decides [m = n] by a transparent recursion, so on closed
    numbers an equal pair reduces to [Some erefl] and a cast by it
    disappears. *)
Fixpoint nat_eqd (m n : nat) : option (m = n) :=
  match m, n return option (m = n) with
  | 0, 0 => Some erefl
  | m'.+1, n'.+1 =>
      if nat_eqd m' n' is Some e
      then Some (match e in (_ = y) return (m'.+1 = y.+1) with erefl => erefl end)
      else None
  | _, _ => None
  end.

(** Transposed when the attribute says so. *)
Definition trans_mx {T : Type} (t : int64) (hw : nat * nat) (M : 'M[T]_(hw.1, hw.2)) :
    'M[T]_((trans_dims t hw).1, (trans_dims t hw).2) :=
  match Z_of_int64 t as z
    return 'M[T]_((if z is 0%Z then hw else (hw.2, hw.1)).1,
                  (if z is 0%Z then hw else (hw.2, hw.1)).2) with
  | 0%Z => M
  | _ => M^T
  end.

(** Broadcasting index: [k] if it is in range, otherwise 0; computes. *)
Definition bidx (h k : nat) : 'I_h.+1 :=
  match (k < h.+1)%nat as b return (k < h.+1)%nat = b -> 'I_h.+1 with
  | true => fun E => Ordinal E
  | false => fun _ => ord0
  end erefl.

(** [C] broadcast to [n x p]: a dimension of size 1 always reads index 0. *)
Definition bcast_mx {T : Type} {h w : nat} (n p : nat) (C : 'M[T]_(h.+1, w.+1)) : 'M[T]_(n, p) :=
  \matrix_(i, j) C (bidx h (if h == 0 then 0 else i)) (bidx w (if w == 0 then 0 else j)).

(** ** The element theory *)

(** What Gemm and Relu compute on matrices and entries of an element type. *)
Record elem_ops (T : Type) := ElemOps {
  gemm2 : forall m n p, float32 -> 'M[T]_(m, n) -> 'M[T]_(n, p) -> 'M[T]_(m, p);
  gemm3 : forall m n p, float32 -> float32 ->
          'M[T]_(m, n) -> 'M[T]_(n, p) -> 'M[T]_(m, p) -> 'M[T]_(m, p);
  relu : T -> T
}.
Arguments ElemOps {T}.
Arguments gemm2 {T} _ {m n p}.
Arguments gemm3 {T} _ {m n p}.
Arguments relu {T}.

(** ** The evaluator *)

Section GraphEval.
Context {T : Type} (ops : elem_ops T).

(** How an initialiser is read. *)
Context (read_init : TensorProto -> @tv T).

Local Notation tA attrs := (get_gemm_attributes attrs).1.2.
Local Notation tB attrs := (get_gemm_attributes attrs).2.
Local Notation alpha_of attrs := (get_gemm_attributes attrs).1.1.1.
Local Notation beta_of attrs := (get_gemm_attributes attrs).1.1.2.

(** Gemm: A and B read as matrices, transposed as transA and transB say,
    with agreeing inner dimension; C, if given, broadcast to the result. *)
Definition gemm_val (attrs : seq AttributeProto) (A B : @tv T) (C : option (@tv T)) : option (@tv T) :=
  match val_mx A, val_mx B with
  | Some (existT hwA MA), Some (existT hwB MB) =>
      let MA' := trans_mx (tA attrs) hwA MA in
      let MB' := trans_mx (tB attrs) hwB MB in
      let n := (trans_dims (tA attrs) hwA).1 in
      let p := (trans_dims (tB attrs) hwB).2 in
      match nat_eqd (trans_dims (tB attrs) hwB).1 (trans_dims (tA attrs) hwA).2 with
      | None => None
      | Some ek =>
          let MB'' := castmx (ek, erefl) MB' in
          match C with
          | None => Some (mk [:: n; p] (gemm2 ops (alpha_of attrs) MA' MB''))
          | Some c =>
              if val_mx c is Some (existT hwC MC) then
                match hwC as hw0 return 'M[T]_(hw0.1, hw0.2) -> option (@tv T) with
                | (h.+1, w.+1) => fun MC =>
                    Some (mk [:: n; p] (gemm3 ops (alpha_of attrs) (beta_of attrs)
                                          MA' MB'' (bcast_mx n p MC)))
                | _ => fun _ => None
                end MC
              else None
          end
      end
  | _, _ => None
  end.

(** [onnx_evaluator_recursive].  The user inputs are positional: the input
    vertex at position [i] of the graph inputs takes the [i]-th user input. *)
Fixpoint graph_eval (fuel : nat) (user_inputs : seq (@tv T)) (inputs : seq ValueInfoProto)
    (vertices : seq vertex) (w : vertex) : option (@tv T) :=
  if fuel is fuel.+1 then
    let child i :=
      if find_vertex vertices i is [:: v] then graph_eval fuel user_inputs inputs vertices v
      else None in
    match w with
    | node (NodeProto_constructor ins _ _ (Some op) _ _ attrs _ _ _) =>
        if (op =? """Gemm""")%string then
          match ins with
          | [:: a; b] =>
              if (child a, child b) is (Some A, Some B) then gemm_val attrs A B None else None
          | [:: a; b; c] =>
              if (child a, child b, child c) is (Some A, Some B, Some C)
              then gemm_val attrs A B (Some C) else None
          | _ => None
          end
        else if (op =? """Relu""")%string then
          if ins is [:: a] then omap (map_tv (relu ops)) (child a) else None
        else None
    | node _ => None
    | tensor t => Some (read_init t)
    | input v => nth None (map Some user_inputs) (seq.index v inputs)
    | output _ => None
    end
  else None.

(** All the values of a list, if every one is there. *)
Fixpoint all_some {A : Type} (s : seq (option A)) : option (seq A) :=
  match s with
  | [::] => Some [::]
  | Some a :: s' => omap (cons a) (all_some s')
  | None :: _ => None
  end.

(** [onnx_evaluator]: the values of all graph outputs. *)
Definition model_eval (m : ModelProto) (user_inputs : seq (@tv T)) : option (seq (@tv T)) :=
  if m is ModelProto_constructor _ _ _ _ _ _ _
       (Some (GraphProto_constructor nodes _ initialisers _ _ inputs outputs _ _ _)) _ _ _ _ then
    let vertices := graph_items nodes inputs initialisers in
    all_some [seq if value_name o is Some nm then
                    if find_vertex vertices nm is [:: w]
                    then graph_eval (size vertices).+1 user_inputs inputs vertices w
                    else None
                  else None
             | o <- outputs]
  else None.

End GraphEval.

(** * Reals *)

Definition R_of_float32 (f : float32) : R := Binary.B2R 24%Z 128%Z f.

Lemma R_of_default_one : R_of_float32 default_one = 1%R.
Proof.
have H := Binary.binary_normalize_correct 24 128 erefl erefl BinarySingleNaN.mode_NE 1 0 false.
have F1 : Defs.F2R (Defs.Float radix2 1 0) = R1 by rewrite /Defs.F2R /= Rmult_1_r.
rewrite F1 Generic_fmt.round_generic in H;
  try by apply: (Generic_fmt.generic_format_bpow _ _ 0).
have H1 : Rlt R1 (Raux.bpow radix2 128) := Raux.bpow_lt radix2 0 128 erefl.
rewrite Rabs_R1 (Raux.Rlt_bool_true _ _ H1) in H.
by case: H => [HB _]; rewrite /R_of_float32 /default_one HB.
Qed.

Definition relumx {m n : nat} (M : 'M[R]_(m, n)) : 'M[R]_(m, n) :=
  map_mx (fun v => Num.max v 0%R) M.

Definition real_ops : elem_ops R :=
  ElemOps
    (fun m n p alpha A B => (R_of_float32 alpha *: (A *m B))%R)
    (fun m n p alpha beta A B C => (R_of_float32 alpha *: (A *m B) + R_of_float32 beta *: C)%R)
    (fun v => Num.max v 0%R).

Definition float_data (t : TensorProto) : seq float32 :=
  let: TensorProto_constructor _ _ _ fd _ _ _ _ _ _ _ _ _ _ _ := t in fd.

Definition float_zero : float32 := Binary.B754_zero 24%Z 128%Z false.

(** The entries of an initialiser as reals, and its matrix, in row-major
    order. *)
Definition proto_entry (t : TensorProto) (i : nat) : R :=
  R_of_float32 (nth float_zero (float_data t) i).

Definition proto_mx (h w : nat) (f : nat -> R) : 'M[R]_(h, w) :=
  \matrix_(i, j) f (i * w + j)%nat.

(** The column of a tensor's data in row-major order, as a tensor of [ds]. *)
Definition col_tensor {R : Type} (ds : seq nat) (f : nat -> R) :
    'nT[R]_(projT2 (dims_type ds)) :=
  @Tensor _ _ _ _ _
    (castmx (erefl, esym (prod_ord0 _))
       (\col_(i < \prod_(i < size ds) (projT2 (dims_type ds) i)%:num) f i)).

(** An initialiser as a real value. *)
Definition read_init_R (t : TensorProto) : @tv R :=
  let ds := map int64_to_dim (get_dims t) in
  let f := proto_entry t in
  mk ds (match ds as ds0 return TV R ds0 with
         | [::] => proto_mx 1 1 f
         | [:: w] => proto_mx 1 w f
         | [:: h; w] => proto_mx h w f
         | n1 :: n2 :: n3 :: rest => col_tensor (n1 :: n2 :: n3 :: rest) f
         end).

Definition real_eval (m : ModelProto) (xs : seq (@tv R)) : option (seq (@tv R)) :=
  model_eval real_ops read_init_R m xs.

(** ** Simplifying the semantics of a closed model

    [cbv] evaluates the walk and every lookup; the matrix operations, the
    reading of the entries and the algebraic structures on real matrices are
    kept folded.  The default Gemm attributes alpha and beta are 1, which the
    two rewrites remove. *)
Ltac graph_eval_simp :=
  cbv -[TV mulmx trmx GRing.scale GRing.one GRing.zero map_mx Order.max
        R_of_float32 default_one float_zero proto_mx proto_entry relumx
        RbaseSymbolsImpl_R__canonical__GRing_PzSemiRing
        RbaseSymbolsImpl_R__canonical__Order_Preorder
        matrix_matrix__canonical__GRing_LSemiModule
        RbaseSymbolsImpl_R__canonical__Algebra_BaseAddUMagma];
  rewrite ?R_of_default_one;
  repeat erewrite GRing.scale1r.

(** * Example: a two-layer network

    x : [1; 2]  --Gemm(W1, transB)-->  h : [1; 2]  --Relu-->  a : [1; 2]
      --Gemm(W2, transB)-->  y : [1; 1]
    with W1 : [2; 2] and W2 : [1; 2].  Its value is relumx (x *m W1^T) *m W2^T. *)

Definition vinfo (s : string) (dims : seq nat) : ValueInfoProto :=
  ValueInfoProto_constructor (Some s)
    (Some (TypeProto_constructor
             (Some (tensor_type_value_TypeProto
                      (Tensor_TypeProto_constructor (Some (int32_of_Z 1%Z))
                         (Some (TensorShapeProto_constructor
                                  (map (fun n => Dimension_TensorShapeProto_constructor
                                     (Some (dim_value_value_Dimension_TensorShapeProto
                                              (int64_of_Z (Z.of_nat n)))) None) dims))))))
             None))
    None [::].

Definition ftensor (s : string) (dims : seq nat) (data : seq float32) : TensorProto :=
  TensorProto_constructor (map (fun n => int64_of_Z (Z.of_nat n)) dims) (Some (int32_of_Z 1%Z)) None
    data [::] [::] [::] (Some s) None None [::] None [::] [::] [::].

Definition transB_attr : AttributeProto :=
  AttributeProto_constructor (Some """transB""") None None (Some INT_AttributeProto) None
    (Some (int64_of_Z 1%Z)) None None None None [::] [::] [::] [::] [::] [::].

Definition gemm_node (s : string) (ins : seq string) (out : string) : NodeProto :=
  NodeProto_constructor ins [:: out] (Some s) (Some """Gemm""") None None [:: transB_attr] None [::] [::].

Definition relu_node (s : string) (i out : string) : NodeProto :=
  NodeProto_constructor [:: i] [:: out] (Some s) (Some """Relu""") None None [::] None [::] [::].

Definition W1_proto := ftensor "W1" [:: 2; 2] [:: default_one; default_one; default_one; default_one].
Definition W2_proto := ftensor "W2" [:: 1; 2] [:: default_one; default_one].

Definition toy : ModelProto :=
  ModelProto_constructor None [::] None None None None None
    (Some (GraphProto_constructor
             [:: gemm_node "g1" [:: "x"; "W1"] "h"; relu_node "r" "h" "a";
                 gemm_node "g2" [:: "a"; "W2"] "y"]
             (Some "toy") [:: W1_proto; W2_proto] [::] None
             [:: vinfo "x" [:: 1; 2]] [:: vinfo "y" [:: 1; 1]] [::] [::] [::]))
    [::] [::] [::] [::].

Definition W1 : 'M[R]_(2, 2) := proto_mx 2 2 (proto_entry W1_proto).
Definition W2 : 'M[R]_(1, 2) := proto_mx 1 2 (proto_entry W2_proto).

Lemma toy_sem (x : 'M[R]_(1, 2)) :
  real_eval toy [:: mk [:: 1; 2] x] = Some [:: mk [:: 1; 1] (relumx (x *m W1^T) *m W2^T)].
Proof. by graph_eval_simp. Qed.
