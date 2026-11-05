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

(** * An evaluator of ONNX graphs over mathcomp tensors

    [graph_eval] walks the graph exactly as [onnx_evaluator_recursive]
    does: same vertices, same lookups, same fuel.  The values on the edges
    are tensors tagged with their dims; Gemm reads its inputs as matrices and
    its result coerces back to a tensor.  Every branch the ONNX evaluator
    answers with [Error] answers [None].  The element theory, what Gemm and
    Relu compute and how an initialiser is read, is a parameter.

    Everything but the matrix and tensor operations computes: on a closed
    model, [cbv] with those operations kept folded normalises [model_eval] to
    the expression the model denotes ([toy_sem] at the end). *)

(** ** Values *)

Section Values.
Context {T : Type}.

(** A value on an edge: its dims and its data. *)
Definition tv := {ds : seq nat & 'nT[T]_(projT2 (dims_type ds))}.
Definition mk (ds : seq nat) (v : 'nT[T]_(projT2 (dims_type ds))) : tv := existT _ ds v.

(** A value as a matrix, with the matrix dims Gemm reads: [None] above rank
    two, or if a dim is zero, which a matrix view would have to read as 1. *)
Definition val_mx (v : tv) : option {hw : nat * nat & 'M[T]_(dimc hw.1, dimc hw.2)} :=
  let: existT ds t := v in
  match (size ds <= 2)%nat as b return (size ds <= 2)%nat = b ->
    option {hw : nat * nat & 'M[T]_(dimc hw.1, dimc hw.2)} with
  | true => fun H =>
      if all (fun d => 0 < d)%nat ds
      then Some (existT _ (mat_of_dims ds) (tensor_mx ds H t))
      else None
  | false => fun _ => None
  end erefl.

(** An entrywise map on a tensor. *)
Definition map_t (f : T -> T) {k} {u : {posnum nat} ^ k} (t : 'nT[T]_(u)) : 'nT[T]_(u) :=
  @Tensor _ _ _ _ _ (map_mx f (tensor_val t)).

(** An entrywise map on a value of any rank. *)
Definition map_tv (f : T -> T) (v : tv) : tv :=
  let: existT ds t := v in mk ds (map_t f t).
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
Definition trans_mx {T : Type} (t : int64) (hw : nat * nat) (M : 'M[T]_(dimc hw.1, dimc hw.2)) :
    'M[T]_(dimc (trans_dims t hw).1, dimc (trans_dims t hw).2) :=
  match Z_of_int64 t as z
    return 'M[T]_(dimc (if z is 0%Z then hw else (hw.2, hw.1)).1,
                  dimc (if z is 0%Z then hw else (hw.2, hw.1)).2) with
  | 0%Z => M
  | _ => M^T
  end.

(** [C] broadcast to [n x p]: a dimension of size 1 always reads index 0. *)
Definition bcast_mx {T : Type} {h w : nat} (n p : nat) (C : 'M[T]_(dimc h, dimc w)) : 'M[T]_(n, p) :=
  \matrix_(i, j) C (bidx h (if h == 1 then 0 else i)) (bidx w (if w == 1 then 0 else j)).

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

(** How an initialiser is read; [None] if it cannot be. *)
Context (read_init : TensorProto -> option (@tv T)).

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
      match nat_eqd (dimc (trans_dims (tB attrs) hwB).1) (dimc (trans_dims (tA attrs) hwA).2) with
      | None => None
      | Some ek =>
          let MB'' := castmx (ek, erefl) MB' in
          match C with
          | None => Some (mk [:: n; p] (gemm2 ops (alpha_of attrs) MA' MB''))
          | Some c =>
              if val_mx c is Some (existT hwC MC) then
                Some (mk [:: n; p] (gemm3 ops (alpha_of attrs) (beta_of attrs)
                                       MA' MB'' (bcast_mx _ _ MC)))
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
    | tensor t => read_init t
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

(** The value of the vertex named [nm]: [model_eval] for a single output. *)
Definition name_eval (m : ModelProto) (nm : string) (user_inputs : seq (@tv T)) : option (@tv T) :=
  if m is ModelProto_constructor _ _ _ _ _ _ _
       (Some (GraphProto_constructor nodes _ initialisers _ _ inputs _ _ _ _)) _ _ _ _ then
    let vertices := graph_items nodes inputs initialisers in
    if find_vertex vertices nm is [:: w]
    then graph_eval (size vertices).+1 user_inputs inputs vertices w
    else None
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

Definition float_zero : float32 := Binary.B754_zero 24%Z 128%Z false.

(** The entries of an initialiser as reals, read from the field its dtype
    selects, in row-major order. *)
Definition proto_entry (t : TensorProto) (i : nat) : R :=
  let: TensorProto_constructor _ dt _ fd i32 _ i64 _ _ _ _ _ _ _ _ := t in
  match obind DataType_TensorProto_of_int32 dt with
  | Some INT32_TensorProto => IZR (Z_of_int32 (nth (int32_of_Z 0%Z) i32 i))
  | Some INT64_TensorProto => IZR (Z_of_int64 (nth (int64_of_Z 0%Z) i64 i))
  | _ => R_of_float32 (nth float_zero fd i)
  end.

(** The column of a tensor's data in row-major order, as a tensor of [ds]. *)
Definition col_tensor {R : Type} (ds : seq nat) (f : nat -> R) :
    'nT[R]_(projT2 (dims_type ds)) :=
  @Tensor _ _ _ _ _
    (castmx (erefl, esym (prod_ord0 _))
       (\col_(i < \prod_(i < size ds) (projT2 (dims_type ds) i)%:num) f i)).

(** The real value of dims [ds] with the given row-major entries. *)
Definition tv_of_entries (ds : seq nat) (f : nat -> R) : @tv R :=
  mk ds (col_tensor ds f).

(** An initialiser as a real value: [None] unless its dtype is supported and
    its data fills its dims, so a read never runs off the end of the data. *)
Definition read_init_R (t : TensorProto) : option (@tv R) :=
  if tensorProtoSized t
  then Some (tv_of_entries (map int64_to_dim (get_dims t)) (proto_entry t))
  else None.

Lemma read_init_R_sized t : tensorProtoSized t ->
  exists v, read_init_R t = Some v /\ tag v = map int64_to_dim (get_dims t).
Proof. by rewrite /read_init_R => ->; eexists. Qed.

Definition real_eval (m : ModelProto) (xs : seq (@tv R)) : option (seq (@tv R)) :=
  model_eval real_ops read_init_R m xs.

(** ** Between values and mathcomp tensors

    Both directions go through row-major entries indexed by [nat], so no
    cast between dims is needed. *)

Definition dims_seq {k : nat} (dims : {posnum nat} ^ k) : seq nat :=
  map (fun q : {posnum nat} => q%:num) (tval dims).

(** An entry of a matrix; 0 out of range. *)
Definition mx_nth {m n : nat} (M : 'M[R]_(m, n)) (i j : nat) : R :=
  match (insub i : option 'I_m), (insub j : option 'I_n) with
  | Some i', Some j' => M i' j'
  | _, _ => 0%R
  end.

(** The [n]-th entry of a value in row-major order. *)
Definition tv_entry (v : @tv R) (n : nat) : R :=
  let: existT ds t := v in mx_nth (tensor_val t) n 0.

Definition tv_of_tensor {k : nat} (dims : {posnum nat} ^ k) (t : 'nT[R]_(dims)) : @tv R :=
  tv_of_entries (dims_seq dims) (fun n => mx_nth (tensor_val t) n 0).

(** An evaluation that succeeded with the dims [dims]. *)
Definition value_fits {k : nat} (dims : {posnum nat} ^ k) (o : option (@tv R)) : bool :=
  if o is Some v then tag v == dims_seq dims else false.

(** The tensor of [dims] an evaluation denotes.  The evaluation must be known
    to have succeeded with those dims; the [None] branch is discharged, so a
    closed model still reduces whatever the proof is. *)
Definition tensor_of_value {k : nat} (dims : {posnum nat} ^ k) (o : option (@tv R))
  : value_fits dims o -> 'nT[R]_(dims) :=
  match o as o0 return value_fits dims o0 -> 'nT[R]_(dims) with
  | Some v => fun _ => @Tensor _ _ _ _ _ (\matrix_(i, j) tv_entry v i)
  | None => fun H => False_rect _ (notF H)
  end.

(** The real value of the vertex named [nm]. *)
Definition real_name_eval (m : ModelProto) (nm : string) (xs : seq (@tv R)) : option (@tv R) :=
  name_eval real_ops read_init_R m nm xs.

Lemma nth_val {m n} (M : 'M[R]_(m, n)) (i : 'I_m) (j : 'I_n) : mx_nth M i j = M i j.
Proof. by rewrite /mx_nth !valK. Qed.

Lemma index_pairs (A B : eqType) (xs : seq A) (ys : seq B) (x : A) (y : B) :
  x \in xs -> y \in ys ->
  seq.index (x, y) [seq (a, b) | a <- xs, b <- ys] = (seq.index x xs * size ys + seq.index y ys)%nat.
Proof.
move=> + yin; elim: xs => // a s IH; rewrite allpairs_cons index_cat in_cons.
case: eqP => [->|/eqP xa] /=.
  have -> : (a, y) \in [seq (a, b) | b <- ys] by apply/mapP; exists y.
  rewrite eqxx mul0n add0n.
  by rewrite (index_map (f := pair a)) // => p q [].
move=> /IH ->.
have -> : (x, y) \in [seq (a, b) | b <- ys] = false.
  by apply/negbTE/mapP => -[b _ [xE _]]; rewrite xE eqxx in xa.
have ax : (a == x) = false by rewrite eq_sym; exact: negbTE.
by rewrite size_map /= ax mulSn addnA.
Qed.

Lemma rank_pair n m (i : 'I_n) (j : 'I_m) :
  val (enum_rank (i, j)) = (i * m + j)%nat.
Proof.
have -> : val (enum_rank (i, j)) = seq.index (i, j) (fintype.enum {: 'I_n * 'I_m}).
  rewrite -[in RHS](nth_enum_rank (i, j) (i, j)).
  by rewrite index_uniq ?enum_uniq // -cardE ltn_ord.
rewrite enumT unlock /= /prod_enum index_pairs ?mem_enum //.
by rewrite !index_enum_ord size_enum_ord.
Qed.

(** Reading a rank-two tensor as a matrix agrees with its row-major entries. *)
Lemma mx_of_tensor_nth (h w : {posnum nat}) (t : 'nT[R]_([tuple h; w])) (i : 'I_h%:num) (j : 'I_w%:num) :
  (t : 'M[R]_(h%:num, w%:num)) i j = mx_nth (tensor_val t) (i * w%:num + j)%nat 0.
Proof.
rewrite /mx_of_tensor /= castmxE /= mxE /tensor_nil /nindex /= !mxE.
set A := tensormx_index _.
have eA : val A = (i * w%:num + j)%nat.
  rewrite /A /tensormx_index /= {A t} rank_pair /= rank_pair /=.
  by rewrite big_ord0 muln1 addn0 big_ord1 /finfun_of_tuple ffunE.
transitivity (mx_nth (tensor_val t) (val A) (val (cast_ord prod_nil (@ord0 0)))).
  by rewrite nth_val.
by rewrite eA.
Qed.

(** Reading a tensor as a matrix commutes with an entrywise map. *)
Lemma mx_of_map_t {T : Type} p q (n : mx_dim p) (m : mx_dim q) (f : T -> T)
    (t : 'nT[T]_([tuple mx_dim_pos n; mx_dim_pos m])) :
  @mx_of_tensor _ _ (mx_shape_dim n m) _ (map_t f t) =
  map_mx f (@mx_of_tensor _ _ (mx_shape_dim n m) _ t).
Proof.
case: n m t => p' /= e [q' /= e'] t; case: p / e; case: q / e'.
apply/matrixP => i j.
by rewrite /mx_of_tensor /= !castmxE /= !mxE /tensor_nil /nindex /map_t /= !mxE !cast_ord_id.
Qed.

Lemma nth_col {m n} (f : nat -> R) k : (k < m)%nat -> (0 < n)%nat ->
  mx_nth (\matrix_(i < m, j < n) f i) k 0 = f k.
Proof.
move=> km n0; rewrite /mx_nth.
have -> : (insub k : option 'I_m) = Some (Ordinal km) by exact: (valK (Ordinal km)).
have -> : (insub 0 : option 'I_n) = Some (Ordinal n0) by exact: (valK (Ordinal n0)).
by rewrite mxE.
Qed.

Lemma prod_pos k (f : {posnum nat} ^ k) : (0 < \prod_(i < k) (f i)%:num)%nat.
Proof.
apply: prodn_gt0 => i; case: (f i) => v.
by rewrite /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat.
Qed.

Lemma tensor_of_valueE {k} (dims : {posnum nat} ^ k) (o : option (@tv R)) (H : value_fits dims o) v :
  o = Some v -> tensor_of_value dims o H = @Tensor _ _ _ _ _ (\matrix_(i, j) tv_entry v i).
Proof. by move=> E; move: H; rewrite E. Qed.

(** ** No read falls back on a default

    [mx_nth], [proto_entry], [bidx] and [dims_type] are total functions on
    [nat] and so each has a branch for an index or dim that does not fit.  The
    lemmas below show that the structure of a value keeps every read away from
    those branches: all the indexes a tensor of the right dims asks for are in
    range, and the data of a sized initialiser fills its dims. *)

Lemma mx_nth_in {m n} (M : 'M[R]_(m, n)) i j (hi : (i < m)%nat) (hj : (j < n)%nat) :
  mx_nth M i j = M (Ordinal hi) (Ordinal hj).
Proof. exact: (nth_val M (Ordinal hi) (Ordinal hj)). Qed.

(** [dims_type] keeps positive dims as they are. *)
Lemma prod_dims_type ds : all (fun d => 0 < d)%nat ds ->
  (\prod_(i < size ds) (projT2 (dims_type ds) i)%:num = \prod_(d <- ds) d)%nat.
Proof.
move=> pos; rewrite [RHS]big_tnth; apply: eq_bigr => i _ /=.
by rewrite dims_type_num dimc_id //; apply: (allP pos); exact: mem_tnth.
Qed.

Lemma prod_dims_seq {k} (dims : {posnum nat} ^ k) :
  (\prod_(d <- dims_seq dims) d = \prod_(i < k) (dims i)%:num)%nat.
Proof.
rewrite /dims_seq big_map /= -[in RHS]big_enum /=.
by rewrite big_map.
Qed.

(** Every entry of a value in range of its dims is stored in the value. *)
Lemma tv_entry_stored ds (t : 'nT[R]_(projT2 (dims_type ds))) n :
  all (fun d => 0 < d)%nat ds -> (n < \prod_(d <- ds) d)%nat ->
  exists i j, tv_entry (mk ds t) n = tensor_val t i j.
Proof.
move=> pos lt; rewrite -(prod_dims_type _ pos) in lt.
have h0 : (0 < \prod_(j < 0) (([tuple] : {posnum nat} ^ 0) j)%:num)%nat by rewrite big_ord0.
by exists (Ordinal lt), (Ordinal h0); exact: mx_nth_in.
Qed.

(** Row-major entries are read back at the indexes they were written at. *)
Lemma tv_entry_of_entries ds f n :
  all (fun d => 0 < d)%nat ds -> (n < \prod_(d <- ds) d)%nat ->
  tv_entry (tv_of_entries ds f) n = f n.
Proof.
move=> pos lt; rewrite -(prod_dims_type _ pos) in lt.
have h0 : (0 < \prod_(j < 0) (([tuple] : {posnum nat} ^ 0) j)%:num)%nat by rewrite big_ord0.
by rewrite /= (mx_nth_in _ _ _ lt h0) castmxE /= mxE.
Qed.

(** A rank-two tensor of row-major entries, read as a matrix. *)
Lemma mx_of_col_tensor h w f (i : 'I_(dimc h)) (j : 'I_(dimc w)) : (0 < h)%nat -> (0 < w)%nat ->
  (col_tensor [:: h; w] f : 'M[R]_(dimc h, dimc w)) i j = f (i * dimc w + j)%nat.
Proof.
move=> h0 w0; rewrite (@mx_of_tensor_nth (dim_pos h) (dim_pos w)).
apply: (tv_entry_of_entries [:: h; w] f) => /=; first by rewrite h0 w0.
rewrite big_cons big_seq1 -{2}(dimc_id _ h0) -{3}(dimc_id _ w0).
have lti := ltn_ord i.
apply: (@leq_trans (i.+1 * dimc w)%nat); last by rewrite leq_mul2r lti orbT.
by rewrite mulSnr -addnS leq_add2l ltn_ord.
Qed.

(** The reads of [tensor_of_value] are in range of the value it reads. *)
Lemma tensor_of_value_entry {k} (dims : {posnum nat} ^ k) o (H : value_fits dims o) v i j :
  o = Some v ->
  [/\ tensor_val (tensor_of_value dims o H) i j = tv_entry v i,
      (val i < \prod_(d <- tag v) d)%nat &
      tag v = dims_seq dims].
Proof.
move=> E; move: H; rewrite E => H; have /eqP Tv := H.
split => //; first by rewrite /= mxE.
by rewrite Tv prod_dims_seq ltn_ord.
Qed.

Lemma dims_seq_pos {k} (dims : {posnum nat} ^ k) : all (fun d => 0 < d)%nat (dims_seq dims).
Proof.
rewrite /dims_seq all_map; apply/allP => q _ /=.
by case: q => v; rewrite /Itv.nat_sem /= in_itv /= ?andbT ?ltz_nat.
Qed.

(** Every entry of the tensor an evaluation denotes is stored in its value. *)
Lemma tensor_of_value_stored {k} (dims : {posnum nat} ^ k) o (H : value_fits dims o) ds
    (t : 'nT[R]_(projT2 (dims_type ds))) i j :
  o = Some (mk ds t) ->
  exists i' j', tensor_val (tensor_of_value dims o H) i j = tensor_val t i' j'.
Proof.
move=> E; have [-> lt /= Tv] := tensor_of_value_entry dims o H (mk ds t) i j E.
apply: tv_entry_stored lt; move: (dims_seq_pos dims); rewrite -Tv; exact: id.
Qed.

(** A user input is read back unchanged. *)
Lemma tv_of_tensorK {k} (dims : {posnum nat} ^ k) (t : 'nT[R]_(dims))
    (H : value_fits dims (Some (tv_of_tensor dims t))) :
  tensor_of_value dims (Some (tv_of_tensor dims t)) H = t.
Proof.
case: t H => M H; congr Tensor; apply/matrixP => i j.
rewrite mxE /tv_of_tensor tv_entry_of_entries ?dims_seq_pos ?prod_dims_seq ?ltn_ord //.
have j0 : val j = 0 by case: j => [[|m]] //=; rewrite big_ord0.
have h0 : (0 < \prod_(j < 0) (([tuple] : {posnum nat} ^ 0) j)%:num)%nat by rewrite big_ord0.
rewrite /= (mx_nth_in _ _ _ (ltn_ord i) h0).
by congr (M _ _); apply: val_inj.
Qed.

(** The data of a sized initialiser fills its dims: the read is in range of
    the field its dtype selects, so the default of [nth] is never used, and
    the catch-all branch of [proto_entry] is only taken on a float. *)
Lemma proto_entry_stored t n : tensorProtoSized t -> (n < dims_prod (get_dims t))%nat ->
  let: TensorProto_constructor _ _ _ fd i32 _ i64 _ _ _ _ _ _ _ _ := t in
  [\/ (n < size fd)%nat /\ (forall d, proto_entry t n = R_of_float32 (nth d fd n)),
      (n < size i32)%nat /\ (forall d, proto_entry t n = IZR (Z_of_int32 (nth d i32 n))) |
      (n < size i64)%nat /\ (forall d, proto_entry t n = IZR (Z_of_int64 (nth d i64 n)))].
Proof.
case/tensorProtoSizedP => dims dt ? fd i32 ? i64 ? ? ? ? ? ? ? ? -> /= Dt _ Sz lt.
- apply: Or31; rewrite Sz; split => // d; rewrite /proto_entry /= Dt.
  by congr R_of_float32; apply: set_nth_default; rewrite Sz.
- apply: Or32; rewrite Sz; split => // d; rewrite /proto_entry /= Dt.
  by congr (IZR (Z_of_int32 _)); apply: set_nth_default; rewrite Sz.
- apply: Or33; rewrite Sz; split => // d; rewrite /proto_entry /= Dt.
  by congr (IZR (Z_of_int64 _)); apply: set_nth_default; rewrite Sz.
Qed.

(** An initialiser reads the entries of its proto, all of them in range. *)
Lemma read_init_R_entry t n : tensorProtoSized t -> (n < dims_prod (get_dims t))%nat ->
  exists v, read_init_R t = Some v /\ tv_entry v n = proto_entry t n.
Proof.
move=> sized lt; exists (tv_of_entries (map int64_to_dim (get_dims t)) (proto_entry t)).
rewrite /read_init_R sized; split => //.
rewrite tv_entry_of_entries ?big_map -?dims_prodE // all_map.
exact: tensorProtoSized_pos.
Qed.

(** ** A well-formed graph evaluates

    Every vertex of a well-formed graph evaluates to a value with the dims
    [infer_dims] gives its name, and they are positive.  This is what lets
    the semantics discharge the [option] of [graph_eval]. *)

Lemma val_mxE {T : Type} (A : @tv T) : (size (tag A) <= 2)%nat ->
  all (fun d => 0 < d)%nat (tag A) ->
  exists M, val_mx A = Some (existT _ (mat_of_dims (tag A)) M).
Proof. by case: A => [[|x [|y [|z zs]]] t] //= _ pos; rewrite ?pos; eexists. Qed.

Lemma nat_eqd_eq m n : m = n -> exists e, nat_eqd m n = Some e.
Proof.
move=> <-; elim: m => [|m [e IH]]; first by exists erefl.
by rewrite /= IH; eexists.
Qed.

Lemma tag_map_tv {T : Type} (f : T -> T) (A : @tv T) : tag (map_tv f A) = tag A.
Proof. by case: A. Qed.

Lemma mat_of_dims_pos ds : (size ds <= 2)%nat -> all (fun d => 0 < d)%nat ds ->
  (0 < (mat_of_dims ds).1)%nat /\ (0 < (mat_of_dims ds).2)%nat.
Proof.
case: ds => [|x [|y [|z zs]]] //= _; rewrite ?andbT // => /andP //.
Qed.

Lemma gemm_out_dims_pos attrs da db dc ds :
  all (fun d => 0 < d)%nat da -> all (fun d => 0 < d)%nat db ->
  (size da <= 2)%nat -> (size db <= 2)%nat ->
  gemm_out_dims attrs da db dc = Some ds -> all (fun d => 0 < d)%nat ds.
Proof.
move=> pa pb sa sb /gemm_out_dimsP.
case: (get_gemm_attributes attrs) => [[[? ?] tA] tB] /= [_ _ _ -> _] /=.
have [a1 a2] := mat_of_dims_pos _ sa pa; have [b1 b2] := mat_of_dims_pos _ sb pb.
by rewrite /trans_dims; case: (Z_of_int64 tA); case: (Z_of_int64 tB) => * /=; rewrite ?a1 ?a2 ?b1 ?b2.
Qed.

Lemma gemm_val_fit {T : Type} (ops : elem_ops T) attrs (A B : @tv T) (C : option (@tv T)) ds :
  gemm_out_dims attrs (tag A) (tag B) (omap tag C) = Some ds ->
  all (fun d => 0 < d)%nat (tag A) -> all (fun d => 0 < d)%nat (tag B) ->
  (if C is Some c then all (fun d => 0 < d)%nat (tag c) else true) ->
  exists v, gemm_val ops attrs A B C = Some v /\ tag v = ds.
Proof.
move=> /gemm_out_dimsP + Apos Bpos Cpos; rewrite /gemm_val.
case: (get_gemm_attributes attrs) => [[[al be] tA] tB] /= [sa sb inner -> cok].
have [MA ->] := val_mxE A sa Apos; have [MB ->] := val_mxE B sb Bpos; cbv iota beta.
have [e ->] := nat_eqd_eq _ _ (congr1 dimc (esym inner)); cbv iota beta.
case: C cok Cpos => [c|] /= cok Cpos; last by eexists; split.
have sc : (size (tag c) <= 2)%nat.
  by move: cok; case: (mat_of_dims _) => ? ? /andP [].
have [MC ->] := val_mxE c sc Cpos; cbv iota beta.
by eexists; split.
Qed.

(** Broadcasting reads in range: on dims Gemm accepts, the index of [C] that
    [bcast_mx] asks for always fits, so [bidx] never falls back on [ord0]. *)
Lemma bidx_in x k (H : (k < dimc x)%nat) : bidx x k = Ordinal H.
Proof.
suff gen b (e : (k < dimc x)%nat = b) : b = true ->
    match b as b0 return (k < dimc x)%nat = b0 -> 'I_(dimc x) with
    | true => fun E => Ordinal E
    | false => fun _ => Ordinal (dimc_gt0 x)
    end e = Ordinal H by exact: gen _ erefl H.
by case: b e => // e _; exact: val_inj.
Qed.

Lemma gemm_bcast_in attrs da db dc n p h w i j :
  gemm_out_dims attrs da db (Some dc) = Some [:: n; p] ->
  mat_of_dims dc = (h.+1, w.+1) -> (i < n)%nat -> (j < p)%nat ->
  ((if h == 0 then 0 else i) < h.+1)%nat /\ ((if w == 0 then 0 else j) < w.+1)%nat.
Proof.
move=> /gemm_out_dimsP + Mc lti ltj.
case: (get_gemm_attributes attrs) => [[[? ?] ?] ?] /= [_ _ _ [<- <-]].
rewrite Mc /= => /andP [_]; case: h Mc => [|h] Mc /=.
  move=> /eqP E; split => //.
  by case: w E Mc => [|w] //= E _; rewrite -E in ltj.
case/andP=> /eqP Ei Hw; split; first by rewrite Ei.
case: w Mc Hw => [|w] //= _ /eqP E.
by rewrite E.
Qed.

Lemma bcast_mx_stored {T : Type} attrs da db dc n p h w (C : 'M[T]_(h.+1, w.+1)) (i : 'I_n) (j : 'I_p) :
  gemm_out_dims attrs da db (Some dc) = Some [:: n; p] -> mat_of_dims dc = (h.+1, w.+1) ->
  exists i' j', @bcast_mx _ h.+1 w.+1 n p C i j = C i' j'.
Proof.
move=> G Mc; have [hi hj] := gemm_bcast_in _ _ _ _ _ _ _ _ _ _ G Mc (ltn_ord i) (ltn_ord j).
by exists (Ordinal hi), (Ordinal hj); rewrite /bcast_mx mxE !bidx_in.
Qed.

Section Fits.
Context {T : Type} (ops : elem_ops T) (read_init : TensorProto -> option (@tv T)).
Hypothesis read_init_sized : forall t, tensorProtoSized t ->
  exists v, read_init t = Some v /\ tag v = map int64_to_dim (get_dims t).

Lemma graph_eval_fits nodes inputs initialisers vertices (xs : seq (@tv T)) :
  graph_items nodes inputs initialisers = vertices ->
  graph_acyclic nodes inputs initialisers ->
  (forall i, i \in inputs -> (value_name i != None) && (value_dims i != None)) ->
  (forall t, t \in initialisers -> tensorProtoSized t && (tensor_name t != None)) ->
  all (node_dims_ok (infer_dims nodes inputs initialisers)) nodes ->
  (forall i ds, i \in inputs -> value_dims i = Some ds ->
     exists u, [/\ nth None (map Some xs) (seq.index i inputs) = Some u,
                   tag u = map int64_to_dim ds &
                   all (fun d => 0 < d)%nat (tag u)]) ->
  forall fuel its w, (size its <= fuel)%nat -> {subset its <= vertices} ->
    w \in its -> acyclic_at its w ->
    exists v ds, [/\ graph_eval ops read_init fuel xs inputs vertices w = Some v,
                     infer_dims nodes inputs initialisers (seq.head ""%string (vnames w)) = Some ds,
                     tag v = ds &
                     all (fun d => 0 < d)%nat ds].
Proof.
move=> Hv acyc decl init nodes_ok Hxs.
have uI : uniq (flatten (map vnames vertices)).
  by case/andP: acyc => ub ts; rewrite -Hv vnames_items; exact: topo_sorted_uniq.
elim=> [|fuel IH] its w.
  by rewrite leqn0 => /nilP -> _.
move=> sz sub win ac.
case: w win ac => [n|t|i|o] win ac.
- (** node **)
  have nin : n \in nodes by move: (sub _ win); rewrite -Hv mem_graph_items_node.
  have Nn := allP nodes_ok n nin; have Vn := node_dims_ok_valid_op _ _ Nn.
  have child a : a \in node_inputs n -> exists w v ds,
      [/\ find_vertex vertices a = [:: w],
          graph_eval ops read_init fuel xs inputs vertices w = Some v,
          infer_dims nodes inputs initialisers a = Some ds,
          tag v = ds &
          all (fun d => 0 < d)%nat ds].
    move=> iin; have [w F ac'] := acyclic_at_nodeP ac a iin.
    have wn : w != node n.
      by have [w' F' wn] := acyclic_at_find ac iin; move: F' wn; rewrite F => -[->].
    have wi : w \in rem (node n) its by apply: rem_mem (finds_in F); exact: wn.
    have sz' : (size (rem (node n) its) <= fuel)%nat.
      by rewrite size_rem // -subn1 leq_subLR add1n.
    have [v [ds [E S Tv Pv]]] := IH _ w sz' (fun z zi => sub z (mem_rem zi)) wi ac'.
    exists w, v, ds; split => //.
    + apply: find_vertex_uniq uI (sub _ (finds_in F)) _.
      have : w \in find_vertex its a by rewrite F mem_head.
      by rewrite find_vertexE mem_filter vertex_has_nameE => /andP [].
    + rewrite -(graph_dims_find nodes inputs initialisers _ its a w nodes_ok _ F) //.
      by rewrite Hv.
  move: Nn Vn child {win ac nin}.
  case: n => ins outs nm [op|] dom ov attrs doc meta x Nn Vn child //.
  case: (String.eqb_spec op """Gemm""") => [E|ne]; first subst op.
    case: ins Nn Vn child => [|a [|b [|c [|? ?]]]] //= Nn Vn child.
    + (** Gemm, two inputs **)
      have [wa [A [da [Fa Ea Sa Ta Pa]]]] := child a (mem_head _ _).
      have [wb [B [db [Fb Eb Sb Tb Pb]]]] := child b ltac:(by rewrite !inE eqxx orbT).
      case/node_dims_ok_gemm2: Nn => da' [db' [ds [Ha Hb G Ho]]].
      move: Ha Hb; rewrite Sa Sb -Ta -Tb => -[Ea'] [Eb'].
      rewrite -Ea' -Eb' in G.
      rewrite -Ta in Pa; rewrite -Tb in Pb.
      have [v [Ev Tv]] := gemm_val_fit ops attrs A B None ds G Pa Pb isT.
      exists v, ds; rewrite Fa Fb Ea Eb; split => //.
      move: (gemm_out_dimsP _ _ _ _ _ G); case: (get_gemm_attributes attrs) => [[[? ?] ?] ?] /= [sa sb _ _ _].
      exact: (gemm_out_dims_pos _ _ _ _ _ Pa Pb sa sb G).
    + (** Gemm, three inputs **)
      have [wa [A [da [Fa Ea Sa Ta Pa]]]] := child a (mem_head _ _).
      have [wb [B [db [Fb Eb Sb Tb Pb]]]] := child b ltac:(by rewrite !inE eqxx orbT).
      have [wc [C [dc [Fc Ec Sc Tc Pc]]]] := child c ltac:(by rewrite !inE eqxx !orbT).
      case/node_dims_ok_gemm3: Nn => da' [db' [dc' [ds [Ha Hb Hc G Ho]]]].
      move: Ha Hb Hc; rewrite Sa Sb Sc -Ta -Tb -Tc => -[Ea'] [Eb'] [Ec'].
      rewrite -Ea' -Eb' -Ec' in G.
      rewrite -Ta in Pa; rewrite -Tb in Pb; rewrite -Tc in Pc.
      have [v [Ev Tv]] := gemm_val_fit ops attrs A B (Some C) ds G Pa Pb Pc.
      exists v, ds; rewrite Fa Fb Fc Ea Eb Ec; split => //.
      move: (gemm_out_dimsP _ _ _ _ _ G); case: (get_gemm_attributes attrs) => [[[? ?] ?] ?] /= [sa sb _ _ _].
      exact: (gemm_out_dims_pos _ _ _ _ _ Pa Pb sa sb G).
  move: Vn => /=; move/String.eqb_neq: ne => -> Vn.
  case: (String.eqb_spec op """Relu""") Vn => [E|ne] //; subst op => Vn.
  case: ins Nn Vn child => [|a [|? ?]] //= Nn Vn child.
  have [wa [A [da [Fa Ea Sa Ta Pa]]]] := child a (mem_head _ _).
  have Ho := node_dims_ok_relu _ _ _ _ _ _ _ _ _ _ Nn.
  exists (map_tv (relu ops) A), da; rewrite Fa Ea tag_map_tv; split => //.
  by rewrite Ho.
- (** initialiser **)
  have tin : t \in initialisers by move: (sub _ win); rewrite -Hv mem_graph_items_tensor.
  case/andP: (init t tin) => sized; case E: (tensor_name t) => [s|] // _.
  have [v [Ev Tv]] := read_init_sized t sized.
  exists v, (map int64_to_dim (get_dims t)); split => //.
  + by rewrite /= E /=; exact: infer_dims_initialiser acyc tin E.
  + rewrite all_map; apply: sub_all (tensorProtoSized_pos _ sized) => d //.
- (** graph input **)
  have iin : i \in inputs by move: (sub _ win); rewrite -Hv mem_graph_items_input.
  case/andP: (decl i iin); case En: (value_name i) => [s|] // _.
  case Ed: (value_dims i) => [ds|] // _.
  have [u [Eu Tu Pu]] := Hxs i _ iin Ed.
  exists u, (map int64_to_dim ds); split => //.
  + by rewrite /= En /=; exact: infer_dims_input acyc iin En Ed.
  + by rewrite -Tu.
- (** an output is never a vertex **)
  by move: (sub _ win); rewrite -Hv output_notin_graph_items.
Qed.

End Fits.

(** ** Simplifying the semantics of a closed model

    [cbv] evaluates the walk and every lookup; the matrix and tensor
    operations, the reading of the entries and the algebraic structures on real
    matrices are kept folded.  The tensor operations have dims that are products
    in their types, which [cbv] must not normalise.  The default Gemm attribute
    alpha is 1, which the last rewrite turns into [GRing.one].  Only the left
    hand side, the evaluation, is normalised; the right hand side is left as
    stated. *)
Ltac graph_eval_simp :=
  match goal with
  | |- ?lhs = ?rhs =>
    let lhs' := eval cbv -[mx_shape_num mx_shape_dim mx_dim_default finfun_of_tuple cons_tuple nil_tuple
        map_t mx_of_tensor tensor_of_mx tensor_val tensor_nil nindex col_tensor castmx
        mulmx trmx GRing.scale GRing.one GRing.zero map_mx Order.max
        R_of_float32 Binary.binary_normalize default_one float_zero proto_entry relumx
        RbaseSymbolsImpl_R__canonical__GRing_SemiRing
        RbaseSymbolsImpl_R__canonical__Order_Preorder
        matrix_matrix__canonical__GRing_LSemiModule
        RbaseSymbolsImpl_R__canonical__Algebra_BaseAddUMagma] in lhs in
    change (lhs' = rhs)
  end;
  rewrite ?R_of_default_one.

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

Local Notation f32 n := (Binary.binary_normalize 24 128 erefl erefl BinarySingleNaN.mode_NE n%Z 0 false).

Definition W1_proto := ftensor "W1" [:: 2; 2] [:: f32 2; f32 1; f32 (-1); f32 1].
Definition W2_proto := ftensor "W2" [:: 1; 2] [:: f32 (-1); f32 2].

Definition toy : ModelProto :=
  ModelProto_constructor None [::] None None None None None
    (Some (GraphProto_constructor
             [:: gemm_node "g1" [:: "x"; "W1"] "h"; relu_node "r" "h" "a";
                 gemm_node "g2" [:: "a"; "W2"] "y"]
             (Some "toy") [:: W1_proto; W2_proto] [::] None
             [:: vinfo "x" [:: 1; 2]] [:: vinfo "y" [:: 1; 1]] [::] [::] [::]))
    [::] [::] [::] [::].

Definition W1 : 'M[R]_(2, 2) := col_tensor [:: 2; 2] (proto_entry W1_proto).
Definition W2 : 'M[R]_(1, 2) := col_tensor [:: 1; 2] (proto_entry W2_proto).

Definition toy_dnn
  (x : 'nT[R]_([tuple 1%:posnat; 2%:posnat]))
  : 'nT[R]_([tuple 1%:posnat; 1%:posnat]) :=
  let W1 := \matrix_(i < 2, j < 2) nth 0%R (nth [::] [:: [:: 2%R; 1%R]; [:: -1; 1]]%R i) j in
  let W2 := \matrix_(i < 1, j < 2) nth 0%R [:: -1; 2]%R j in
  (relumx (x *m W1^T)) *m W2^T.

Lemma R_of_f32 (n : Z) : (Z.abs n < 2 ^ 24)%Z -> R_of_float32 (f32 n) = IZR n.
Proof.
move=> nb.
have H := Binary.binary_normalize_correct 24 128 erefl erefl BinarySingleNaN.mode_NE n 0 false.
have F : Defs.F2R (Defs.Float radix2 n 0) = IZR n by rewrite /Defs.F2R /= Rmult_1_r.
have fmt : FLT.FLT_format radix2 (-149) 24 (IZR n).
  by apply: (FLT.FLT_spec _ _ _ _ (Defs.Float radix2 n 0)) => //=.
rewrite F Generic_fmt.round_generic in H;
  try exact: (FLT.generic_format_FLT radix2 (-149) 24 _ fmt).
have Hlt : Rlt (Rabs (IZR n)) (Raux.bpow radix2 128).
  rewrite Rabs_Zabs; apply: (Rlt_trans _ (IZR (2 ^ 24))); first exact: IZR_lt.
  by apply: IZR_lt.
rewrite (Raux.Rlt_bool_true _ _ Hlt) in H.
by case: H => [HB _]; rewrite /R_of_float32 HB.
Qed.

(** The weights of [toy], as they are written in [toy_dnn]. *)
Lemma W1E : W1 = \matrix_(i < 2, j < 2) nth 0%R (nth [::] [:: [:: 2%R; 1%R]; [:: -1; 1]]%R i) j.
Proof.
apply/matrixP => i j; rewrite /W1 (@mx_of_col_tensor 2 2) // mxE.
case: i => [[|[|?]] ?] //; case: j => [[|[|?]] ?] //;
  rewrite /proto_entry /W1_proto;
  cbv -[Binary.binary_normalize R_of_float32 GRing.natmul GRing.opp GRing.one];
  by rewrite R_of_f32.
Qed.

Lemma W2E : W2 = \matrix_(i < 1, j < 2) nth 0%R [:: -1; 2]%R j.
Proof.
apply/matrixP => i j; rewrite /W2 (@mx_of_col_tensor 1 2) // mxE (ord1 i) /=.
case: j => [[|[|?]] ?] //;
  rewrite /proto_entry /W2_proto;
  cbv -[Binary.binary_normalize R_of_float32 GRing.natmul GRing.opp GRing.one];
  by rewrite R_of_f32.
Qed.

Lemma toy_sem (x : 'nT[R]_([tuple 1%:posnat; 2%:posnat])) :
  real_eval toy [:: mk [:: 1; 2] x] = Some [:: mk [:: 1; 1] (toy_dnn x)].
Proof.
graph_eval_simp.
rewrite /toy_dnn -W1E -W2E.
refine (congr1 (fun t => Some [:: @mk R [:: 1; 1] t])
          (congr1 (@tensor_of_mx _ _ (mx_shape_num (dim_pos 1) (dim_pos 1)) R) _)).
by rewrite GRing.scale1r mx_of_map_t tensor_of_mxK GRing.scale1r !castmx_id !tensor_of_mxK.
Qed.
