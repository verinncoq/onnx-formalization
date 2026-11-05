Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.

From Stdlib Require Import Rdefinitions Reals.
From mathcomp Require Import boot algebra order reals Rstruct.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith Lia Init.Byte Strings.Byte.
From ONNXFormalization.ProtobufDatatypes Require Export float.
From ONNXFormalization.ProtobufDatatypes Require Export int.
From ONNXFormalization.ProtobufDatatypes Require Export bytes.
From Flocq Require Import Core Bits.
From ONNXFormalization.VNNLIB.ONNX Require Import Syntax Semantics mc_inst real.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem graph_eval inst_reals.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

Definition empty_model : ModelProto :=
  ModelProto_constructor None nil None None None None None None nil nil nil nil.

(* Type checks *)
Definition test := onnx_evaluator empty_model nil.

Compute test.

Lemma Hprec32 : FLX.Prec_gt_0 24. Proof. reflexivity. Qed.
Lemma Hmax32  : BinarySingleNaN.Prec_lt_emax 24 128. Proof. reflexivity. Qed.

Definition f32 (n : Z) : binary32 :=
  Binary.binary_normalize 24 128 Hprec32 Hmax32 BinarySingleNaN.mode_NE n 0 false.

Definition W1 : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 2; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 2; f32 1; f32 (-1); f32 1] nil nil nil (Some """W1"""%string) None None nil None nil nil nil.

Definition W2 : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """W2"""%string) None None nil None nil nil nil.

(** x : float[1,2] --Gemm(W1, transB=1)--> z --Relu--> v --Gemm(W2, transB=1)--> y : float[1,1] *)
Definition g : GraphProto :=
  let float_ty := Some (int32_of_Z 1) in
  let vinfo nm (ds : seq Z) :=
    ValueInfoProto_constructor (Some nm)
      (Some (TypeProto_constructor
               (Some (tensor_type_value_TypeProto
                        (Tensor_TypeProto_constructor float_ty
                           (Some (TensorShapeProto_constructor
                                    [seq Dimension_TensorShapeProto_constructor
                                         (Some (dim_value_value_Dimension_TensorShapeProto (int64_of_Z d))) None
                                    | d <- ds]))))) None))
      None nil in
  let transB1 :=
    AttributeProto_constructor (Some """transB"""%string) None None (Some INT_AttributeProto)
      None (Some (int64_of_Z 1)) None None None None nil nil nil nil nil nil in
  let gemm a b out :=
    NodeProto_constructor [:: a; b] [:: out] None (Some """Gemm"""%string) None None
      [:: transB1] None nil nil in
  let relu a out :=
    NodeProto_constructor [:: a] [:: out] None (Some """Relu"""%string) None None
      nil None nil nil in
  GraphProto_constructor
    [:: gemm """x"""%string """W1"""%string """z"""%string;
        relu """z"""%string """v"""%string;
        gemm """v"""%string """W2"""%string """y"""%string]
    None
    [:: W1; W2]
    nil
    None
    [:: vinfo """x"""%string [:: 1; 2]%Z]
    [:: vinfo """y"""%string [:: 1; 1]%Z]
    [:: vinfo """z"""%string [:: 1; 2]%Z; vinfo """v"""%string [:: 1; 2]%Z]
    nil nil.

Definition model : ModelProto :=
  ModelProto_constructor None nil None None None None None (Some g) nil nil nil nil.

(* Compute (onnx_evaluator model). *)

Definition x : TensorProto :=
  TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """x"""%string) None None nil None nil nil nil.

Definition emap {T T'} (f : T -> T') (x : error_option T) : error_option T' :=
match x with
| Success x => Success (f x)
| Error x => Error x
end.

Definition ebind {T T'} (x : error_option T) (f : T -> error_option T') : error_option T' :=
match x with
| Success x' => f x'
| Error x => Error x
end.

Definition eapp {T T'} (f : error_option (T -> T')) (x : error_option T) :
  error_option T' :=
match f with
| Success f' => match x with
             | Success x' => Success (f' x')
             | Error x => Error x
             end
| Error x => Error x
end.

Definition toy_dnn (x : TensorProto) : error_option TensorProto :=
  let W1 := TensorProto_constructor [:: int64_of_Z 2; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 2; f32 1; f32 (-1); f32 1] nil nil nil (Some """W1"""%string) None None nil None nil nil nil in
  let W2 := TensorProto_constructor [:: int64_of_Z 1; int64_of_Z 2] (Some (int32_of_Z 1)) None [:: f32 (-1); f32 2] nil nil nil (Some """W2"""%string) None None nil None nil nil nil in
  emap tensor_of_matrix_float32 (ebind (emap (map (map relu_float32)) (ebind (matrix_float32_of_tensor x) (fun x =>
                                                                                                             ebind (matrix_float32_of_tensor W1) (fun y => gemm_float32 x y [:: [:: f32 0]] (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::])))) (fun x => ebind (matrix_float32_of_tensor W2) (fun y => gemm_float32 x y [:: [:: f32 0]] (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::]))).

Definition toy_dnn' {R : numFieldType}
  (x : 'nT[R]_([tuple 1%:posnat; 2%:posnat]))
  : 'nT[R]_([tuple 1%:posnat; 1%:posnat]) :=
  let W1 := \matrix_(i < 2, j < 2) nth 0%R (nth [::] [:: [:: 2%R; 1%R]; [:: -1; 1]]%R i) j in
  let W2 := \matrix_(i < 1, j < 2) nth 0%R [:: -1; 2]%R j in
    (map_mx (fun x => if 0%R < x then x else 0%R) (x *m W1^T)) *m W2^T.

Definition networkType : NetworkType Elem :=
  {|
    inputs := exist (fun s => (0 < size s)%nat) [:: tensorType Elem (exist _ FLOAT_TensorProto isT) (existT (fun k => {posnum nat} ^ k)%type 2%N [ffun i : 'I_2 => tnth [:: 1%:posnat; 2%:posnat] i])] isT;
    outputs := exist (fun s => (0 < size s)%nat) [:: tensorType _ (exist _ FLOAT_TensorProto isT) (existT (fun k => {posnum nat} ^ k)%type 2%N [ffun i : 'I_2 => tnth [:: 1%:posnat; 1%:posnat] i])] isT;
  |}.

Lemma network_dims_matches : network_dim_match model networkType.
Proof.
rewrite /network_dim_match /= !andbT.
apply/andP; split; apply/andP; split => //; rewrite /omap /=; apply/eqP/f_equal;
  (have -> : fintype.enum 'I_2 = [:: ord0; ord_max] by
     apply: (inj_map val_inj); rewrite val_enum_ord);
  by rewrite /= !ffunE.
Qed.

Lemma well_formed : model_well_formed model.
Proof. by []. Qed.

Definition model' : well_formed_model networkType
  := exist _ model
       ([eta introTF (c:=true) andP] (conj network_dims_matches well_formed)).

Program Definition seq1_head {T} (xs : seq1 T) : T :=
match xs with
| nil => _
| cons x _ => x
end.
Next Obligation.
move: xs Heq_xs.
case.
by case.
Qed.

Lemma idk : NodeOutput syntax_inst model' """y"""%string
          (seq1_head (outputs Elem networkType)).
Proof.
rw /=.
rw /model /graph_outputs /=.
exists (ValueInfoProto_constructor (Some """y"""%string)
                    (Some
                       (TypeProto_constructor
                          (Some
                             (tensor_type_value_TypeProto
                                (Tensor_TypeProto_constructor 
                                   (Some (int32_of_Z 1))
                                   (Some
                                      (TensorShapeProto_constructor
                                         [:: Dimension_TensorShapeProto_constructor
                                               (Some
                                                  (dim_value_value_Dimension_TensorShapeProto
                                                     (int64_of_Z 1)))
                                               None;
                                             Dimension_TensorShapeProto_constructor
                                               (Some
                                                  (dim_value_value_Dimension_TensorShapeProto
                                                     (int64_of_Z 1)))
                                               None])))))
                          None))
                    None [::]).
apply/and4P.
split => //.
rw /omap /=.
apply/eqP/f_equal.
have -> : fintype.enum 'I_2 = [:: ord0; ord_max].
by apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite /= !ffunE /=.
by [].
Qed.

Definition abc (x : InputSemantics (@realElementTypeInterp R)
    {| inputs := exist (fun s => (0 < size s)%nat)
         [:: tensorType RealElementType real (existT (fun k => {posnum nat} ^ k)%type 2%N [tuple 1%:posnat; 2%:posnat])] isT;
       outputs := exist (fun s => (0 < size s)%nat)
         [:: tensorType RealElementType real (existT (fun k => {posnum nat} ^ k)%type 2%N [tuple 1%:posnat; 1%:posnat])] isT |})
  : 'nT[R]_([tuple 1%:posnat; 1%:posnat]).
Proof.
refine (realSemantics networkType _ (seq1_head (outputs _ networkType))
    (tensorType RealElementType real (existT (fun k => {posnum nat} ^ k)%type 2%N [tuple 1%:posnat; 1%:posnat]))
    """y"""%string model' _ x idk (eqxx _)).
exact (introT andP (conj (introT andP (conj (eqxx _) isT)) (introT andP (conj (eqxx _) isT)))).
Defined.

Local Notation W1m := (col_tensor [:: 2; 2]%nat (proto_entry W1) : 'M[R]_(2, 2)).
Local Notation W2m := (col_tensor [:: 1; 2]%nat (proto_entry W2) : 'M[R]_(1, 2)).

Lemma ev (X : 'M[R]_(1, 2)) :
  real_name_eval model """y"""%string [:: mk [:: 1; 2]%nat X]
  = Some (mk [:: 1; 1]%nat (relumx (X *m W1m^T) *m W2m^T)).
Proof.
cbv -[f32 mx_shape_num mx_shape_dim mx_dim_default finfun_of_tuple cons_tuple nil_tuple
      map_t mx_of_tensor tensor_of_mx tensor_val tensor_nil nindex col_tensor castmx
      mulmx trmx GRing.scale GRing.one GRing.zero map_mx Order.max
      R_of_float32 default_one float_zero proto_entry relumx
      RbaseSymbolsImpl_R__canonical__GRing_SemiRing
      RbaseSymbolsImpl_R__canonical__Order_Preorder
      matrix_matrix__canonical__GRing_LSemiModule
      RbaseSymbolsImpl_R__canonical__Algebra_BaseAddUMagma].
rewrite ?R_of_default_one.
refine (congr1 (fun t => Some (@mk R [:: 1; 1]%nat t)) (_ : tensor_of_mx _ = tensor_of_mx _)).
congr (tensor_of_mx _).
rewrite GRing.scale1r mx_of_map_t tensor_of_mxK GRing.scale1r tensor_of_mxK !castmx_id.
reflexivity.
Qed.


Lemma dims_seq12 : dims_seq ([tuple 1%:posnat; 2%:posnat] : {posnum nat} ^ 2) = [:: 1; 2]%nat.
Proof.
have E2 : fintype.enum 'I_2 = [:: ord0; ord_max] by apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite /dims_seq /= E2 /=.
by rewrite !ffunE.
Qed.

Lemma value_11 (M : 'M[R]_(1, 1)) :
  (@Tensor _ _ _ _ _ (\matrix_(i, j) tv_entry (mk [:: 1; 1]%nat M) i)
     : 'nT[R]_([tuple 1%:posnat; 1%:posnat])) =
  (M : 'nT[R]_([tuple 1%:posnat; 1%:posnat])).
Proof.
apply: (can_inj (@mx_of_tensorK _ _ _ _)); rewrite tensor_of_mxK.
apply/matrixP => i j.
rewrite (@mx_of_tensor_nth 1%:posnat 1%:posnat) /= (ord1 j) (ord1 i) /=.
rewrite (nth_col (fun n => tv_entry (mk [:: 1; 1]%nat M) n)); try exact: prod_pos.
have := @mx_of_tensor_nth (dim_pos 1) (dim_pos 1) (M : 'nT[R]_(projT2 (dims_type [:: 1; 1]%nat))) ord0 ord0.
by rewrite tensor_of_mxK.
Qed.

Lemma input_12 (t : 'nT[R]_([tuple 1%:posnat; 2%:posnat])) :
  tv_of_tensor ([tuple 1%:posnat; 2%:posnat]) t = mk [:: 1; 2]%nat (t : 'M[R]_(1, 2)).
Proof.
rewrite /tv_of_tensor dims_seq12 /tv_of_entries; congr (mk _ _).
apply: (can_inj (@mx_of_tensorK _ _ _ _)); rewrite tensor_of_mxK.
apply/matrixP => i j.
by rewrite (@mx_of_col_tensor 1 2) // (@mx_of_tensor_nth 1%:posnat 2%:posnat).
Qed.

Lemma f32_val (n : Z) : (Z.abs n < 2 ^ 24)%Z -> R_of_float32 (f32 n) = IZR n.
Proof.
move=> nb.
have H := Binary.binary_normalize_correct 24 128 Hprec32 Hmax32 BinarySingleNaN.mode_NE n 0 false.
have F : Defs.F2R (Defs.Float radix2 n 0) = IZR n by rewrite /Defs.F2R /= Rmult_1_r.
have fmt : FLT.FLT_format radix2 (-149) 24 (IZR n).
  by apply: (FLT.FLT_spec _ _ _ _ (Defs.Float radix2 n 0)) => //=.
rewrite F Generic_fmt.round_generic in H;
  try exact: (FLT.generic_format_FLT radix2 (-149) 24 _ fmt).
have Hlt : Rlt (Rabs (IZR n)) (Raux.bpow radix2 128).
  rewrite Rabs_Zabs; apply: (Rlt_trans _ (IZR (2 ^ 24))); first exact: IZR_lt.
  by apply: IZR_lt.
rewrite (Raux.Rlt_bool_true _ _ Hlt) in H.
by case: H => [HB _]; rewrite /R_of_float32 /f32 HB.
Qed.

Lemma R_f32_1 : R_of_float32 (f32 1) = 1%R.
Proof. by rewrite f32_val. Qed.
Lemma R_f32_2 : R_of_float32 (f32 2) = 2%R.
Proof.
by rewrite f32_val.
Qed.
Lemma R_f32_m1 : R_of_float32 (f32 (-1)) = (-1)%R.
Proof.
by rewrite f32_val.
Qed.

Lemma W1mE : W1m = \matrix_(i < 2, j < 2) nth 0%R (nth [::] [:: [:: 2%R; 1%R]; [:: -1; 1]]%R i) j.
Proof.
apply/matrixP => i j; rewrite (@mx_of_col_tensor 2 2) // !mxE.
case: i => [[|[|?]] ?] //; case: j => [[|[|?]] ?] //;
rewrite /proto_entry /W1; cbv -[f32 R_of_float32 GRing.natmul GRing.opp GRing.one];
  by rewrite ?R_f32_1 ?R_f32_2 ?R_f32_m1.
Qed.

Lemma W2mE : W2m = \matrix_(i < 1, j < 2) nth 0%R [:: -1; 2]%R j.
Proof.
apply/matrixP => i j; rewrite (@mx_of_col_tensor 1 2) // !mxE (ord1 i) /=.
case: j => [[|[|?]] ?] //;
rewrite /proto_entry /W2; cbv -[f32 R_of_float32 GRing.natmul GRing.opp GRing.one];
  by rewrite ?R_f32_2 ?R_f32_m1.
Qed.

Lemma abc_toy_dnn' x : abc x = toy_dnn' (x ord0).
Proof.
graph_eval_simp.
have E1 : fintype.enum 'I_1 = [:: ord0] by apply: (inj_map val_inj); rewrite val_enum_ord.
have Ev : real_name_eval model """y"""%string
            [:: tv_of_tensor ([tuple 1%:posnat; 2%:posnat]) (x ord0)] =
          Some (mk [:: 1; 1]%nat (relumx ((x ord0 : 'M[R]_(1, 2)) *m W1m^T) *m W2m^T)).
  by rewrite input_12 ev.
rewrite /abc /realSemantics /sem_of_value; cbv beta iota.
rewrite (tensor_of_valueE _ _ _
  (mk [:: 1; 1]%nat (relumx ((x ord0 : 'M[R]_(1, 2)) *m W1m^T) *m W2m^T))).
  rewrite -Ev /input_tvs; cbv beta iota.
  change (fintype.enum 'I_(size _)) with (fintype.enum 'I_1).
  by rewrite E1.
rewrite value_11 /toy_dnn' W1mE W2mE.
congr (tensor_of_mx (_ *m _)).
by apply: eq_map_mx => v; rewrite maxC maxElt.
Qed.

(* Lemma result (x : sized_tensor) : *)
(*   forall x', (matrix_float32_of_tensor (val x)) = Success x' -> *)
(*         forall W1', (matrix_float32_of_tensor W1) = Success W1' -> *)
(*                forall W2', (matrix_float32_of_tensor W2) = Success W2' -> *)
(*                       let x'' := (smap tensor_of_matrix_float32 (gemm_float32 x' W1' [:: [:: f32 0]] *)
(*                                                                    (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::])) in *)
(*   onnx_evaluator model [:: (val (val x))] = smap (fun x => cons (tensor_of_matrix_float32 x) [::]) *)
(*   (sbind (fun a => gemm_float32 a W2' [:: [:: f32 0]] *)
(*   (f32 1) (f32 1) (int64_of_Z 0) (int64_of_Z 1) [::]) (sbind matrix_float32_of_tensor (x''))) *)
(*  . *)
(* Proof. *)
