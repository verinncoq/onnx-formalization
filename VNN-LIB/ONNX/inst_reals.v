Set Warnings "-notation-overridden,-ambiguous-paths".
From ONNXFormalization.ONNXConverter Require Import model.

From Stdlib Require Import Rdefinitions.
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
From ONNXFormalization.VNNLIB.ONNX Require Import inst_syntax inst_sem graph_eval.
From ONNXFormalization.ONNXEvaluator Require Import onnx_evaluator op_comp op_add op_matmul op_neg.
Import Order.TTheory.
Import Order.DefaultSeqProdOrder.
Import Order.DefaultProdOrder.
Open Scope order_scope.
Import EqNotations.
Open Scope quotient_scope.

(********************************************)
(**************** REALS *********************)
(********************************************)

(** The real semantics of a network is [real_name_eval] of [graph_eval], and
    it computes: a closed model reduces to the matrix expression it denotes.
    The evaluator's [option] is discharged by [real_name_eval_fits]: on a
    well-formed model with matching inputs, a declared output always evaluates,
    to the declared dims. *)

Definition tv_of_sem (d : TensorType RealElementType)
  : TensorSemantics (@realElementTypeInterp R) d -> @tv R :=
  match d with
  | tensorType _ (existT _ dims) => @tv_of_tensor _ dims
  end.

(** The user inputs in position order. *)
Definition input_tvs (y : NetworkType RealElementType)
  : InputSemantics (@realElementTypeInterp R) y -> seq (@tv R) :=
  match y with
  | networkType ins _ => fun inp =>
      [seq tv_of_sem _ (inp i) | i <- fintype.enum 'I_(size ins)]
  end.

Lemma tag_tv_of_sem d (t : TensorSemantics (@realElementTypeInterp R) d) :
  tag (tv_of_sem d t) = dims_seq (projT2 (tensorDims _ d)).
Proof. by case: d t => tt [k dims] t. Qed.

Lemma real_name_eval_fits y1 y2 d1 (d2 : TensorType RealElementType) u (m : well_formed_model y1) :
  NetworkShapesMatch y1 y2 ->
  forall inp : InputSemantics (@realElementTypeInterp R) y2,
  nodeOutput y1 m u d1 -> TensorShapesMatch d1 d2 ->
  value_fits (projT2 (tensorDims _ d2)) (real_name_eval (proj1_sig m) u (input_tvs y2 inp)).
Proof.
move: y1 y2 m => [[inps g1] [outs g2]] [[inps' g3] [outs' g4]] [m dmwf] sm inp.
case=> o /and3P [oin /eqP oname otype] d12.
cbv beta iota delta [proj1_sig].
case/andP: dmwf => dm wf; case/andP: sm => in_match _.
case: m dm wf oin => ir opset prod_name prod_vers domain model_version doc
  [[nodes name initialisers sparse_initialisers doc_string inputs outputs value_info
    quantisation metadata_props]|//] metadata training functions config dm wf oin.
rewrite /= in dm wf oin.
case/and5P: wf => acyc /allP outs_one /allP decl /allP init_ok /and3P [nodes_ok /allP o_sh _].
have Hsz : size inps = size inputs.
  by move/andP: dm => [+ _]; rewrite all2E => /andP [/eqP].
have Hsz' : size inps' = size inps.
  by move: in_match; rewrite all2E => /andP [/eqP].
(** the user input at a graph input's position has the input's declared dims **)
have Hxs : forall v ds, v \in inputs -> value_dims v = Some ds ->
    exists u0, [/\ nth None (map Some [seq tv_of_sem _ (inp i) | i <- fintype.enum 'I_(size inps')])
                     (seq.index v inputs) = Some u0,
                   tag u0 = map int64_to_dim ds &
                   all (fun d => 0 < d)%nat (tag u0)].
  move=> v ds vin Evd.
  have ilt : (seq.index v inputs < size inps)%nat by rewrite Hsz index_mem.
  have ilt' : (seq.index v inputs < size inps')%nat by rewrite Hsz'.
  have vt_ok : value_has_type (tnth (in_tuple inps) (Ordinal ilt)) v.
    move/andP: dm => [+ _]; rewrite all2E => /andP [_ /all_nthP same].
    have := same (tnth (in_tuple inps) (Ordinal ilt), v) (seq.index v inputs).
    rewrite nth_zip_cond size_zip -Hsz minnn ilt => /(_ isT) /=.
    by rewrite nth_index // -(tnth_nth _ (in_tuple inps) (Ordinal ilt)).
  have vt_match : TensorShapesMatch (tnth (in_tuple inps) (Ordinal ilt))
                                    (tnth (in_tuple inps') (Ordinal ilt')).
    move: in_match; rewrite all2E => /andP [_ /all_nthP same].
    have := same (tnth (in_tuple inps) (Ordinal ilt), tnth (in_tuple inps') (Ordinal ilt'))
                 (seq.index v inputs).
    have imin : (seq.index v inputs < minn (size inps) (size inps'))%nat by rewrite Hsz' minnn.
    rewrite nth_zip_cond size_zip imin => /(_ isT) /=.
    by rewrite -(tnth_nth _ (in_tuple inps) (Ordinal ilt))
               -(tnth_nth _ (in_tuple inps') (Ordinal ilt')).
  pose u0 := tv_of_sem _ (inp (Ordinal ilt')).
  exists u0; split.
  - have En : nth (Ordinal ilt') (fintype.enum 'I_(size inps')) (seq.index v inputs) = Ordinal ilt'
      := nth_ord_enum (Ordinal ilt') (Ordinal ilt').
    have Some_nth (s : seq (@tv R)) k : (k < size s)%nat ->
        nth None (map Some s) k = Some (nth u0 s k).
      by elim: s k => //= a s IH [|k] //= /IH.
    rewrite Some_nth; first by rewrite size_map size_enum_ord.
    congr Some; rewrite /u0 (nth_map (Ordinal ilt')); first by rewrite size_enum_ord.
    by rewrite En.
  - rewrite /u0 tag_tv_of_sem.
    move: vt_ok vt_match; rewrite /value_has_type Evd /= => /andP [_ /eqP [E]] /eqP Ed.
    by rewrite E /dims_seq -Ed.
  - by rewrite /u0 tag_tv_of_sem; exact: dims_seq_pos.
have decl' i : i \in inputs -> (value_name i != None) && (value_dims i != None).
  by move=> iin; move: (decl i); rewrite mem_cat iin => /(_ isT) /and4P [_ _ -> ->].
have init' t : t \in initialisers -> tensorProtoSized t && (tensor_name t != None).
  by move/init_ok => /and3P [_ -> ->].
(** model_well_formed: the output names exactly one vertex, a node **)
have Hone := outs_one o oin.
case: o oin oname otype Hone => [[nm|] ot od om] oin oname otype Hone; last by [].
subst u.
have {Hone} : if find_vertex (graph_items nodes inputs initialisers) nm is [:: node _]
              then true else false := Hone.
case F: (find_vertex (graph_items nodes inputs initialisers) nm) => [|w [|? ?]] //; last by case: w F.
case: w F => // n F _.
have win := finds_in F.
have ac := graph_acyclic_at (node n) acyc win.
rewrite /real_name_eval /name_eval; cbv beta iota zeta delta [value_info_name]; rewrite F /input_tvs; cbv beta iota.
have [v [ds [E S Tv _]]] := graph_eval_fits real_ops read_init_R read_init_R_sized
  nodes inputs initialisers _ _ erefl acyc decl' init' nodes_ok Hxs _ _ (node n) (leqnSn _)
  (fun _ x => x) win ac.
rewrite E.
(** the value has the output's declared dims, which are d1's, which are d2's **)
move: S; rewrite (graph_dims_find nodes inputs initialisers _ _ _ _ nodes_ok (fun _ x => x) F).
set ov := ValueInfoProto_constructor (Some nm) ot od om in oin otype *.
move: (o_sh _ oin) otype; cbv beta; rewrite /value_has_type (_ : value_name ov = Some nm) //.
case: (value_dims ov) => [l|] //= /eqP -> /andP [_ /eqP [odims]] [Eds].
by apply/eqP; rewrite Tv -Eds odims /dims_seq -(eqP d12).
Qed.

Definition sem_of_value (d : TensorType RealElementType) (o : option (@tv R))
  : value_fits (projT2 (tensorDims _ d)) o -> TensorSemantics (@realElementTypeInterp R) d :=
  match d with
  | tensorType _ (existT _ dims) => @tensor_of_value _ dims o
  end.

Definition realSemantics : @RealNetworkSemantics syntax_inst R :=
  fun y1 y2 d1 d2 u m sm inp out d12 =>
    sem_of_value d2 _ (real_name_eval_fits y1 y2 d1 d2 u m sm inp out d12).

(* Section RealEvaluator. *)
(* Context (r : realType). *)

(* Local Open Scope ring_scope. *)

(* Local Notation realTensor := *)
(*   {d : TensorType RealElementType & TensorSemantics (@realElementTypeInterp r) d}. *)

(* Context (R_of_float32 : float32 -> r) (IZR : Z -> r). *)

(* Lemma prod_ord0 (f : 'I_0 -> nat) : \prod_(j < 0) f j = 1%nat. *)
(* Proof. by rewrite big_ord0. Qed. *)

(* Lemma prod_ord2 (h w : {posnum nat}) : *)
(*   (h%:num * w%:num)%nat = \prod_(i < 2) ([ffun i => tnth [tuple h; w] i] i)%:num. *)
(* Proof. by rewrite !big_ord_recl big_ord0 !ffunE /= GRing.mulr1. Qed. *)

(* (*tensor-to-matrix: reshape a tensor into an h x w matrix (row-major)*) *)
(* Definition as_matrix (x : realTensor) (h w : nat) : option 'M[r]_(h, w) := *)
(*   match x with *)
(*   | existT (tensorType _ (existT k dims)) t => *)
(*     match \prod_(i < k) (dims i)%:num =P (h * w)%nat with *)
(*     | ReflectT E => Some (vec_mx (castmx (prod_ord0 _, E) (tensor_val t)^T)) *)
(*     | ReflectF _ => None *)
(*     end *)
(*   end. *)

(* (*A' is A, but might be transposed, depending on trans*) *)
(* Definition as_matrix_t (x : realTensor) (trans : bool) (h w : nat) : option 'M[r]_(h, w) := *)
(*   if trans then omap (fun M => M^T) (as_matrix x w h) else as_matrix x h w. *)

(* (*matrix-to-tensor: a rank 2 tensor of shape [h; w]*) *)
(* Definition tensor_of_matrix2 (h w : {posnum nat}) (M : 'M[r]_(h%:num, w%:num)) : realTensor := *)
(*   existT _ (tensorType _ real (existT _ 2%nat [ffun i => tnth [tuple h; w] i])) *)
(*     (Tensor (castmx (prod_ord2 h w, esym (prod_ord0 _)) (mxvec M)^T)). *)

(* (*as convert_dims: scalars are 1x1, vectors 1xn, matrices hxw*) *)
(* Definition matrix_dims (x : realTensor) : option ({posnum nat} * {posnum nat}) := *)
(*   match tag x with *)
(*   | tensorType _ dims => *)
(*     match projT1 dims as k return {posnum nat} ^ k -> _ with *)
(*     | 0%nat => fun _ => Some (1%:posnat, 1%:posnat) *)
(*     | 1%nat => fun d => Some (1%:posnat, d ord0) *)
(*     | 2%nat => fun d => Some (d ord0, d ord_max) *)
(*     | _ => fun _ => None *)
(*     end (projT2 dims) *)
(*   end. *)

(* (*helper for broadcast_2d_real, as broadcast_2d_vector*) *)
(* Definition broadcast_2d_vector_real (h w hC wC : nat) (C : 'M[r]_(hC, wC)) *)
(*   : error_option 'M[r]_(h, w) := *)
(*   match hC =P 1%nat, wC =P w with *)
(*   | ReflectT E1, ReflectT E2 => Success (\matrix_(i, j) (castmx (E1, E2) C) ord0 j) (*C is a row vector*) *)
(*   | ReflectT _, ReflectF _ => Error "Broadcast: Dimension which is not one must match at least one given dimension" *)
(*   | ReflectF _, _ => *)
(*     match hC =P h, wC =P 1%nat with *)
(*     | ReflectT E1, ReflectT E2 => Success (\matrix_(i, j) (castmx (E1, E2) C) i ord0) (*C is a column vector*) *)
(*     | ReflectF _, ReflectT _ => Error "Broadcast: Dimension which is not one must match at least one given dimension" *)
(*     | _, ReflectF _ => Error "Broadcast: Vector matrices must have at least one dimension which is one" *)
(*     end *)
(*   end. *)

(* (*unidirectional broadcasting for two dimensions, as broadcast_2d*) *)
(* Definition broadcast_2d_real (h w : nat) (dims_C : seq nat) (hC wC : nat) (C : 'M[r]_(hC, wC)) *)
(*   : error_option 'M[r]_(h, w) := *)
(*   match dims_C with *)
(*   | [::] => (*C is a scalar*) *)
(*     match hC =P 1%nat, wC =P 1%nat with *)
(*     | ReflectT E1, ReflectT E2 => Success (const_mx ((castmx (E1, E2) C) ord0 ord0)) *)
(*     | _, _ => Error "Broadcast: Scalar matrices must have exactly one element" *)
(*     end *)
(*   | [:: _] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: 1%nat; _] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: _; 1%nat] => broadcast_2d_vector_real h w hC wC C (*C is a vector*) *)
(*   | [:: _; _] => (*C is a matrix*) *)
(*     match hC =P h, wC =P w with *)
(*     | ReflectT E1, ReflectT E2 => Success (castmx (E1, E2) C) *)
(*     | _, _ => Error "Broadcast: Matrices must have matching shape" *)
(*     end *)
(*   | _ => Error "Broadcast: Can only broadcast scalars, vectors and matrices" *)
(*   end. *)

(* (* *)
(* Gemm: alpha *: A' *m B' + beta *: C, with C broadcast to the shape of A' *m B'. *)
(* broadcast_C receives that shape. *)
(* *) *)
(* Definition gemm_real (A B : realTensor) (broadcast_C : forall h w : nat, error_option 'M[r]_(h, w)) *)
(*   (a : list AttributeProto) : error_option realTensor := *)
(*   let '(alpha, beta, transA, transB) := get_gemm_attributes a in *)
(*   let tA := if Z_of_int64 transA is Z0 then false else true in *)
(*   let tB := if Z_of_int64 transB is Z0 then false else true in *)
(*   match matrix_dims A, matrix_dims B with *)
(*   | Some (hA, wA), Some (hB, wB) => *)
(*     let '(hA', wA') := if tA then (wA, hA) else (hA, wA) in *)
(*     let '(hB', wB') := if tB then (wB, hB) else (hB, wB) in *)
(*     match as_matrix_t A tA hA'%:num wA'%:num, as_matrix_t B tB hB'%:num wB'%:num with *)
(*     | Some A', Some B' => *)
(*       match wA'%:num =P hB'%:num with *)
(*       | ReflectT E => *)
(*         match broadcast_C hA'%:num wB'%:num with *)
(*         | Success C_b => *)
(*           Success (tensor_of_matrix2 hA' wB' *)
(*             (R_of_float32 alpha *: A' *m castmx (esym E, erefl) B' + R_of_float32 beta *: C_b)) *)
(*         | Error e => Error e *)
(*         end *)
(*       | ReflectF _ => Error "Cannot compute dot product: row and column have not the same length (problably wrong dimension)" *)
(*       end *)
(*     | _, _ => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)" *)
(*     end *)
(*   | _, _ => Error "dims list cannot be longer than two when converting into a matrix" *)
(*   end. *)

(* (*Computes Gemm for three inputs, as gemm*) *)
(* Definition real_gemm (A B C : realTensor) (a : list AttributeProto) : error_option realTensor := *)
(*   match matrix_dims C with *)
(*   | Some (hC, wC) => *)
(*     match as_matrix C hC%:num wC%:num with *)
(*     | Some C' => gemm_real A B (fun h w => broadcast_2d_real h w [:: hC%:num; wC%:num] _ _ C') a *)
(*     | None => Error "Error in converting a Tensor into a Matrix (maybe empty data list, or non-fitting dim list?)" *)
(*     end *)
(*   | None => Error "dims list cannot be longer than two when converting into a matrix" *)
(*   end. *)

(* (*Computes Gemm for two inputs, as gemm_two_inputs: C is the 1x1 zero matrix*) *)
(* Definition real_gemm_two_inputs (A B : realTensor) (a : list AttributeProto) : error_option realTensor := *)
(*   gemm_real A B (fun h w => broadcast_2d_real h w [::] _ _ (0 : 'M[r]_(1, 1))) a. *)

(* (*Computes ReLU, as relu*) *)
(* Definition relu_tensor (d : TensorType RealElementType) *)
(*   : TensorSemantics (@realElementTypeInterp r) d -> TensorSemantics (@realElementTypeInterp r) d := *)
(*   match d as d return TensorSemantics _ d -> TensorSemantics _ d with *)
(*   | tensorType _ dims => fun t => Tensor (map_mx (fun x => Num.max x 0) (tensor_val t)) *)
(*   end. *)

(* Definition real_relu (X : realTensor) : error_option realTensor := *)
(*   Success (existT _ (tag X) (relu_tensor (tag X) (tagged X))). *)

(* (*initializers: the data of a TensorProto as reals, read as matrix_float32_of_tensor does*) *)
(* Definition real_data_of_tensor (t : TensorProto) : error_option (seq r) := *)
(*   match t with *)
(*   | TensorProto_constructor _ (Some data_type) _ float32_data int32_data _ int64_data _ _ raw_data _ _ _ _ _ => *)
(*     match Z_of_int32 data_type with *)
(*     | 1%Z => (*float32*) *)
(*       match float32_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match float32_of_bytes bytes with *)
(*           | Success floats => Success (map R_of_float32 floats) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type float32 must either have non-empty float_data or non-empty raw_data" *)
(*         end *)
(*       | floats => Success (map R_of_float32 floats) *)
(*       end *)
(*     | 6%Z => (*int32*) *)
(*       match int32_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match int32_of_bytes bytes with *)
(*           | Success ints => Success (map (fun i => IZR (Z_of_int32 i)) ints) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type int32 must either have non-empty int32_data or non-empty raw_data" *)
(*         end *)
(*       | ints => Success (map (fun i => IZR (Z_of_int32 i)) ints) *)
(*       end *)
(*     | 7%Z => (*int64*) *)
(*       match int64_data with *)
(*       | [::] => match raw_data with *)
(*         | Some bytes => match int64_of_bytes bytes with *)
(*           | Success ints => Success (map (fun i => IZR (Z_of_int64 i)) ints) *)
(*           | Error e => Error e *)
(*           end *)
(*         | None => Error "TensorProto with type int64 must either have non-empty int64_data or non-empty raw_data" *)
(*         end *)
(*       | ints => Success (map (fun i => IZR (Z_of_int64 i)) ints) *)
(*       end *)
(*     | _ => Error "Tensor Datatype must either be float32, int32 or int64" *)
(*     end *)
(*   | _ => Error "Tensor must have a given Datatype" *)
(*   end. *)

(* Definition real_of_tensorproto (t : TensorProto) : error_option realTensor := *)
(*   match t, real_data_of_tensor t with *)
(*   | TensorProto_constructor dims _ _ _ _ _ _ _ _ _ _ _ _ _ _, Success data => *)
(*     let ds := map int64_to_dim dims in *)
(*     let pdims : seq {posnum nat} := pmap insub ds in *)
(*     if size pdims == size ds then *)
(*       let fdims : {posnum nat} ^ (size pdims) := [ffun i => tnth (in_tuple pdims) i] in *)
(*       match size data =P \prod_(i < size pdims) (fdims i)%:num with *)
(*       | ReflectT E => Success (existT _ (tensorType _ real (existT _ _ fdims)) (build_tensor fdims data E)) *)
(*       | ReflectF _ => Error "TensorProto data does not match its dims" *)
(*       end *)
(*     else Error "dim cannot be zero or negative" *)
(*   | _, Error e => Error e *)
(*   end. *)

(* (* *)
(* Recursive implementation of the real valued onnx_evaluator, case by case as *)
(* onnx_evaluator_recursive: *)
(*   - Node:    Check op_type, evaluate all input vertices and compute if possible *)
(*   - Tensor:  Return itself *)
(*   - Input:   Search in user inputs for tensor with same name, if exactly one found: return it *)
(*   - Output:  Search in vertices for vertex with same name, if exactly one found: evaluate it *)
(* *) *)
(* Fixpoint real_onnx_evaluator_recursive (depth : nat) (user_inputs : seq (string * realTensor)) *)
(*   (vertices : list vertex) (evaluate : vertex) : error_option realTensor := *)
(*   match depth with *)
(*   | O => Error "ONNX Evaluator: Run out of vertices. Maybe a circular dependency, a missing vertex, or the list of nodes is not sorted topologically" *)
(*   | S n => (*check the type of the vertex to be evaluated*) *)
(*     match evaluate with *)
(*     (*Node: check op_type and compute it if possible*) *)
(*     | node (NodeProto_constructor node_inputs node_outputs _ op_type _ _ attributes _ _ _) => match op_type with *)
(*       | Some s => *)
(*         if String.eqb s """Gemm""" then *)
(*           match node_inputs with (*check input amount*) *)
(*           | [:: node_input_A; node_input_B; node_input_C] => (*three inputs*) *)
(*             match find_vertex vertices node_input_A, find_vertex vertices node_input_B, find_vertex vertices node_input_C with *)
(*             | [:: vertex_A], [:: vertex_B], [:: vertex_C] => (*evaluate each vertex and compute gemm*) *)
(*               match *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_A, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_B, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_C *)
(*               with *)
(*               | Success A, Success B, Success C => real_gemm A B C attributes *)
(*               | Error e, _, _ => Error e *)
(*               | _, Error e, _ => Error e *)
(*               | _, _, Error e => Error e *)
(*               end *)
(*             | _, _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ *)
(*                         node_input_A ++ " or " ++ node_input_B ++ " or " ++ node_input_C)%string *)
(*             end *)
(*           | [:: node_input_A; node_input_B] => (*two inputs*) *)
(*             match find_vertex vertices node_input_A, find_vertex vertices node_input_B with *)
(*             | [:: vertex_A], [:: vertex_B] => (*evaluate each vertex and compute gemm*) *)
(*               match *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_A, *)
(*               real_onnx_evaluator_recursive n user_inputs vertices vertex_B *)
(*               with *)
(*               | Success A, Success B => real_gemm_two_inputs A B attributes *)
(*               | Error e, _ => Error e *)
(*               | _, Error e => Error e *)
(*               end *)
(*             | _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ *)
(*                         node_input_A ++ " or " ++ node_input_B)%string *)
(*             end *)
(*           | _ => Error "Gemm must have 2-3 inputs" *)
(*           end *)
(*         else *)
(*         if String.eqb s """Relu""" then *)
(*           match node_inputs with (*check input amount*) *)
(*           | [:: node_input_name] => *)
(*             match find_vertex vertices node_input_name with *)
(*             | [:: vertex] => *)
(*               match real_onnx_evaluator_recursive n user_inputs vertices vertex with *)
(*               | Success rec => real_relu rec *)
(*               | Error e => Error e *)
(*               end *)
(*             | _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ node_input_name)%string *)
(*             end *)
(*           | _ => Error "Relu must have exactly one input" *)
(*           end *)
(*         else Error ("ONNX Evaluator: op_type of NodeProto must be a valid, implemented operation, not " ++ s)%string *)
(*       | None => Error "ONNX Evaluator: op_type of NodeProto must be non-empty" *)
(*       end *)

(*     (*Tensor: just return itself*) *)
(*     | tensor t => real_of_tensorproto t *)

(*     (*Input: search in user_inputs for tensor with same name, if exactly one found: return it*) *)
(*     | input (ValueInfoProto_constructor name_option _ _ _) => *)
(*       match name_option with *)
(*       | Some name => match filter (fun x => String.eqb name x.1) user_inputs with *)
(*         | [:: user_input] => Success user_input.2 *)
(*         | _ => Error ("ONNX Evaluator: not exactly one user input given for input vertex: " ++ name)%string *)
(*         end *)
(*       | None => Error "ONNX Evaluator: Input Vertex must define name" *)
(*       end *)

(*     (*Output: search in vertices for vertex with same name, if exactly one found: evaluate it*) *)
(*     | output (ValueInfoProto_constructor name_option _ _ _) => *)
(*       match name_option with *)
(*       | Some name => match filter (vertex_has_name name) vertices with *)
(*         | [:: v] => real_onnx_evaluator_recursive n user_inputs vertices v *)
(*         | _ => Error ("ONNX Evaluator: not exaclty one vertex (node, initializer or input) found: " ++ name)%string *)
(*         end *)
(*       | None => Error "ONNX Evaluator: Output Vertex must define name" *)
(*       end *)

(*     end *)
(*   end. *)

(* (*the computational graph, as built in onnx_evaluator*) *)
(* Definition graph_vertices (graph : GraphProto) : list vertex := *)
(*   match graph with *)
(*   | GraphProto_constructor nodes _ initializers _ _ inputs _ _ _ _ => *)
(*     map node (rev nodes) ++ map input inputs ++ map tensor initializers *)
(*   end. *)

(* (*Calls the recursive implementation of the real onnx_evaluator on a model's graph*) *)
(* Definition real_onnx_evaluator (model : ModelProto) (user_inputs : seq (string * realTensor)) *)
(*   : error_option (list realTensor) := *)
(*   match graph_of model with *)
(*   | Some graph => *)
(*     let vertices := graph_vertices graph in *)
(*     let evaluate := real_onnx_evaluator_recursive (size vertices) user_inputs vertices in *)
(*     let output_vertices := map output (graph_outputs model) in *)
(*     list_error_option_to_error_option_list (map evaluate output_vertices) [::] *)
(*   | None => Error "ONNX Evaluator: Model must define a graph" *)
(*   end. *)

(* (*the InputSemantics, named after the model's graph inputs*) *)
(* Definition real_user_inputs (graph_ins : seq ValueInfoProto) (y : NetworkType RealElementType) *)
(*   : InputSemantics (@realElementTypeInterp r) y -> seq (string * realTensor) := *)
(*   match y as y return InputSemantics (@realElementTypeInterp r) y -> seq (string * realTensor) with *)
(*   | networkType ins _ => fun inp => *)
(*     [seq (value_info_name (nth emptyValueInfoProto graph_ins i), existT _ _ (inp i)) *)
(*     | i : 'I_(size ins) <- fintype.enum 'I_(size ins)] *)
(*   end. *)

(* (*the evaluator's result at type d; errors and shape mismatches give 0*) *)
(* Definition real_result (d : TensorType RealElementType) (t : error_option realTensor) *)
(*   : TensorSemantics (@realElementTypeInterp r) d := *)
(*   match d as d return TensorSemantics (@realElementTypeInterp r) d with *)
(*   | tensorType _ dims => *)
(*     match t with *)
(*     | Success (existT (tensorType _ dims') t) => *)
(*       match dims' =P dims with *)
(*       | ReflectT E => rew [fun ds => 'nT[r]_(projT2 ds)] E in t *)
(*       | ReflectF _ => const_t 0 *)
(*       end *)
(*     | Error _ => const_t 0 *)
(*     end *)
(*   end. *)

(* End RealEvaluator. *)

(* From Stdlib Require Import Rdefinitions. *)
(* Definition R_of_float32 (f : float32) : R := Binary.B2R 24 128 f. *)

(* (* *)
(* Executes the network over R: the semantic inputs are named after the *)
(* model's graph inputs, and the requested node output is evaluated by *)
(* real_onnx_evaluator_recursive as onnx_evaluator evaluates an output vertex. *)
(* *) *)
(* Definition realSemantics : (@RealNetworkSemantics syntax_inst R) := *)
(*   fun y1 y2 d1 d2 u m _ inp out _ => *)
(*   match m as m return NodeOutput syntax_inst m u d1 -> _ with *)
(*   | exist model _ => fun out => *)
(*     let user_inputs := real_user_inputs R (graph_inputs model) y2 inp in *)
(*     match graph_of model with *)
(*     | Some graph => *)
(*       let vertices := graph_vertices graph in *)
(*       real_result R d2 (real_onnx_evaluator_recursive R R_of_float32 IZR (size vertices) user_inputs vertices (output (val out))) *)
(*     | None => real_result R d2 (Error "ONNX Evaluator: Model must define a graph") *)
(*     end *)
(*   end out. *)
