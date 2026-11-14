From HB Require Import structures.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.
From mathcomp Require Import tuple.
(* see https://github.com/rocq-prover/stdlib/blob/master/theories/Vectors/Vector.v *)

From Flocq Require Import Bits.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model bytes_converter.
From ONNXFormalization.ONNXEvaluator Require Export matrices.

HB.mixin Record isValidType T := {
    zero : T;
    add : T -> T -> T;
    mul : T -> T -> T;
    ge0 : T -> bool;
    of_bytes : bytes -> error_option (list T);
    name : string;
    typed_field : TensorProto -> error_option (list T);
    to_tensor : list int64 -> list T -> TensorProto;
    of_float32 : float32 -> option T;
  }.

#[short(type="validType")]
  HB.structure Definition ValidType := {T of isValidType T}.

Definition ge0_int32 (i: int32) : bool :=
  match Z_of_int32 i with
  | Zneg _ => false (*i is less than zero*)
  | Z0 => true(* i is zero*)
  | _ => true (*i is more than zero*)
  end.

Definition get_int32 (X : TensorProto) : error_option (list int32) :=
  match X with
  | TensorProto_constructor _ _ _ _ int32 _ _ _ _ raw_data _ _ _ _ _ =>
      match int32 with
      | nil =>
          match raw_data with
          | Some b => int32_of_bytes b
          | None => Error ("TensorProto with type int32
                            must have non-empty int32_data or raw_data")
          end
      | xs => Success xs
      end
  end.

Definition int32_to_tensor (dims : list int64) (int_data : list int32)
  : TensorProto :=
  TensorProto_constructor dims (Some (int32_of_Z 6%Z)) None nil int_data nil nil
    None None None nil None nil nil nil.

Definition int32_of_float32 (x : float32) : option int32 :=
  match Z_of_float32 x with
  | Some y => Some (int32_of_Z y)
  | None => None
  end.

HB.instance Definition _ := isValidType.Build int32
  (int32_of_Z 0%Z)
  (fun x y => int32_of_Z ((Z_of_int32 x) + (Z_of_int32 y))%Z)
  (fun x y => int32_of_Z ((Z_of_int32 x) * (Z_of_int32 y))%Z)
  ge0_int32
  int32_of_bytes
  "int32"
  get_int32
  int32_to_tensor
  int32_of_float32.

Definition ge0_int64 (i: int64) : bool :=
  match Z_of_int64 i with
  | Zneg _ => false (*i is less than zero*)
  | Z0 => true (* i is zero*)
  | _ => true (*i is more than zero*)
  end.

Definition get_int64 (X : TensorProto) : error_option (list int64) :=
  match X with
  | TensorProto_constructor _ _ _ _ _ _ int64 _ _ raw_data _ _ _ _ _ =>
      match int64 with
      | nil =>
          match raw_data with
          | Some b => int64_of_bytes b
          | None => Error ("TensorProto with type int64
                            must have non-empty int64_data or raw_data")
          end
      | xs => Success xs
      end
  end.

Definition int64_to_tensor (dims : list int64) (int_data : list int64)
  : TensorProto :=
  TensorProto_constructor dims (Some (int32_of_Z 7%Z)) None nil nil nil int_data
                          None None None nil None nil nil nil.

Definition int64_of_float32 (x : float32) : option int64 :=
  match Z_of_float32 x with
  | Some y => Some (int64_of_Z y)
  | None => None
  end.

HB.instance Definition _ := isValidType.Build int64
  (int64_of_Z 0%Z)
  (fun x y => int64_of_Z ((Z_of_int64 x) + (Z_of_int64 y))%Z)
  (fun x y => int64_of_Z ((Z_of_int64 x) * (Z_of_int64 y))%Z)
  ge0_int64
  int64_of_bytes
  "int64"
  get_int64
  int64_to_tensor
  int64_of_float32.

Definition get_float32 (X : TensorProto) : error_option (list float32) :=
  match X with
  | TensorProto_constructor _ _ _ float32 _ _ _ _ _ raw_data _ _ _ _ _ =>
      match float32 with
      | nil =>
          match raw_data with
          | Some b => float32_of_bytes b
          | None => Error ("TensorProto with type float32
                            must have non-empty float32_data or raw_data")
          end
      | xs => Success xs
      end
  end.

Definition float32_to_tensor (dims : list int64) (float_data : list float32)
  : TensorProto :=
  TensorProto_constructor dims (Some (int32_of_Z 1%Z)) None float_data nil nil nil
                          None None None nil None nil nil nil.

Definition ge0_f32 (f: float32) : bool :=
  match f with
  | Binary.B754_zero _ => true (*f is zero*)
  | Binary.B754_infinity sign =>      (*f is infinite*)
    match sign with
    | true => (*f is -inf*)
        false
    | false => true (*f is +inf*)
    end
  | Binary.B754_nan _ _ _ => true     (*f is Nan*)
  | Binary.B754_finite sign _ _ _ =>  (*f is finite*)
    match sign with
    | true => (*f is less than zero*)
        false
    | false => true (*f is more or equal zero, result is f*)
    end
  end.

HB.instance Definition _ := isValidType.Build float32
  (Binary.binary_normalize 24 128 eq_refl eq_refl BinarySingleNaN.mode_NE 0 0 false)
  (b32_plus BinarySingleNaN.mode_NE)
  (b32_mult BinarySingleNaN.mode_NE)
  ge0_f32
  float32_of_bytes
  "float32"
  get_float32
  float32_to_tensor
  Some.

Definition pack {R : validType} (r : error_option (list R))
  : error_option {R : validType & list R} :=
  match r with
  | Success xs => Success (existT (fun R : validType => list R) R xs)
  | Error e => Error e
  end.

(* Definition decode {R : validType} (data : list R) (raw : option bytes) *)
(*   : error_option (list R) := *)
(*   match data with *)
(*   | nil => *)
(*       match raw with *)
(*       | Some bytes => of_bytes bytes *)
(*       | None => Error ("TensorProto with type " ++ @name R ++ " must either have non-empty " ++ @name R ++ "_data or non-empty raw_data") *)
(*       end *)
(*   | xs => Success xs *)
(*   end. *)
Record tensor (R : Type) := Tensor { tdims : list int64; tdata : list R }.
Arguments Tensor {R}. Arguments tdims {R}. Arguments tdata {R}.

Definition ebind {A B} (m : error_option A) (f : A -> error_option B) : error_option B :=
  match m with Success a => f a | Error e => Error e end.
Notation "x <- m ;; k" := (ebind m (fun x => k)) (at level 61, m at next level, right associativity).

Definition eapp {A B} (f : A -> B) (m : error_option A) : error_option B :=
match m with
| Success x => Success (f x)
| Error x => Error x
end.

Definition dispatch (dt : option int32) : error_option validType :=
  match option_map Z_of_int32 dt with
  | Some 1%Z => Success (ValidType.clone float32 _)
  | Some 6%Z => Success (ValidType.clone int32 _)
  | Some 7%Z => Success (ValidType.clone int64 _)
  | Some _ => Error "Tensor Datatype must either be float32, int32 or int64"
  | None   => Error "Tensor must have a given Datatype"
  end.

Definition same_dtype (a b : option int32) : bool :=
  match a, b with
  | Some x, Some y => Z.eqb (Z_of_int32 x) (Z_of_int32 y)
  | _, _ => false
  end.

Fixpoint mapM {A B} (f : A -> error_option B) (s : list A) : error_option (list B) :=
  match s with
  | nil => Success nil
  | x :: s' => y <- f x ;; ys <- mapM f s' ;; Success (y :: ys)
  end.

Fixpoint mapM_tuple {A B} (f : A -> error_option B) {k} : k.-tuple A -> error_option (k.-tuple B) :=
  match k with
  | O => fun _ => Success (nil_tuple B)
  | S k' => fun t =>
              y  <- f (thead t) ;;
              ys <- mapM_tuple f (behead_tuple t) ;;
              Success (cons_tuple y ys)
  end.

Definition dims_of (X : TensorProto) : list int64 :=
  let: TensorProto_constructor d _ _ _ _ _ _ _ _ _ _ _ _ _ _ := X in d.
Definition dtype_of (X : TensorProto) : option int32 :=
  let: TensorProto_constructor _ t _ _ _ _ _ _ _ _ _ _ _ _ _ := X in t.

Definition apply_op {k}
  (op : forall R : validType, (S k).-tuple (tensor R) -> error_option (tensor R))
  (Xs : (S k).-tuple TensorProto) : error_option TensorProto :=
  let X0 := thead Xs in
  if negb (forallb (fun X => same_dtype (dtype_of X) (dtype_of X0)) Xs)
  then Error "All inputs must have the same data type"
  else
    R    <- dispatch (dtype_of X0) ;;
    args <- mapM_tuple (fun X => d <- typed_field X ;; Success (Tensor (dims_of X) d)) Xs ;;
    out  <- op R args ;;
    Success (to_tensor (tdims out) (tdata out)).
