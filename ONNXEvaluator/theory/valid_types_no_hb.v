From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import ZArith.

From Flocq Require Import Bits.

From ONNXFormalization.External Require Export error_option.
From ONNXFormalization.ONNXConverter Require Export model bytes_converter.
From ONNXFormalization.ONNXEvaluator Require Export matrices.

Structure ValidType := buildValidType {
    T : Type;
    zero : T;
    add : T -> T -> T;
    mul : T -> T -> T;
    ge0 : T -> bool;
    of_bytes : bytes -> error_option (list T);
    name : string;
    typed_field : TensorProto -> error_option (list T);
    to_tensor : list int64 -> list T -> TensorProto;
    of_float32 : float32 -> option T
  }.

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

Definition int32ValidType := buildValidType int32
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

Definition int64ValidType := buildValidType int64
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
  | Binary.B754_zero _ _ _ => true (*f is zero*)
  | Binary.B754_infinity _ _ sign =>      (*f is infinite*)
    match sign with
    | true => (*f is -inf*)
        false
    | false => true (*f is +inf*)
    end
  | Binary.B754_nan _ _ _ _ _ => true     (*f is Nan*)
  | Binary.B754_finite _ _ sign _ _ _ =>  (*f is finite*)
    match sign with
    | true => (*f is less than zero*)
        false
    | false => true (*f is more or equal zero, result is f*)
    end
  end.

Definition float32ValidType := buildValidType float32
  (Binary.binary_normalize 24 128 eq_refl eq_refl BinarySingleNaN.mode_NE 0 0 false)
  (b32_plus BinarySingleNaN.mode_NE)
  (b32_mult BinarySingleNaN.mode_NE)
  ge0_f32
  float32_of_bytes
  "float32"
  get_float32
  float32_to_tensor
  Some.

Record tensor (R : Type) := Tensor { tdims : list int64; tdata : list R }.
Arguments Tensor {R}. Arguments tdims {R}. Arguments tdata {R}.

Definition ebind {A B} (m : error_option A) (f : A -> error_option B) : error_option B :=
  match m with Success a => f a | Error e => Error e end.

Definition eapp {A B} (f : A -> B) (m : error_option A) : error_option B :=
match m with
| Success x => Success (f x)
| Error x => Error x
end.

Definition dispatch (dt : option int32) : error_option ValidType :=
  match option_map Z_of_int32 dt with
  | Some 1%Z => Success float32ValidType
  | Some 6%Z => Success int32ValidType
  | Some 7%Z => Success int64ValidType
  | Some _ => Error "Tensor Datatype must either be float32, int32 or int64"
  | None   => Error "Tensor must have a given Datatype"
  end.

Definition same_dtype (a b : option int32) : bool :=
  match a, b with
  | Some x, Some y => Z.eqb (Z_of_int32 x) (Z_of_int32 y)
  | _, _ => false
  end.

Definition all_same_dtype (l : list (option int32)) : bool :=
  match l with
  | [] => true
  | t :: ts => forallb (same_dtype t) ts
  end. 

Definition dims_of (X : TensorProto) : list int64 :=
  match X with
  | TensorProto_constructor d _ _ _ _ _ _ _ _ _ _ _ _ _ _ => d
  end.

Definition dtype_of (X : TensorProto) : option int32 :=
  match X with
  | TensorProto_constructor _ t _ _ _ _ _ _ _ _ _ _ _ _ _ => t
  end.

Fixpoint tensorOperadCall {R : ValidType} (n : nat) : Type :=
  match n with
  | 0%nat => error_option (tensor (T R))
  | S n => tensor (T R) -> tensorOperadCall (R:=R) n
  end.

Definition tensorOperad (n : nat) : Type :=
  forall (R : ValidType), tensorOperadCall (R:=R) n.

Fixpoint apply_op_helper (k : nat) (R : ValidType)
  (op : tensorOperadCall (R:=R) k)
  (Xs : list TensorProto)
  : error_option TensorProto :=
  (match k as k2 return (k = k2 -> error_option TensorProto) with
    | 0%nat => fun eq : k = 0%nat => 
      let result : error_option (tensor (T R)) := (eq_rect _ _ op _ eq) in
        match result with
        | Success t_out => Success (to_tensor R (tdims t_out) (tdata t_out))
        | Error msg => Error msg
        end
    | S p => fun eq : k = S p =>
      match Xs with
      | nil => Error "Not enough arguments for an operation"
      | X0 :: Xrest => 
          ebind 
          (typed_field R X0) 
          (fun data => 
            let reduced_operad := eq_rect _ _ op (S p) eq in
            apply_op_helper p R 
              (reduced_operad (Tensor (dims_of X0) data)) 
              Xrest) 
      end
    end) eq_refl.

Definition apply_op {k}
  (op : tensorOperad k)
  (Xs : list TensorProto) 
  : error_option TensorProto :=
  if negb (all_same_dtype (map (fun t => dtype_of t) Xs))
  then 
    Error "All inputs must have the same data type"
  else 
    match Xs with
    | nil => Error "An operation has at least one input"
    | X0 :: _ => 
      match dispatch (dtype_of X0) with
        | Success R => apply_op_helper k R (op R) Xs
        | Error msg => Error msg
      end
    end.