From Coq Require Import Nat Reals List Arith Lia Lra.

Open Scope nat_scope.


Lemma S_pred_pos n: O < n -> n = S (pred n).
Proof. intros. unfold pred. destruct n.
- inversion H.
- reflexivity.
Qed.

Theorem le_lt_n_Sm n m : n <= m -> n < S m.
Proof. apply Nat.lt_succ_r. Qed.

Lemma le_n_0_eq n : n <= 0 -> 0 = n.
Proof. intros. destruct n.
- reflexivity.
- inversion H.
Qed.