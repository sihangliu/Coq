Require Export Basics.

Theorem plus_n_O : forall (n : nat), n + 0 = n.
Proof.
  intros n. induction n as [ | n' IHn'].
  + auto.
  + simpl. rewrite IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n : nat, minus n n = 0.
Proof.
  intros n. induction n.
  + auto.
  + simpl. rewrite IHn. reflexivity.
Qed.

