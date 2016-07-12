Require Export Tactics.

Check 3 = 3.
Check forall m n : nat, m + n = n + m.
Check forall n : nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_4 : 2 + 2 = 4.
Proof. auto. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B : Type} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Check @injective.

Lemma succ_inj : injective S.
Proof.
  unfold injective. intros x y H. inversion H. reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

