Require Export IndPrinciples.

Definition relation (X : Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function. intros.
  inversion H. inversion H0. reflexivity.
  Show Proof.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
  apply Hc with (x := 0). auto. auto.
  inversion Nonsense.
Qed.

Theorem total_relation_is_not_partial_function :
  ~(partial_function total_relation).
Proof.
  unfold not, partial_function. intros Hc.
  Print total_relation.
  pose proof Hc 0 1 2.
  assert (t1 : total_relation 0 1). apply tt_1. auto.
  assert (t2 : total_relation 0 2). apply tt_1. auto.
  pose proof H t1 t2. inversion H0.
Qed.

Print empty_relation.

Theorem empty_relation_is_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function. intros x y1 y2 H1 H2.
  inversion H1.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive : reflexive le.
Proof.
  unfold reflexive. intros. auto.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans : transitive le.
Proof.
  unfold transitive. intros a b c H1 H2.
  omega.
Qed.

Theorem lt_trans: transitive lt.
Proof.
  unfold transitive. intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := S n) (b := S m) (c := o).
  auto. auto.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  auto. auto.
Qed.

Theorem lt_trans'' : transitive lt.
Proof.
  unfold transitive, lt. intros n m o Hnm Hmo.
  induction o as [| o']. inversion Hmo.
  apply le_S. inversion Hmo. rewrite <- H0.
  apply Hnm. apply IHo'. assumption.
Qed.


