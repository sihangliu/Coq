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


Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  auto. auto.
Qed.

Theorem le_S_n : forall n m, (S n <= S m) -> (n <= m).
Proof.
  intros n m H. apply Sn_le_Sm__n_le_m. auto.
Qed.

Theorem le_Sn_n : forall n, ~ (S n <= n).
Proof.
  unfold not. intros n H. induction n. inversion H. apply IHn.
  omega.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b, R a b -> R b a.

Theorem le_not_symmetric : ~ (symmetric le).
Proof.
  unfold not, symmetric. intros.
  assert (t : 0 <= 1) by omega.
  pose proof H 0 1 t. inversion H0.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b, R a b -> R b a -> a = b.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric. intros a b H1 H2. omega.
Qed.

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preoder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order : order le.
Proof.
  unfold order. split. unfold reflexive. auto. split. unfold antisymmetric.
  intros. omega. unfold transitive. intros. omega.
Qed.

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
| rt_step x y : R x y -> clos_refl_trans R x y
| rt_refl x : clos_refl_trans R x x
| rt_trans x y z : clos_refl_trans R x y -> clos_refl_trans R y z ->
                   clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
    (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split. intros H.
  induction H. apply rt_refl.
  apply rt_trans with m. assumption. apply rt_step.
  apply nn.
  intros H. induction H. inversion H. apply le_S. apply le_n.
  auto. apply le_trans with y. auto. auto.
Qed.

Inductive clos_refl_trans_1n {A : Type} (R : relation A) (x : A) : A -> Prop :=
| rt1n_refl : clos_refl_trans_1n R x x
| rt1n_trans (y z : A) : R x y ->  clos_refl_trans_1n R y z ->
                         clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
    R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H. apply rt1n_trans with y.
  auto. apply rt1n_refl.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros. induction H. auto.
  apply  rt1n_trans with y. auto.
  pose proof IHclos_refl_trans_1n H0. assumption.
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split. intros H. 
  induction H. apply rt1n_trans with y. auto. constructor. constructor.
  pose proof (rsc_trans _ _ _ _ _ IHclos_refl_trans1 IHclos_refl_trans2). auto.

  intros H. induction H. apply rt_refl. apply rt_trans with y.
  apply rt_step. assumption. assumption.
Qed.

