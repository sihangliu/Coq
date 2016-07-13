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

Lemma and_intro :
  forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros. split.
  - assumption.
  - assumption.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  induction n.
  {
    induction m. simpl. intros.
    split. reflexivity. reflexivity.
    simpl. intros. split. reflexivity.
    inversion H.
  }
  {
    induction m. simpl. intros. inversion H.
    simpl. intros. inversion H.
  }
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [HA HB].
  rewrite HA. rewrite HB. auto.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H. apply and_exercise in H.
  destruct H as [Ha Hb].
  rewrite Ha; rewrite Hb; auto.
Qed.

Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q [HP HQ]. apply HP.
Qed.

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q [HP HQ]. apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split. apply HQ. apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. assumption. assumption. assumption.
Qed.

Check and.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  rewrite Hn. auto.
  rewrite Hm. auto.
Qed.

Lemma or_intro :
  forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. assumption.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros n. induction n.
  left. reflexivity.
  right. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. destruct n.
  {
    destruct m.
    left. auto.
    left. auto.
  }
  {
    destruct m.
    right. auto.
    right. simpl in H. inversion H.
  }
Qed.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  right. assumption.
  left. assumption.
Qed.

Module MyNot.
  Definition not (P : Prop) := P -> False.
  Notation "~ x" := (not x) : type_scope.
  Check not.
End MyNot.

Theorem ex_falso_quodlibet :
  forall (P : Prop), False -> P.
Proof.
  intros P H. destruct H.
Qed.

Fact not_implies_our_not : forall (P:Prop),
    ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H Q HP. unfold not in H.
  apply H in HP. destruct HP.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof. unfold not. intros H. inversion H. Qed.

Theorem not_False : ~False.
Proof. unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HQ]. unfold not in HQ.
  apply HQ in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P HP. unfold not.
  intros H. apply H in HP.
  destruct HP.
Qed.

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2. unfold not in H2. unfold not.
  intros H3. apply H1 in H3. apply H2 in H3. inversion H3.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros [HP HQ].
  apply HQ. assumption.
Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H. unfold not in H.
  induction b. apply ex_falso_quodlibet.
  apply H. reflexivity.
  reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H. unfold not in H.
  induction b. exfalso. apply H. reflexivity.
  reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
  Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HP HQ].
  unfold iff. split. apply HQ. apply HP.
Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  unfold iff. unfold not. split.
  induction b.
  intros H. exfalso. apply H. reflexivity.
  intros H. reflexivity.
  induction b.
  intros H1 H2. discriminate H1.
  intros H1 H2. discriminate H2.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
  unfold iff. intros P. split.
  intros H. assumption.
  intros H. assumption.
Qed.

Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  unfold iff in HPQ. unfold iff in HQR.
  destruct HPQ. destruct HQR.
  unfold iff. split. intros.
  apply H in H3. apply H1 in H3. assumption.
  intros. apply H2 in H3. apply H0 in H3.
  assumption.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  unfold iff. intros.
  split. intros. destruct H as [HP | [HQ HR]].
  split. left. assumption. left. assumption.
  split. right. assumption. right. assumption.
  intros. destruct H as [[HP | HQ] [HP' | HR]].
  left. assumption. left. assumption.
  left. assumption. right. split. assumption. assumption.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  apply mult_eq_0.
  apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]].
    + left. left. assumption.
    + left. right. assumption.
    + right. assumption.
  - intros [[HP | HQ] | HR].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  destruct H. exists (2 + x). simpl. assumption.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros. destruct H0. apply H0.
  apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H. destruct H as [Hp | Hq].
    left. exists x. assumption.
    right. exists x. assumption.
  - intros. destruct H as [Hp | Hq].
    destruct Hp. exists x. left. assumption.
    destruct Hq. exists x. right. assumption.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x = x' \/ In x l'
  end.

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  simpl. right.  left. auto.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros n H. simpl in H.
  destruct H as [H1 | [H2 | H3]].
  exists 1. simpl. auto.
  exists 2. auto.
  inversion H3.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x. induction l.
  - simpl. intros. assumption.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl. assumption.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - generalize l, y. induction l0.
    + intros y0 H. inversion H.
    + simpl. intros y0 [H | H]. exists x. split. symmetry.
      assumption. left. reflexivity. apply IHl0 in H.
      destruct H. exists x0. split. destruct H as [H1  H2]. assumption.
      right. destruct H as [H1 H2]. assumption.
  - intros H. induction l.
    + destruct H. destruct H as [H1 H2]. inversion H2.
    + simpl. destruct H. simpl in H. destruct H as [H1 H2].
      destruct H2 as [H | H].  left. rewrite <- H. symmetry. assumption.
      right. apply IHl. exists x0. split. assumption. assumption.
Qed.

