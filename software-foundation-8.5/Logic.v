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

Lemma in_app_iff : forall A l l' ( a : A),
    In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  split. generalize l l' a. induction l0.
  - simpl. intros. right. assumption.
  - simpl. intros. destruct H as [H1 | H1]. left. left. assumption.
    apply or_assoc. right. apply IHl0. assumption.
  -  generalize l l' a. induction l0.
     + simpl. intros. destruct H. inversion H. assumption.
     + simpl. intros. destruct H as [[H1 | H1] | H1]. left. assumption.
       right. apply IHl0. left. assumption. right. apply IHl0. right. assumption.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' =>
    P x /\ All P l'
  end.

Lemma All_In :
  forall (T : Type) (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  split.
  - generalize l. induction l0.
    + simpl. intros. apply I.
    + simpl. intros. split.
      apply H. left. reflexivity. apply IHl0. intros. apply H. right. assumption.
  - generalize l. induction l0.
    + simpl. intros. inversion H0.
    + simpl. intros. destruct H0 as [H1 | H1]. destruct H as [H2 H3]. rewrite H1. assumption.
      destruct H as [H2 H3]. apply IHl0. assumption. assumption.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if evenb n then Peven n else Podd n.

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros podd peven n. unfold oddb. unfold combine_odd_even.
  intros H1 H2. destruct evenb.
  apply H2. reflexivity.
  apply H1. reflexivity.
Qed.

Definition combine_odd_even' (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => Peven n \/ Podd n.


Theorem combine_odd_even_intro' : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even' Podd Peven n.
Proof.
  intros podd peven n. unfold oddb. unfold combine_odd_even'.
  destruct evenb.
  - intros H1 H2. left. apply H2. reflexivity.
  - intros H1 H2. right. apply H1. reflexivity.
Qed.

Check plus_comm.

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite Hm. reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
    (forall (x : X), f x = g x) -> f = g.

Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros x0.
  apply plus_comm.
Qed.

Print Assumptions plus_comm_ext.

Fixpoint rev_append {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | h :: t => rev_append t (h :: l2)
  end.

Compute (rev_append [1;2;3;4] []).  
Definition tr_rev {X : Type} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall (X : Type), @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality. intros x.
  induction x.
  - auto.
  - simpl. rewrite <- IHx. unfold tr_rev.
Abort.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k.
  - auto.
  - simpl. assumption.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
           else S (double k).
Proof.
  intros n. induction n.
  - simpl. exists 0. auto.
  - rewrite evenb_S.
    destruct evenb. simpl. destruct IHn. exists x. auto.
    simpl. destruct IHn. rewrite H. exists (S x). simpl. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  intros H. destruct (evenb_double_conv n) as [k Hk].
  rewrite Hk. rewrite H. exists k. reflexivity.
  intros [k Hk]. rewrite Hk.
 apply evenb_double. 
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
    Basics.beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  split. intros H. apply beq_nat_true. auto.
  intros H. assert (forall (m n : nat), m = n -> Basics.beq_nat m n = true).
  {
    induction m.
    - intros n H1. rewrite <- H1. simpl. reflexivity.
    - intros n H1. induction n.
      + inversion H1.
      + simpl. apply IHm. inversion H1. reflexivity.
  }
  apply H0. assumption.
Qed.

