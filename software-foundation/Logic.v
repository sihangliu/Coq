Require Export MoreCoq.

Check (3 = 3).
Check (forall n, n = 2).

Lemma silly : 0 * 3 = 0.
Proof.
  reflexivity.
Qed.
Print silly.

Lemma silly_implication : (1 + 1) = 2 -> 0 × 3 = 0.
Proof.
  intros H. reflexivity. Show Proof.
Qed.

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> and P Q.

Notation "P /\ Q" := (and P Q) : type_scope.
Check conj.

Theorem and_example :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.

Theorem and_example' :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H. destruct H as [HP HQ].
  assumption.
Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q ->  Q.
Proof.
  intros P Q H. destruct H eqn: Ht. assumption.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H. destruct H eqn: Ht.
  split.
  assumption. assumption.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H. destruct H as [Hp [Hq Hr]].
  split. split. assumption. assumption. assumption.
Qed.

Definition iff (P Q : Prop) : Prop := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
Theorem iff_implies : forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  intros P Q H. destruct H as [HL HR]. assumption.
Qed.

Theorem iff_sym : forall (P Q : Prop), (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H. destruct H as [Hl Hr].
  apply conj. assumption. assumption.
Qed.

Theorem iff_refl : forall (P : Prop), P <-> P.
Proof.
  intros P. apply conj.
  Case "Left". intros H. assumption.
  Case "Right". intros H. assumption.
Qed.

Print iff_refl.
Theorem iff_trans : forall (P Q R : Prop),
                      (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  apply conj.
  Case "Left".
  {
    destruct H1 as [Hl Hr].
    destruct H2 as [Hl' Hr'].
    intros P'. apply Hl in P'. apply Hl' in P'. assumption.
  }
  Case "Right".
  {
    destruct H1 as [H1l H1r]. destruct H2 as [H2l H2r].
    intros R'. apply H2r in R'. apply H1r in R'. assumption.
  }
Qed.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.
Check or_introl.

Theorem or_commute : forall (P Q : Prop),
                       P \/ Q -> Q \/ P.
Proof.
  intros P Q H. destruct H as [Hp | Hq].
  apply or_intror. assumption.
  apply or_introl. assumption.
Qed.

Theorem or_commute' : forall (P Q : Prop),
                       P \/ Q -> Q \/ P.
Proof.
  intros P Q H. destruct H as [Hp | Hq].
  Case "Left". right. assumption.
  Case "Right". left. assumption.
Qed.

Theorem or_distributes_over_and_1 : forall (P Q R : Prop),
                                      P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  apply conj.
  Case "Left".
  {
    destruct H as [Hp | [Hq Hr]].
    apply or_introl. assumption.
    apply or_intror. assumption.
  }
  Case "Right".
  {
    destruct H as [Hp | [Hq Hr]].
    apply or_introl. assumption.
    apply or_intror. assumption.
  }
Qed.


Theorem or_distributes_over_and_r : forall (P Q R : Prop),
                                    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  destruct H as [[Hp | Hq] [Hp' | Hq']].
  apply or_introl. assumption.
  apply or_introl. assumption.
  apply or_introl. assumption.
  apply or_intror. apply conj. assumption. assumption.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  apply conj.
  Case "Left".
  {
    intros H. destruct H as [Hp | [Hq Hr]].
    apply conj. apply or_introl. assumption.
    apply or_introl. assumption.
    apply conj. apply or_intror. assumption.
    apply or_intror. assumption.
  }
  Case "Right".
  {
    intros H. destruct H as [[Hp | Hq] [Hp' | Hr]].
    apply or_introl. assumption.
    apply or_introl. assumption.
    apply or_introl. assumption.
    apply or_intror. apply conj. assumption. assumption.
  }
Qed.

Theorem andb_prop : forall (b c : bool),
                      andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
  {
    destruct c. apply conj. reflexivity. reflexivity.
    inversion H.
  }
  Case "b = false".
  {
    destruct c. apply conj. inversion H. reflexivity. inversion H.
  }
Qed.

Theorem andb_true_intro : forall (b c : bool),
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H. destruct H as [Hb Hc].
  rewrite Hb. rewrite Hc. reflexivity.
Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
  {
    destruct c. inversion H.
    apply or_intror. reflexivity.
  }
  Case "b = false".
  {
    apply or_introl. reflexivity.
  }
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "Left". apply or_introl. reflexivity.
  Case "Right".
  {
    destruct c.
    apply or_intror. reflexivity.
    inversion H.
  }
Qed.


Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "left".
  {
    destruct c. inversion H.
    inversion H.
  }
  Case "right".
  {
    apply conj. reflexivity.
    destruct c. inversion H. reflexivity.
  }
Qed.

Inductive False : Prop := .

Theorem false_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros H. inversion H.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros H. inversion H.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P H. inversion H.
Qed.

Inductive True : Prop :=
| trivial : True.

Definition not (P : Prop) : Prop := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not (2 = 2).

Theorem not_False : ~False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  destruct H as [Hp Hp'].
  unfold not in Hp'. apply Hp' in Hp. inversion Hp.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not. intros H1. apply H1 in H. inversion H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2. unfold not in H2. unfold not. intros P'.
  apply H1 in P'. apply H2 in P'. inversion P'.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros H. destruct H as [Hp Hp'].
  apply Hp' in Hp. inversion Hp.
Qed.

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  intros P. unfold not. intros H.
Abort.

Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) ->  P  \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem peirce_implies_classical: peirce -> classic.
Proof.
  unfold peirce. unfold classic.
  intros H1 P H2. unfold not in H2. apply H1 with (Q := False).
  intros H3. apply H2 in H3. inversion H3.
Qed.

Lemma disjunction_and_implication : forall P Q : Prop,
                        P \/ Q -> (~P -> Q).
Proof.
  intros P Q H1 H2. destruct H1 as [Hp | Hq]. unfold not in H2.
  apply H2 in Hp. inversion Hp. assumption.
Qed. 
(*
Theorem classical_implies_excluded : classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle.
  intros H. Admitted.
 *)

Theorem excluded_middle_irrefutable: forall (P : Prop), ~~(P \/  ~P).
Proof.
  unfold not. intros P H. apply H.
  apply or_intror. intros P'. apply H.
  apply or_introl. assumption.
Qed.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  unfold not. intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false". apply ex_falso_quodlibet. apply H. reflexivity.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  unfold not. intros n. induction n.
  Case "n = O".
  {
    intros m H. induction m.
    SCase "m = O". simpl. apply ex_falso_quodlibet. apply H. reflexivity.
    SCase "m = S m". simpl. reflexivity.
  }
  Case "n = S n".
  {
    intros m H. induction m.
    SCase "m = O". simpl. reflexivity.
    SCase "m = S m". simpl. apply IHn. intros Hnm.  apply H.
    apply f_equal. assumption.
  }
Qed.

Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n. induction n.
  Case "n = O".
  {
    intros m. induction m.
    SCase "m = O". simpl. unfold not. intros H1 H2. inversion H1.
    SCase "m = S m". simpl. unfold not. intros H1 H2. inversion H2.
  }
  Case "n = S n".
  {
    intros m. induction m.
    SCase "m = O". simpl. unfold not. intros H1 H2. inversion H2.
    SCase "m = S m". simpl. unfold not. intros H1 H2. inversion H2.
    apply IHn in H1. unfold not in H1. apply H1. assumption.
  }
Qed.
     
