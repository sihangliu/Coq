Require Export Logic.

Inductive  ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS n : ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. repeat (constructor 2); constructor 1. Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof. intros. repeat (constructor 2). trivial. Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros. induction n. simpl. constructor 1.
  simpl. constructor 2. trivial.
Qed.

Theorem evenb_minus2: forall n,
  evenb n = true -> evenb (pred (pred n)) = true.
Proof.
  intros [ | [ | n']].
  - auto.
  - auto.
  - simpl. auto.
Qed.

Theorem ev_minus2: forall n,
    ev n ->  ev (pred (pred n)).
Proof.
  intros n H. inversion H. simpl. constructor 1.
  simpl. assumption.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H. inversion H.
  trivial.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n H. inversion H. exists 0. auto.
  assert (I : (exists k, n0 = double k) -> (exists k, S (S n0) = double k)).
  {
    intros [k' Hk'].
    rewrite Hk'. exists (S k'). simpl. auto.
  }
  apply I.
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n H. induction H as [|n' H' IH].
  exists 0. auto. destruct IH as [k' Hk'].
  exists (S k'). simpl. repeat  (apply f_equal). assumption.
Qed.


Inductive NoDup {X : Type} : list X -> Prop :=
|basecase : NoDup []
|nextcase x l : ~ In x l ->  NoDup l -> NoDup (x :: l). 

Lemma nodup_1 : NoDup [0;1;2;4].
Proof.
  constructor 2. simpl. unfold not. intros.
  inversion H as [H1 | [H1 | H1]].
  inversion H1. inversion H1. inversion H1.
  inversion H0. inversion H0.
  constructor 2. simpl. unfold not. intros.
  inversion H. inversion H0. inversion H0. inversion H1.
  inversion H1. constructor 2. unfold not. intros.
  inversion H. inversion H0. inversion H0.
  constructor 2. unfold not. intros. inversion H.
  constructor 1.
Qed.


 
Fixpoint nodup {X : Type} (l : list X) : Prop :=
  match l with
  | nil => True
  | h :: t => ~ In h t /\ nodup t
  end.

Lemma equinodup : forall (X : Type) (l : list X), NoDup l <-> nodup l.
Proof.
  split.
  {
    intros. induction H.
    - simpl. auto.
    - simpl. split. trivial. trivial.
  }
  {
    intros. induction l.
    -  constructor 1.
    - constructor 2. simpl in H. destruct H as [H1 H2]. trivial.
      apply IHl. destruct H as [H1 H2]. trivial.
  }
Qed.

