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

Print NoDup.


Inductive Edge : nat -> nat -> nat -> Prop :=
  Arc a b c : Edge a b c.

Inductive Path : nat -> nat -> nat -> Prop :=
|Unit_path a b w : Edge a b w -> Path a b w
|Cons_path a b c w v m : Edge a b w -> Path b c v -> m <= w -> m <= v -> Path a c m.

SearchAbout (_ <= _).
Check 1 <= 0.
Print Path_ind.

(* winner is 5th node E *)
Lemma path_40 : Path 4 0 25.
Proof.
  constructor 2 with (a := 4) (b := 3) (c := 0) (w := 31) (v := 25).
  apply (Arc 4 3 31).
  constructor 2 with (a := 3) (b := 2) (c := 0) (w := 28) (v := 25).
  apply (Arc 3 2 28).
  constructor 2 with (a := 2) (b := 1) (c := 0) (w := 29) (v := 25).
  apply (Arc 2 1 29).
  constructor 1 with (a := 1) (b := 0) (w := 25).
  apply (Arc 1 0 25).
  omega. omega. omega. omega. omega. omega.
Qed.

Print path_40.

Lemma path_41 : Path 4 1 28.
Proof.
  constructor 2 with (a := 4) (b := 3) (c := 1) (w := 31) (v := 28).
  apply (Arc 4 3 31).
  constructor 2 with (a := 3) (b := 2) (c := 1) (w := 28) (v := 29).
  apply (Arc 3 2 28).
  constructor 1 with (a := 2) (b := 1) (w := 29).
  apply (Arc 2 1 29).
  omega. omega. omega. omega.
Qed.

Module  Vote.
  Variable cand : Type.
  Inductive Edge : cand -> cand -> nat -> Prop :=
    Arc l m w : Edge l m w.

  Variable a b c d e : cand.
  Variable n n1 n2 n3 n4 : nat.

  Inductive Path : cand -> cand -> nat -> Prop :=
    | Unit_path a b w : Edge a b w -> Path a b w
    | Cons_path a b c w v m : Edge a b w -> Path b c v -> m <= w -> m <= v
                                 -> Path a c m.
  Check [Edge a b 5; Edge b c 10].
  Definition max (a b : nat) : Prop :=
    a >= b \/ b >= a.
  Lemma mx : max 2 3.
  Proof.
    unfold max.
    right. omega.
  Qed.
  
    Lemma path_ea : forall (n1 n2 n3 n4 n m o : nat) (a b c d e : cand),
      n <= n1 /\ n <= n2 /\ n <= n3 /\ n <= n4 /\ m <= n2 /\ m <= n3 /\ m <= n4
      /\ o <= n3 /\ o <= n4 /\ n <= m /\ m <= o
      -> Edge e d n1 -> Edge d c n2 -> Edge c b n3
      -> Edge b a n4 -> Path e a n.
  Proof.
    intros n1 n2 n3 n4 n m o a b c d e H E1 E2 E3 E4.
    constructor 2 with (b := d) (w := n1) (v := m).
    assumption.
    constructor 2 with (b := c) (w := n2) (v := o).
    assumption.
    constructor 2 with (b := b) (w := n3) (v := n4).
    assumption.
    constructor 1 with (a := b) (b := a). assumption. omega. omega. omega. omega. omega.
    omega.
  Qed.

  Lemma path_eb : forall (n1 n2 n3 n m : nat) (b c d e : cand),
      n <= n1 /\ n <= n2 /\ n <= n3 /\ m <= n2 /\ m <= n3 /\ n <= m -> Edge e d n1 -> Edge d c n2 ->
      Edge c b n3 -> Path e b n.
  Proof.
    intros n1 n2 n3 n m b c d e H E1 E2 E3.
    constructor 2 with (b := d) (w := n1) (v := m).
    assumption.
    constructor 2 with (b := c) (w := n2) (v := n3).
    assumption.
    constructor 1. assumption. omega. omega. omega. omega.
  Qed.

  Lemma path_ec : forall (n1 n2 n : nat) (c d e : cand),
      n <= n1 /\ n <= n2 -> Edge e d n1 -> Edge d c n2 -> Path e c n.
  Proof.
    intros n1 n2 n c d e H E1 E2.
    constructor 2 with (b := d) (w := n1) (v := n2).
    assumption.
    constructor 1. assumption. omega. omega.
  Qed.

  Lemma path_ed : forall (n1 : nat) (d e : cand),
      Edge d e n1 -> Path d e n1.
  Proof.
    intros n1 d e E.
    constructor 1. assumption.
  Qed.
  
End Vote.

Module Evote.
  Require Import Notations.
  Require Import Coq.Lists.List.
  Require Import Coq.Arith.Le.
  Require Import Coq.Numbers.Natural.Peano.NPeano.
  Require Import Coq.Arith.Compare_dec.
  Require Import Coq.omega.Omega.
  Import ListNotations.

  Parameter cand : Type.
  Parameter cand_all : list cand.
  Hypothesis cand_fin : forall c : cand, In c cand_all.
  Parameter edge : cand -> cand -> nat.

  Inductive Path (k : nat) : cand -> cand -> Prop :=
  | Unit c d : edge c d >= k -> Path k c d
  | Cons c d e : edge c d >= k -> Path k d e -> Path k c d.

  Inductive PathT (k : nat) : cand -> cand -> Type :=
  | UnitT c d : edge c d >= k -> PathT k c d
  | ConsT c d e : edge c d >= k -> PathT k d e -> PathT k c e.

  Definition wins (c : cand) :=
    forall d : cand,
      exists k : nat, ((Path k c d) /\ (forall l : nat, Path l d c -> l <= k)). 

  Fixpoint all_pairs {A : Type} (l : list A) : list (A * A) :=
    match l with
    | [] => []
    | c :: cs =>
      (c, c) :: (all_pairs cs) ++ (map (fun x => (c, x)) cs) ++ (map (fun x => (x, c)) cs)
    end.
  Compute (all_pairs [1;2;3]).

  Hypothesis cand_dec : forall c d : cand, {c = d} + {c <> d}.
End Evote.
