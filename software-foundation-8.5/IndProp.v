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

Theorem ev_even_iff : forall n,
    ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  apply ev_even; auto.
  intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Print ev_even_iff.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn. assumption.
  simpl. constructor. assumption.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m : ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  intros H. induction H. constructor. repeat constructor.
  apply ev_sum; assumption.
  intros. induction H. constructor. apply ev'_sum with (n := 2) (m := n).
  constructor. assumption.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H1 H2. induction H2. assumption.
  apply IHev. simpl in H1. apply evSS_ev in H1.
  assumption.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H1 H2.
  apply ev_sum with (n := n + m) (m := n + p) in H1.
  replace (n + m + (n + p)) with ((n + n) + (m + p)) in H1.
  apply ev_ev__ev with (n := n + n) in H1.
  auto. replace (n + n) with (double n).
Abort.

Module LeModule.

  Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m : le n m -> le n (S m).

  Notation "m <= n" := (le m n).

  Theorem test_le1 : 3 <= 3.
  Proof. apply le_n. Qed.
  Print test_le1.

  Theorem test_le2: 3 <= 6.
  Proof. repeat constructor. Qed.

  Print test_le2.
End LeModule.

Definition lt n m := (le (S n) m).

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq n : square_of n (n * n).

Theorem test_square : square_of 3 9.
Proof. repeat constructor. Qed.

Print test_square.

Inductive next_nat : nat -> nat -> Prop :=
  nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 n : ev n -> next_even n (S (S n))
| ne_2 n : ev (S n) -> next_even n (S n).

Inductive total_relation : nat -> nat -> Prop :=
| tt_1 n m : n <= m -> total_relation n m
| tt_2 n m : m < n -> total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=.

Lemma trans : forall m n o,
    m <= n -> n <= o -> m <= o.
Proof.
  induction 2. auto. auto.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n; auto.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H; auto.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  apply le_n. apply trans with (n := S n). auto.
  auto.
Qed.

Theorem le_plus_l : forall a b,
    a <= a + b.
Proof.
  intros a b. induction b.
  rewrite plus_n_O. auto.
  rewrite <- plus_n_Sm. apply le_S. auto.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H. split.
  induction H; swap 1 2. 
  unfold "<". unfold "<" in IHle.
  apply le_S. auto.
  unfold "<". apply  n_le_m__Sn_le_Sm.
  apply le_plus_l.

  induction H.
  unfold "<". apply n_le_m__Sn_le_Sm. rewrite plus_comm.
  apply le_plus_l.
  unfold "<". unfold "<" in IHle.
  apply le_S. auto.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold "<". intros n m H. apply le_S. auto.
Qed.

Theorem leb_complete : forall n m,
  Basics.leb n m = true -> n <= m.
Proof.
  induction n.
  intros m H. apply O_le_n.
  destruct m. intros H. inversion H.
  intros H. simpl in H. pose proof IHn m H.
  apply n_le_m__Sn_le_Sm. assumption.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  Basics.leb n m = true.
Proof.
  intros n m H. generalize dependent n.
  induction m.
  intros n H. destruct n.
  reflexivity. inversion H.
  intros n H. destruct n.
  reflexivity. simpl. apply IHm.
  apply Sn_le_Sm__n_le_m. assumption.
Qed.

Theorem leb_true_trans : forall n m o,
    Basics.leb n m = true -> Basics.leb m o = true -> Basics.leb n o = true.
Proof.
  intros n m o H1 H2. pose proof leb_complete n m H1.
  pose proof leb_complete m o H2.
  apply leb_correct.
  pose proof trans _ _ _ H H0. assumption.
Qed.

Theorem leb_iff : forall n m,
  Basics.leb n m = true <-> n <= m.
Proof.
  intros n m. split. apply leb_complete.
  apply leb_correct.
Qed.

