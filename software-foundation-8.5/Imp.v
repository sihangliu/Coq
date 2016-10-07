Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => aeval a1 + aeval a2
    | AMinus a1 a2 => aeval a1 - aeval a2
    | AMult a1 a2 => aeval a1 * aeval a2
    end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. compute. auto. Qed.

  Print test_aeval1.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq b1 b2 => beq_nat (aeval b1) (aeval b2)
    | BLe b1 b2 => leb (aeval b1) (aeval b2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum a => ANum a
    | APlus (ANum 0) e2 => e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.


  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a. induction a.
    - auto.
    - destruct a1.
      + destruct n.
        * simpl. auto.
        * simpl. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
    - simpl. auto.
    - simpl. auto.
  Qed.

  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof. try reflexivity. Qed.

  Theorem silly2 : forall (P : Prop), P -> P.
  Proof.
    intros P Hp.
    try reflexivity.     
    apply Hp.
  Qed.

  Lemma foo : forall n, leb 0 n = true.
  Proof.
    intros n. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.

  Lemma foo' : forall n, leb 0 n = true.
  Proof.
    intros n. destruct n; simpl; reflexivity.
  Qed.

  Theorem optimize_0plus_sound': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    reflexivity.
    destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    destruct n; simpl; rewrite <- IHa2; reflexivity.
  Qed.

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try (left; reflexivity)).
  Qed.


  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq b1 b2 => BEq (optimize_0plus b1) (optimize_0plus b2)
    | BLe b1 b2 => BLe (optimize_0plus b1) (optimize_0plus b2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  
  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    assert (Ht : forall a1, aeval (optimize_0plus a1) = aeval a1)
      by apply optimize_0plus_sound.
    intros b. induction b.
    - reflexivity.
    - reflexivity.
    - simpl. repeat (rewrite Ht). reflexivity.
    - simpl. repeat (rewrite Ht). reflexivity.
    - simpl. rewrite IHb. reflexivity.
    - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  Qed.

  
  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega.
  Qed.

  Module aevalR_first_try.

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum n : aevalR (ANum n) n
    | E_APlus e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

    Notation "e '\\' n" := (aevalR e n) (at level 50, left associativity)
                           : type_scope.
  End aevalR_first_try.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n : (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

  Theorem aeval_iff_aevalR : forall a n, (a \\ n) <-> aeval a = n.
  Proof.
    intros a n. split. intros H.
    induction H; auto; simpl; rewrite IHaevalR1; rewrite IHaevalR2; auto.
    generalize dependent n.
    induction a; simpl; intros; subst; constructor; try apply IHa1; try apply IHa2; auto.
  Qed.

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> bevalR (BEq e1 e2) (beq_nat n1 n2)
  | E_BLe e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> bevalR (BLe e1 e2) (leb n1 n2)
  | E_BNot e b : bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd e1 e2 b1 b2 : bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2).

  Theorem beval_iff_bevalR : forall a n, (bevalR a n) <-> beval a = n.
  Proof.
    intros a n. split. intros H.
    induction H. auto. auto.
    simpl. specialize (aeval_iff_aevalR e1 n1); intros. destruct H1.
    specialize (aeval_iff_aevalR e2 n2); intros. destruct H3.
    pose proof H1 H. pose proof H3 H0. auto.
    simpl. specialize (aeval_iff_aevalR e1 n1); intros. destruct H1.
    specialize (aeval_iff_aevalR e2 n2); intros. destruct H3.
    pose proof H1 H. pose proof H3 H0. auto.
    simpl. rewrite IHbevalR. auto.
    simpl. rewrite IHbevalR1, IHbevalR2. auto.

    generalize dependent n.
    induction a; simpl; intros; subst.
    apply E_BTrue. apply E_BFalse.
    apply E_BEq. apply aeval_iff_aevalR. reflexivity.
    apply aeval_iff_aevalR. reflexivity.
    constructor. apply aeval_iff_aevalR. reflexivity.
    apply aeval_iff_aevalR. reflexivity.
    constructor. apply IHa. reflexivity.
    constructor. apply IHa1. reflexivity.
    apply IHa2. reflexivity.
  Qed.

  
