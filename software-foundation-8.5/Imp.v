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
