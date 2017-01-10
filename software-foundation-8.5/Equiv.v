Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state), beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state), (c1 / st \\ st') <-> (c2 / st \\ st'). 

(* X := Id 0, Y := Id 1, Z := Id 2 *)

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
        X ::= APlus (AId X) (ANum 1)
        END.
(* while !(x < 0) do x ::= x + 1 
   Infinite loop *)

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
      X ::= APlus (AId X) (ANum 1);;
      Y ::= ANum 1
      ELSE
      Y ::= ANum 0
      FI;;
      X ::= AMinus (AId X) (AId Y);;
      Y ::= ANum 0.
(* condition true x := 1, y := 1 => x := 0 y := 0 *)  

Definition prog_c : com :=
  SKIP.
(* x := 0 y := 1 *)

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
        END.
(* condition false because x := 0 so final output is x := 0 y := 1 *)

Definition prog_e : com :=
  Y ::= ANum 0.
(* x := 0 y := 0 *)

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
    WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
    END.
(* y := 1 => condition true because x := 0 and y := 1 
   and loop continue because no change in x and y always remains 1 
   infinite loop *)

Definition prog_g : com :=
  WHILE BTrue DO
        SKIP
        END.
(* infinite loop *)

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
        X ::= APlus (AId X) (ANum 1)
        END.
(* condition false and no loop execution. x := 0 and y := 1 *)

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
        X ::= APlus (AId Y) (ANum 1)
        END.
(* condition true x := 1 and now condition false x := 1 y := 1 *)

Definition equiv_classes : list (list com) :=
  [[prog_a; prog_f; prog_g]; [prog_b; prog_e]; [prog_c; prog_d; prog_h]; [prog_i]].

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Theorem skip_left: forall c, cequiv (SKIP;; c) c.
Proof.
  unfold cequiv. intros c st st'. split.
  intros H. inversion H. subst.
  inversion H2.  subst. assumption.
  intros H. apply E_Seq with st. apply E_Skip.
  assumption.
Qed.

Theorem skip_right: forall c, cequiv (c ;; SKIP) c.
Proof.
  unfold cequiv. intros c st st'. split.
  intros H. inversion H. subst. inversion H5. subst.
  assumption.
  intros H. apply E_Seq with st'. assumption.
  apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
    cequiv (IFB BTrue THEN c1 ELSE c2 FI)
           c1.
Proof.
  unfold cequiv. intros c1 c2 st st'.
  split. intros H. inversion H. subst.
  assumption. subst. inversion H5.
  intros H. apply E_IfTrue. auto.
  assumption.
Qed.

Theorem IFB_false: forall b c1 c2,
    bequiv b BFalse ->
    cequiv
      (IFB b THEN c1 ELSE c2 FI)
      c2.
Proof.
  unfold bequiv, cequiv. intros. split; intros.
  inversion H0; subst. simpl in H.
  specialize (H st). rewrite H6 in H. inversion H.
  assumption.
  simpl in H. apply E_IfFalse. specialize (H st).
  assumption. assumption.
Qed.

Theorem swap_if_branches: forall b e1 e2,
    cequiv
      (IFB b THEN e1 ELSE e2 FI)
      (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv. intros. split; intros.
  inversion H; subst. apply E_IfFalse. simpl.
  apply  negb_false_iff. auto. auto.
  apply E_IfTrue. simpl. apply negb_true_iff. auto. auto.

  inversion H; subst. simpl in H5. apply negb_true_iff in H5.
  apply E_IfFalse. auto. auto.
  simpl in H5. apply negb_false_iff in H5. apply E_IfTrue. auto.
  auto.
Qed.

Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv
      (WHILE b DO c END)
      SKIP.
Proof.
  unfold bequiv, cequiv. split; intros.
  simpl in H. inversion H0; subst. apply E_Skip.
  specialize (H st). rewrite H in H3. inversion H3.
  simpl in H. inversion H0; subst. apply E_WhileEnd.
  specialize (H st'). assumption.
Qed.

Lemma WHILE_true_nonterm : forall b c st st',
    bequiv b BTrue ->
    ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  unfold bequiv in Hb. specialize (Hb st).
  rewrite Hb in H. simpl in H. inversion H.
  apply IHceval2. auto.
Qed.


Program Fixpoint tmp (a b : nat) := a + b.



Theorem WHILE_true: forall b c,
    bequiv b BTrue ->
    cequiv
      (WHILE b DO c END)
      (WHILE BTrue DO SKIP END).
Proof.
  unfold cequiv. split; intros.
  remember (WHILE b DO c END) as cw eqn:Hcw.
  induction H0; inversion Hcw; subst; clear Hcw.
  specialize (H st). rewrite H0 in H. inversion H.
  specialize (WHILE_true_nonterm b c st' st'' H); intros.
  contradiction.

  apply WHILE_true_nonterm in H0. inversion H0.
  unfold bequiv. auto.
Qed.
