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

