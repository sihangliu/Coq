Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* Custom Induction on Natural *)
Definition nat_rect_custom (P : nat -> Type) (f1 : P 0%nat) (f2 : P 1%nat)
           (f3 : forall n, P n -> P (S (S n))) : forall n, P n.
  refine (fix F n :=
            match n with
            | O => f1
            | S O => f2
            | S (S m) => f3 m _
            end).
  auto.
Defined.
Check nat_rect_custom.

Theorem nat_lemma : forall n : nat, n = 0%nat \/ n = 1%nat \/ exists m : nat, n = S (S m).
Proof.
  induction n using nat_rect_custom. auto. auto.
  right. right. exists n. auto.
Qed.


