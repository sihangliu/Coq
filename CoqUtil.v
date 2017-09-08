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

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

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

Inductive custom_list {A : Type} : list A -> Type :=
| nil_list : custom_list []
| cons l1 x l2 : custom_list l1 -> custom_list l2 -> custom_list (l1 ++ [x] ++ l2).                      

Check custom_list_rect.

Definition list_rect_custom (A : Type) (P : list A -> Type) (f1 : P [])
           (fn : forall x l1 l2, P l1 -> P l2 -> P (l1 ++ [x] ++ l2)) :
  forall l, P l.
  refine (fix F l :=
            match l with
            | [] => _
            | (x :: l) => _
            end). auto.
  pose proof (fn x nil l f1). apply X. auto.
Defined.


Theorem list_lemma : forall (A : Type) (l : list A), l = [] \/ exists f x g, l = f ++ [x] ++ g.
Proof.
  induction l using list_rect_custom.
  auto. right.
  exists l1, x, l2. auto.
Qed.

