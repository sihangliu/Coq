Require Export ProofObjects.

Check nat_ind.
Theorem mult_0_r' : forall n : nat, n * 0 = 0.
Proof.
  apply (nat_ind (fun n => n * 0 = 0) (eq_refl 0)
                 (fun n H => H)).
Qed.

Print mult_0_r'.

Theorem plus_one_r' : forall n:nat, n + 1 = S n.
Proof.
  apply (nat_ind (fun n => n + 1 = S n) (eq_refl 1)).
  intros n H. simpl. rewrite H. reflexivity.
  Show Proof.
Qed.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

(* 
  forall P : rgb -> Prop, 
  (P red) -> (P green) -> (P blue) -> 
  forall n : rgb, P n 
 *)
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

(*
 forall P : natlist -> Prop, 
 (P nnil) -> (forall (n : nat) (l : natlist), P l -> P (ncons n l)) -> 
 forall n : natlist, P n 
 *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Print natlist1_ind.

Inductive yesno : Type :=
  | yes : yesno
  | no  : yesno.

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.

(* 
  forall P : byntree -> Prop, 
  (P bempty) -> 
  (forall (y : yesno), P (bleaf y u)) ->
  (forall (a : yesno) (b : byntree) P b -> forall (c : byntree), P c -> P (nbranch a b c)) ->
  forall n : byntree, P n
 *)

Print byntree_ind.

Inductive ExSet : Type :=
| con1 (b : bool) : ExSet
| con2 (n : nat) (e : ExSet) : ExSet.

Print ExSet_ind.

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

(*
 forall (X : Type) (P : tree X -> Prop, 
 (forall (x : X), P (leaf x)) ->
 (forall (x : tree X), P x -> forall (y : tree X), P y -> P (node x y)) -> 
 forall n : tree X, P n
 *)

Print tree_ind.

(*
  mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m →
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m
 *)

Inductive mytype (X : Type) : Type :=
| constr1 (x : X) : mytype X
| constr2 (n : nat) : mytype X
| constr3 (m : mytype X) (n : nat) : mytype X.

Print mytype_ind.

(*

foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f1 : nat → foo X Y,
               (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀f2 : foo X Y, P f2
 *)

Inductive foo (X Y : Type) : Type :=
| bar (x : X) : foo X Y
| baz (y : Y) : foo X Y
| quux (f1 : nat -> foo X Y) : foo X Y.

Print foo_ind.

Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

(*
 forall (X : Type) (P : foo' X -> Prop), 
 (forall (l : list X) (f : foo' X), P f -> P (C1 l f)) ->
 (P C2) ->
 forall f : foo' X, P f. 
 *)

Print foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n : nat,
    P_m0r n.
Proof.
  apply nat_ind.
  reflexivity.
  intros n IHn.
  unfold P_m0r in *. simpl. apply IHn.
  Show Proof.
Qed.

Theorem plus_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IH].
  reflexivity.
  simpl. apply f_equal. apply IH.
Qed.

Theorem plus_comm' : forall n m : nat,
    n + m = m + n.
Proof.
  intros n. induction n as [|n' IHn].
  intros m. simpl. rewrite plus_n_O. reflexivity.
  intros m. simpl. rewrite <- plus_n_Sm. apply f_equal.
  apply IHn.
Qed.

