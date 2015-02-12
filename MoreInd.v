Require Export "ProofObjects".

Check ev_SS.
Check nat_ind ev ev_O.
(*
ev_SS
     : forall n : nat, ev n -> ev (S (S n))
 *)

Check nat_ind.

(*
nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
 *)

Theorem mult_0_r' : forall n:nat,
                      n * 0 = 0.
Proof.
  apply nat_ind. Show Proof.
  Case "O". SearchAbout ( _ * O = O ). apply mult_O_r.
  Show Proof.
  Case "n = S".
  simpl. intros n H. assumption.
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind. Show Proof.
  Case "O". reflexivity. Show Proof.
  Case "S".
  intros n IHn'. simpl. apply f_equal. assumption. Show Proof.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.
Check natlist1_ind.

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
Print byntree_ind.

(*
 ExSet_ind :
         ∀P : ExSet → Prop,
             (∀b : bool, P (con1 b)) →
             (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀e : ExSet, P e *)

Inductive ExSet :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.
Print ExSet_ind.

Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
Print list_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.

(*

mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m → 
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m *)
Inductive mytype ( X : Type ) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.
Print mytype_ind.

(*
mytype_ind = 
fun (X : Type) (P : mytype X -> Prop) => mytype_rect X P
     : forall (X : Type) (P : mytype X -> Prop),
       (forall x : X, P (constr1 X x)) ->
       (forall n : nat, P (constr2 X n)) ->
       (forall m : mytype X, P m -> forall n : nat, P (constr3 X m n)) ->
       forall m : mytype X, P m
 *)

(*

 foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f1 : nat → foo X Y,
               (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀f2 : foo X Y, P f2   *)
Inductive foo ( X Y : Type ) : Type :=
| bar : X ->  foo X Y
| baz : Y -> foo X Y
| quxx : ( nat -> foo X Y ) -> foo X Y. 
Print foo_ind.

(*
foo_ind = 
fun (X Y : Type) (P : foo X Y -> Prop) => foo_rect X Y P
     : forall (X Y : Type) (P : foo X Y -> Prop),
       (forall x : X, P (bar X Y x)) ->
       (forall y : Y, P (baz X Y y)) ->
       (forall f1 : nat -> foo X Y,
        (forall n : nat, P (f1 n)) -> P (quxx X Y f1)) ->
       forall f2 : foo X Y, P f2

Argument scopes are [type_scope type_scope _ _ _ _ _]

 *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

Print foo'_ind.

Lemma pred_of_positive : forall n, 1 <= n -> exists p : nat , n = S p.
Proof.
  intros n H. induction n. inversion H.
  exists n. reflexivity.
Qed.

Definition pred_spec (n:nat) :=
  { m : nat | n = 0 /\ m = 0 \/ n = S m }.

Definition predecessor : forall n : nat , pred_spec n.
  intros n. induction n.
  unfold pred_spec. exists 0. left. split. reflexivity. reflexivity.
  unfold pred_spec. exists n. right. reflexivity.
Defined.

Check { m : nat | 2 = S 1 }.

Extraction pred_spec.
Extraction predecessor.

Inductive prop : Prop :=
  prop_intro : Prop -> prop.
Check ( prop_intro prop ).

Theorem le_reverse_rules :
  forall n m : nat, n <= m -> n = m \/ exists p, n <= p /\ m = S p.
Proof.
  intros n m H. inversion H. left. reflexivity.
  right. exists m0. split. assumption. reflexivity.
Qed.
