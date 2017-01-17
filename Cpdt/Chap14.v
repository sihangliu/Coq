
Ltac find_if :=
  match goal with
  |[|- if ?X then _ else _] => destruct X
  end.

Theorem hmm : forall (a b c : bool),
    if a then if b then True else True
    else if c then True else True.
Proof.      
  intros; repeat find_if; constructor.
Qed.

Ltac find_if_inside :=
  match goal with
  | [|- context [if ?X then _ else _]] => destruct X
  end.

Theorem hmm' : forall (a b c : bool),
    if a then if b then True else True
    else if c then True else True.
Proof.
  intros; repeat find_if_inside; constructor.
Qed.

Theorem hmm2 : forall (a b : bool),
    (if a then 42 else 42) = (if b then 42 else 42).
Proof.
  intros; repeat find_if_inside; auto.
Qed.

Ltac my_auto :=
  repeat match goal with
         | [H : ?P |- ?P] => exact H
         | [|- True] => constructor
         | [|- _ /\ _] => constructor
         | [|- _ -> _] => intro
         | [H : False |- _] => destruct H
         | [H : _ /\ _ |- _] => destruct H
         | [H : _ \/ _ |- _] => destruct H
         | [H1 : ?P -> ?Q, H2: ?P |- _] => specialize (H1 H2)
         end.

Section propositional.
  Variables P Q R : Prop.
  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
    my_auto.
  Qed.
End propositional.

Theorem m1 : True.
  match goal with
  |[|- _] => intro
  |[|- True] => constructor
  end.
Qed.

Theorem m2 : forall (P Q R : Prop), P -> Q -> R -> Q.
  intros; match goal with
  |[H : _ |- _] => exact H
  end.  
Qed.

Ltac notHyp P :=
  match goal with
  | [_ : P |- _] => fail 1
  | _ => match P with
        | ?P1 /\ ?P2 => first [notHyp P1 | notHyp P2 | fail 2]
        | _ => idtac
        end
  end.

Ltac extend pf :=
  let t := type of pf in
  notHyp t; generalize pf; intro.

Ltac completer :=
  repeat match goal with
         | [|- _ /\ _] => constructor
         | [H : _ /\ _ |- _] => destruct H
         | [H1 : ?P -> ?Q, H2 : ?P |- _] => specialize (H1 H2)
         | [|- forall x, _] => intro
         | [H1 : forall x, ?P x -> _, H2 : ?P ?X |- _] => extend (H1 X H2)
         end.


                
Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.
  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.
  Theorem fo : forall (y x: A), P x -> S x.
    completer.
    assumption.
  Qed.
End firstorder.

Ltac completer' :=
  repeat match goal with
         | [|- _ /\ _] => constructor
         | [H : ?P /\ ?Q |- _] => destruct H;
                               repeat match goal with
                                      |[H' : P /\ Q |- _] => clear H'
                                      end
         | [H1 : ?P -> _, H2 : ?P |- _] => specialize (H1 H2)
         | [|- forall x, _] => intro
         | [H1 : forall x, ?P x -> _, H2 : ?P ?X |- _] => extend (H1 X H2)
         end.


Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.
  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.
  Theorem fo' : forall (y x: A), P x -> S x.
    completer'.
  Abort.
End firstorder'.

Theorem t1 : forall x : nat, x = x.
  match goal with
  | [|- forall x, _] => trivial
  end.
Qed.

Theorem t1' : forall x : nat, x = x.
  match goal with
  | [|- forall x, ?P] => trivial
  end.
Qed.  
Require Import Coq.Lists.List.
Import ListNotations.

Ltac length ls :=
  match ls with
  | nil => O
  |  _ :: ?t =>
     let t' := length t in
     constr:(S t')
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
  pose n.
Abort.

Ltac map T f :=
  let rec map' ls :=
      match ls with
      | nil => constr:(@nil T)
      | ?x :: ?ls' =>
        let x' := f x in
        let ls'' := map' ls' in
        constr:(x' :: ls'')
      end
  in map'.

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:(x, x)) (1 :: 2 :: 3 :: nil) in
  pose ls.
Abort.

Reset length.

Ltac length ls k :=
  idtac ls;
  match ls with
  | nil => k O
  | _ :: ?ls' =>
    length ls' ltac:(fun n => k (S n))
  end.

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
Abort.

Ltac inserter n :=
  intuition;
  match n with
  | S ?n' =>
    match goal with
    | [H : forall x : ?T, _, y : ?T |- _] => generalize (H y); inserter n'
    end
  end.

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.
  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).
  Theorem test_inster : forall x, P (g x x) -> Q (f x).
    inserter 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).
  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
    inserter 3.
  Qed.
End test_inster.

