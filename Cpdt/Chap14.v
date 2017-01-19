
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

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.
Theorem and_True_prem : forall P Q,
    (P /\ True -> Q) -> (P -> Q).
Proof.
  imp.
Qed.


Theorem and_True_conc : forall P Q,
    (P -> Q /\ True) -> (P -> Q).
  imp.
Qed.

Theorem pick_perm1 : forall P Q R S,
    (P /\ (Q /\ R) -> S) ->
    ((P /\ Q) /\ R -> S).
  imp.
Qed.

Theorem pick_perm2 : forall P Q R S,
    (Q /\ (P /\ R) -> S) ->
    ((P /\ Q) /\ R -> S).
  imp.
Qed.

Theorem comm_perm : forall P Q R,
    (P /\ Q -> R) ->
    (Q /\ P -> R).
  imp.
Qed.

Theorem pick_conc1 : forall P Q R S,
    (S -> P /\ (Q /\ R)) ->
    (S -> (P /\ Q) /\ R).
  imp.
Qed.

Theorem pick_conc2 : forall P Q R S,
    (S -> Q /\ (P /\ R)) ->
    (S -> (P /\ Q) /\ R).
  imp.
Qed.

Theorem comm_conc : forall P Q R,
    (R -> P /\ Q) ->
    (R -> Q /\ P).
  imp.
Qed.

Ltac search_perm tac :=
  let rec search P :=
      tac
      || (apply and_True_prem; tac)
      || match P with
        | ?P1 /\ ?P2 =>
          (apply pick_perm1; search P1)
          || (apply pick_perm2; search P2)
        end
  in match goal with
     | [|- ?P /\ _ -> _] => search P
     | [|- _ /\ ?P -> _] => apply comm_perm; search P
     | [|- _ -> _] => progress (tac || (apply and_True_prem; tac))
     end.



Ltac search_conc tac :=
  let rec search P :=
      tac
      || (apply and_True_conc; tac)
      || match P with
        | ?P1 /\ ?P2 =>
          (apply pick_conc1; search P1)
          || (apply pick_conc2; search P2)
        end
  in match goal with
     | [|- _ -> ?P /\ _] => search P
     | [|- _ -> _ /\ ?P] => apply comm_conc; search P
     | [|- _ -> _] => progress (tac || (apply and_True_conc; tac))
     end.

Theorem False_perm : forall P Q,
    False /\ P -> Q.
  imp.
Qed.

Theorem True_conc : forall (P Q : Prop),
    (P -> Q) ->
    (P -> (True /\ Q)).
  imp.
Qed.

Theorem Match : forall (P Q R : Prop),
    (Q -> R) ->
    (P /\ Q -> P /\ R).
  imp.
Qed.

Theorem ex_perm : forall (T : Type) (P : T -> Prop) (Q R : Prop),
    (forall x, P x /\ Q -> R) ->
    (ex P /\ Q -> R).
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) (x : T),
    (Q -> P x /\ R) ->
    (Q -> ex P /\ R).
  imp.
Qed.

Theorem imp_True : forall P,
    P -> True.
  imp.
Qed.

Ltac matcher :=
  intros;
  repeat search_perm ltac:(simple apply False_perm || (simple apply ex_perm; intro));
  repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
                           || search_perm ltac:(simple apply Match));
  try simple apply imp_True.

Theorem t2: forall P Q : Prop,
    Q /\ (P /\ False) /\ P -> P /\ Q. 
  imp.
Qed.

(* matcher is not able to solve the lemma *)

Print t2.
Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) -> Q /\ (exists x, P x).
  imp.
Qed.

Print t4.

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
  intros. evar (y : nat).
  let y' := eval unfold y in y in clear y; specialize (H y').
  apply H.
Qed.

Ltac insterU H :=
  repeat match type of H with
         | forall x : ?T, _ =>
           let x := fresh "x" in
           evar (x : T);
           let x' := eval unfold x in x in clear x; specialize (H x)
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1. 
  intros H; insterU H; apply H.
Qed.


Ltac insterKeep H :=
  let H' := fresh "H'" in
  generalize H; intro H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.
  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
      P v1 u1 -> P v2 u2 -> P (f v1 v2) (g u1 u2).
  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros. do 2 insterKeep H1. specialize (H' v1).
    specialize (H'0 v2).
    repeat match goal with
           | [H : ex _ |- _] => destruct H
           end.
    eauto.
  Qed.
End t6.  

Reset insterU.

Ltac insterU tac H :=
  repeat match type of H with
         | forall x : ?T, _ =>
           match type of T with
           | Prop =>
             (let H' := fresh "H'" in
              assert (H' : T) by solve [tac];
              specialize (H H'); clear H')
             || fail 1
           | _ =>
             let x := fresh "x" in
             evar (x : T);
             let x' := eval unfold x in x in
                 clear x; specialize (H x')
           end
         end.

Ltac insterKeep tac H :=
  let H' := fresh "H'" in
  generalize H; intro H'; insterU tac H'.

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.
  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
      P v1 u1 -> P v2 u2 -> P (f v1 v2) (g u1 u2).
  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep ltac:(idtac; match goal with
                                         | [H : Q ?v |- _] =>
                                           match goal with
                                           | [_ : context [P v _] |- _] => fail 1
                                           | _ => apply H
                                           end
                                         end) H1;
    repeat match goal with
           | [H : ex _ |- _]=> destruct H
           end; eauto.
    Qed.
End t7.                                             

Theorem t8 : exists p : nat * nat, fst p = 3.
  econstructor; instantiate (1 := (3, 2)); reflexivity.
Qed.


Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.

Theorem t9 : exists p : nat * nat, fst p = 3.
  econstructor; match goal with
                | [|- fst ?x = 3] => equate x (3, 2)
                end; reflexivity.
Qed.
