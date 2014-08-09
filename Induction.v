Require Export Basic.
Require String. Open Scope string_scope.

Ltac move_to_top x := 
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident ( x ) constr ( v ) :=
  let H := fresh in
  assert ( x = v ) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident ( x ) constr ( name ) :=
  first [ 
      set ( x := name ) ; move_to_top x 
    | assert_eq x name ; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr ( name ) := Case_aux Case name.
Tactic Notation "SCase" constr ( name ) := Case_aux SCase name.
Tactic Notation "SSCase" constr ( name ) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr ( name ) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool, andb b c = true -> b = true.
Proof.
intros b c H.
destruct b.
Case "b = true".
  reflexivity.
Case "b = false".
  rewrite <- H.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
intros b c H. destruct b.  rewrite <- H.
reflexivity.  rewrite <- H. destruct c.
rewrite -> H. reflexivity. reflexivity.
Qed.

Theorem andb_true_elim3 : forall b c : bool, andb b c = true -> c = true.
Proof.
intros b c H.
destruct c.
Case "c = true".
   reflexivity.
Case "c = false".
   rewrite <- H.
   destruct b.
   SCase "b = true".
      reflexivity.
   SCase "b = false".
      reflexivity.
Qed.

Theorem plus_0_r_firsttry  : forall n : nat, n + 0 = n.
Proof.
intros. induction  n as [ O | n' ].
Case "n = O".
   reflexivity.
Case "n = S n'".
   simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
Theorem minus_diag : forall n, minus n n = 0.
Proof.
intros n. destruct n as [ O | n' ].
Case "n = O". 
    reflexivity.
Case "n = S n'".
    simpl. destruct n' as [ O | n'' ].
    SCase "n' = O".
         reflexivity.
    SCase "n' = S n''".
         simpl.
You get the idea. You keep doing this so go for induction or probably Ltac".
*)

Theorem minus_diag : forall n, minus n n = 0 .
Proof. 
intros n. induction n as [ | n' ].
Case "n = O".
   reflexivity.
Case "n = S n'".
   simpl.
   rewrite -> IHn'. reflexivity.
Qed.



Theorem mult_O_r : forall n : nat, n * 0 = 0. 
Proof.
intros n. induction n as [ | n' ].
Case "n = O".
  reflexivity.
Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S ( n + m ) = n + S m.
Proof.
intros n m. induction n as [ | n' ].
Case "n = O".
   reflexivity.
Case "n = S n'".
   simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall m n : nat, m + n = n + m. 
Proof.
intros m n. induction  m as [ | m' ].
Case "m = O".
  simpl. rewrite ->  plus_0_r_firsttry. (* we have used the previous proof *)
  reflexivity.
Case "m = S m'".
  simpl. rewrite -> IHm'. rewrite -> plus_n_Sm. (* we have used the prev proof *)
  reflexivity.
Qed.

Theorem plus_assoc : forall m n p : nat, 
   n + ( m + p ) = ( n + m ) + p.
Proof.
intros m n p. induction n as [ | n' ].
Case "n = O".
   reflexivity.
Case "n = S n'".
   simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double ( n : nat ) : nat := 
  match n with
  | O => O
  | S n' =>  S ( S ( double n' ) )
  end. 

Lemma double_plus : forall n : nat, double n = n + n.
Proof.
intros n. induction n as [ | n' ].
Case "n = O".
  reflexivity.
Case "n = S n'".
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem mult_O_plus' : forall n m : nat, 
   ( 0 + n ) * m =  n * m.
Proof.
intros n m.
assert ( H : 0 + n = n ).
 Case "Proof of assertion". reflexivity.
rewrite -> H. reflexivity.
Qed.

(*
Theorem plus_rearrange_firsttry : forall m n p q : nat, 
    ( n + m ) + ( p + q ) = ( m + n ) + ( q + p ).
Proof.
intros m n p q.
rewrite -> plus_comm.
*)

Theorem plus_rearrange : forall m n p q : nat,
    ( n + m ) + ( p + q ) = ( m + n ) + ( q + p ).
Proof.
intros n m p q.
assert ( H1 : n + m = m + n ).
  Case "Proof of assertion".
  rewrite -> plus_comm. reflexivity.
assert ( H2 : p + q = q + p ).
  Case "Proof of assertion".
  rewrite -> plus_comm. reflexivity.
rewrite -> H1. rewrite -> H2. reflexivity.
Qed.

Theorem plus_swap : forall m n p : nat , 
   n + ( m + p ) = m + ( n + p ).
Proof.
intros n m p. rewrite -> plus_assoc.
assert ( H : m + n = n + m ).
   Case "Proof of assertion".
   rewrite -> plus_comm. reflexivity.
rewrite -> H.  rewrite <- plus_assoc. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat, 
   m * n = n * m.
Proof.
intros m n. destruct m as [ | m' ].
