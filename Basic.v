
Inductive day : Type := 
  | monday : day 
  | tuesday : day 
  | wednesday : day 
  | thrusday : day 
  | friday : day
  | saturday : day 
  | sunday : day.

Definition next_weekday ( d : day ) : day := 
 match d with 
     | monday => tuesday
     | tuesday => wednesday
     | wednesday => thrusday
     | thrusday => friday
     | friday => monday
     | saturday => monday
     | sunday => monday 
 end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday friday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type := 
 | true : bool
 | false : bool.

Definition negb ( b : bool ) : bool := 
  match b with
      | true => false
      | false => true
  end.

Definition andb ( b1 : bool ) ( b2 : bool ) : bool := 
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb ( b1 : bool ) ( b2 : bool ) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Example test_orb1 : ( orb true false ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2 : ( orb true true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3 : ( orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4 : ( orb false false ) = false.
Proof. simpl. reflexivity. Qed.

Definition nandb ( b1 : bool ) ( b2 : bool ) : bool := 
  match b1 with 
  | false => true
  | true => if b2 then false else true
  end.

Example test_nandb1 : ( nandb true false ) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2 : ( nandb true true ) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 ( b1 : bool ) ( b2 : bool ) ( b3 : bool ) : bool := 
  match b1 with 
      | false => false
      | true => if b2 then b3 else false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check ( negb true ) .
Check negb.
Check andb.


Module Playground1.

Inductive nat : Type := 
   | O : nat
   | S : nat -> nat.

Definition pred ( n : nat ) : nat := 
  match n with 
  | O => O
  | S n => n
  end.

End Playground1.

Definition minustwo ( n : nat ) : nat := 
  match n with 
  | O => O
  | S O => O
  | S ( S n ) => n
  end.

Check ( S ( S ( S ( S O )))).
Eval simpl in ( minustwo 4 ).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb ( n : nat ) : bool := 
   match n with 
   | O => true
   | S O => false
   | S ( S n' ) => evenb n'
   end.

(*
Fixpoint oddb ( n : nat ) : bool := 
  match n with 
  | O => false
  | S O => true
  | S ( S n' ) => oddb n'
  end.
*)

Definition oddb ( n : nat ) : bool := negb ( evenb n ).

Example test_oddb1 : ( oddb ( S O ) ) = true.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus ( n : nat ) ( m : nat ) : nat := 
  match n with
  | O => m
  | S n' => S ( plus n' m ) 
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult ( n m : nat ) : nat := 
  match n with
   | O => O
   | S n' => plus m ( mult n' m )
  end.

Eval simpl in ( mult 3 3 ).

Example test_mult: ( mult 3 3 ) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus ( n m : nat ) : nat :=
 match n, m with
 | O, _ => O
 | S _, O => n
 | S n', S m' => minus n' m'
 end.

End Playground2.

Fixpoint exp ( base power : nat ) : nat := 
  match power with
  | O => S O
  | S p => mult base ( exp base p )
  end.

Fixpoint factorial ( n : nat ) : nat := 
  match n with 
  | O => S O
  | S n' => mult n ( factorial n' )
  end. 

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := ( plus x y ) 
                      ( at level 50, left associativity )
                      : nat_scope.
Notation "x - y" := ( minus x y )
                      ( at level 50, left associativity )
                      : nat_scope.

Notation "x * y" := ( mult x y )
                      ( at level 40, left associativity )
                      : nat_scope.

Check (( O + 1 ) + 1 ) * 2 .

Fixpoint beq_nat ( n m : nat ) : bool := 
  match n with 
  | O => match m with 
         | O => true
         | _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat ( n m : nat ) : bool := 
  match n with
  | O => true 
  | S n' => match m with 
            | O => false
            | S m' => ble_nat n' m'
            end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat ( n m : nat ) : bool := andb ( negb ( beq_nat n m ) ) ( ble_nat n m ).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. compute. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. compute. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, O + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_1 : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_O_1 : forall n : nat, O * n = O.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat, 
         n = m -> n + n = m + m.

Proof.
   intros n m.
   intros H.
   rewrite <- H.
   reflexivity.
   Qed.

Theorem plus_id_excercise : forall m n o : nat, 
         n = m -> m = o -> n + m = m + o. 
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
  Qed.

Theorem mult_O_plus : forall n m : nat,
                        ( O + n ) * m = n * m.
Proof. 
 intros n m.
 rewrite -> plus_O_n.
 reflexivity. Qed.

Theorem mult_S_1 : forall m n : nat,
                     m = S n -> m * ( 1 + n ) = m * m.

Proof.
  intros n m.
  intros H. 
  rewrite -> plus_1_1.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_1_neg_O_firsttry : forall n : nat,
         beq_nat ( n + 1 ) O = false.

Proof.
  intros n.  
  destruct n as [| n'].
  reflexivity.
  reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
         negb ( negb b ) = b.

Proof.
  intros b.
  destruct b.
  simpl.
  reflexivity.
  simpl.  
  reflexivity. Qed.

Theorem zero_negb_plus_1 : forall n : nat,
        beq_nat O ( n + 1 ) = false.

Proof. 
  intros n.  
  destruct n as [ | n' ].
  simpl.
  reflexivity.
  simpl.
  reflexivity. Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  ( forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
 intros f.
 intros H. 
 intros b.
 rewrite -> H.
 rewrite -> H.
 reflexivity. Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  ( forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof. 
  intros f. 
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity. Qed.

Theorem andb_eq_orb : forall (b c : bool),
  ( andb b c = orb b c) ->
  b = c.

Proof. 
  intros b c.
  destruct b.
  simpl.
  