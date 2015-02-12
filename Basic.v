
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday ( d : day ) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval compute in ( next_weekday friday ).
Eval compute in ( next_weekday ( next_weekday friday )).

Example test_next_weekday :
( next_weekday ( next_weekday saturday )) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb ( b : bool ) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb ( x : bool ) ( y : bool ) : bool :=
  match x with
  | true => y
  | false => false
  end.

Definition orb ( x : bool ) ( y : bool ) : bool :=
  match x with
  | false => y
  | true => true
  end.


Example test_orb1 : ( orb true false ) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : ( orb false false ) = false.
Proof. simpl. reflexivity. Qed.

Definition nandb ( x : bool ) ( y : bool ) : bool :=
  match ( x, y ) with
  | ( true, true ) => false
  | ( _, _ ) => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 ( x : bool ) ( y : bool ) ( z : bool ) : bool :=
  match ( x, y, z ) with
  | ( true, true, true ) => true
  | ( _, _, _ ) => false
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
Check ( negb false ).
Check andb3.

Definition xorb ( x : bool ) ( y : bool ) : bool :=
  match x, y with
  | true, true => false
  | false, false => false
  | _, _  => true
  end.

Theorem xorb_equal : forall a : bool, xorb a a = false.
Proof.
intros a. destruct a as [ | ].
reflexivity. reflexivity.
Qed.


Theorem xorb_equalleft : forall a b : bool, xorb a b = false -> a = b.
Proof.
intros a b H. destruct a. destruct b.
reflexivity. discriminate.
destruct b. discriminate. reflexivity.
Qed.

(*
Theorem xorb_notequal : forall a b : bool, xorb a b = true -> a <> b.
Proof.
intros a b H.
destruct a. destruct b.
discriminate.
rewrite <- H.
*)

Module Playground1.
Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Definition pred ( n : nat ) : nat :=
  match n with
  | O => O
  | S m => m
  end.

End Playground1.

Definition minustwo ( n : nat ) : nat :=
  match n with
  | O => O
  | S O => O
  | S ( S m ) => m
  end.

Check (S (S (S (S O)))).
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

Definition oddb ( n : nat ) : bool :=
   negb ( evenb n ).

Example test_oddb1: (oddb ( S ( S (S O ) ) ) ) = true.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus ( n : nat ) ( m : nat ) : nat :=
  match n with
  | O => m
  | S n' => S ( plus n' m )
  end.

Eval compute in plus ( S O ) ( S ( S O ) ).

Example plus_test : ( plus 3 4 ) = 7.
Proof. simpl. reflexivity. Qed.

(*
Example plus_comm : forall m n p : nat, plus m ( plus n p ) = plus ( plus m n ) p.
Proof.
intros m n p.
destruct m as [ | ].
reflexivity.
simpl.
Admitted.
*) 

Fixpoint mult ( m n : nat ) : nat :=
  match m with
  | O => O
  | S m' => plus ( mult m' n ) n
  end.


Eval compute in mult 4 9.

Example test_mult : ( mult 3 3 ) = 9.
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

(*
Notation "x + y" := ( plus x y ) ( at level 50, left associativity) : nat_scope.
Notation "x - y" := ( minus x y ) ( at level 50, left associativity) : nat_scope.
Notation "x * y" := ( mult x y ) ( at level 40, left associativity) : nat_scope.
Notation "x ^ y" := ( exp x y ) ( at level 30, right associativity) : nat_scope.

Eval simpl in 2^2^3.
*)

Check ( 10 + 1 + 2 ).
Check (( 0 + 1 ) + 1 ).

Fixpoint beq_nat ( n m : nat ) : bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
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
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat ( n m : nat ) : bool :=
  andb ( ble_nat n m ) ( negb ( beq_nat n m ) ).

Example test_blt_nat1 : ( blt_nat 3 3 ) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2 : ( blt_nat 3 4 ) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat4: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat5: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, O + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof. intros. reflexivity. Qed.

Theorem mult_O_n : forall n : nat, O * n = O.
Proof. intros. reflexivity. Qed.

Theorem plus_id_example : forall m n : nat, m = n -> n + n = m + m.
Proof. intros n m. intros H. rewrite -> H.
reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H1 H2.
rewrite -> H1. rewrite -> H2.
reflexivity. Qed.

Theorem plus_id_exercise2 : forall n m o : nat,
    n = m -> n + o = m + o.
Proof. intros n m o. intros H. rewrite -> H. reflexivity. Qed.

Theorem mult_O_plus : forall m n : nat, ( O + n ) * m = n * m.
Proof. intros m n. rewrite -> plus_O_n. reflexivity. Qed.

(*

Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof. Admitted.

*)

Theorem mult_S_1 : forall m n : nat, m = S n -> m * ( 1 + n ) = m * m.
Proof. intros m n. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
Proof. intros n. destruct n as [ | n']. reflexivity.
reflexivity. Qed.

Theorem negb_involuted : forall b : bool, negb ( negb b ) = b.
Proof. intros b. destruct b. reflexivity.
reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 ( n + 1 ) = false.
Proof. intros n. destruct n as [ | n' ]. reflexivity.
reflexivity. Qed.


Theorem identity_fn_applied_twice : forall ( f : bool -> bool ),
          ( forall (x : bool), f x = x ) ->
          forall (b : bool), f ( f b ) = b.
Proof. intros f H b. rewrite -> H. rewrite -> H. reflexivity. Qed.

Theorem negation_fn_applied_twice : forall (f : bool -> bool),
          ( forall (x : bool), f x = negb x ) ->
          forall (b : bool), f (f b) = b.
Proof. intros f H b. rewrite -> H. rewrite -> H. destruct b.
reflexivity. reflexivity. Qed.

Theorem andb_eq_orb_rev : forall (b c : bool), b = c -> (andb b c = orb b c).
Proof. intros b c H. rewrite -> H. destruct c. reflexivity. reflexivity. Qed.


Theorem andb_eq_orb_rev1 : forall (b c : bool), b = c -> (orb b c = orb b c).
Proof. intros b c H. rewrite -> H. destruct c. reflexivity. reflexivity. Qed.

Theorem andb_eq_orb : forall ( a b : bool ), ( andb a b  = orb a b ) -> a = b.
Proof.
intros a b. destruct a as [ false | true ].
simpl. intros H1. rewrite -> H1. reflexivity.
simpl. intros H2. rewrite -> H2. reflexivity.
Qed.

Inductive bin : Type :=
  | O' : bin
  | Twice : bin -> bin
  | DPlusOne : bin -> bin.

Fixpoint inc ( b : bin ) : bin :=
  match b with
  | O' => DPlusOne O'
  | Twice b' => DPlusOne b'
  | DPlusOne b' => Twice ( inc b' )
  end.

Fixpoint bintonat ( b : bin ) : nat :=
  match b with
  | O' => O
  | Twice b' => plus ( bintonat b' ) ( bintonat b')
  | DPlusOne b' => plus 1 ( plus ( bintonat b' ) ( bintonat b') )
  end.

Eval compute in bintonat ( Twice ( DPlusOne ( DPlusOne O' ) )).

