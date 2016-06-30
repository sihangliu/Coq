
Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday monday).    
Compute (next_weekday (next_weekday saturday)).    

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl. reflexivity.
Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b c : bool) : bool :=
  match b with
    | false => false
    | true => c
  end.


Definition orb (b c : bool) : bool :=
  match b with
    | false => c
    | true => true
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b c : bool) : bool :=
  match b, c with
    | true, true => false
    | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_nandb3: (nandb false true) = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_nandb4: (nandb true true) = false.
Proof.
  simpl. reflexivity.
Qed.

Definition andb3 (b c d : bool) : bool :=
  andb b (andb c d).

Example test_andb31: (andb3 true true true) = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_andb32: (andb3 false true true) = false.
Proof.
  simpl. reflexivity.
Qed.
Example test_andb33: (andb3 true false true) = false.
Proof.
  simpl. reflexivity.
Qed.
Example test_andb34: (andb3 true true false) = false.
Proof.
  simpl. reflexivity.
Qed.

Check true.
Check bool.
Check Set.
Check negb.

Module Playground1.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n => n
    end.
  
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check S (S (S (S O))).
Check (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Inductive evennumber : nat -> Prop :=
| evenO : evennumber O
| evenS : forall n, evennumber n -> evennumber (S (S n)).


Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.

  Compute (plus 2 3).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S O => m
      | S n' => plus m (mult n' m)
    end.

  Compute (mult 4 4).      

  Example test_mult1: (mult 3 3) = 9.
  Proof.
    simpl. reflexivity.
  Qed.
  
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => 1
    | S n' => mult base (exp base n')
  end.

Compute (exp 2 10).    

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Compute (factorial 5).

Example test_factorial1: (factorial 3) = 6.
Proof.
  simpl. reflexivity.
Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
  simpl. reflexivity.
Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
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

Compute (beq_nat 10 10).

Fixpoint leb (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
  end.


Compute (leb 2 3).
Compute (leb 3 2).    

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  negb (leb m n).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof.
  compute. reflexivity.
Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof.
  compute. reflexivity.
Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof.
  compute. reflexivity.
Qed.

Theorem plus_O_n : forall (n : nat), O + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* These are all things that can be applied to a number to yield a number. However, 
there is a fundamental difference between the first one and the other two: functions 
like pred and minustwo come with computation rules — e.g., the definition of pred 
says that pred 2 can be simplified to 1 — while the definition of S has no such behavior 
attached. Although it is like a function in the sense that it can be applied to an 
argument, it does not do anything at all! *)

Theorem plus_1_l : forall (n : nat), 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_0_n : forall (n : nat), O * n = O.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem plus_n_O : forall (n : nat), n + O = n.
Proof.
  intros n. simpl.
Abort.

Theorem plus_id_example : forall (n m : nat),
    n = m -> n + n = m + m.
Proof.
  intros n m H. rewrite -> H. reflexivity.
Qed.

Theorem plus_id_exercise : forall (n m o : nat),
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1. rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall (n m : nat),
    (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n. reflexivity.
Qed.

Theorem mult_S_1 : forall (n m : nat),
    m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite plus_1_l. rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall (n : nat),
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. simpl.
Abort.

Theorem plus_1_neq_0 : forall (n : nat),
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [ | n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall (b : bool),
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall (b c : bool),
    andb b c = andb c b.
Proof.
  intros b. destruct b.
  - intros c. destruct c.
    + reflexivity.
    + reflexivity.
  - intros c. destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall (b c : bool),
    andb b c = andb c b.
Proof.
  intros b. destruct b.
  {
    intros c. destruct c.
    { reflexivity. }
    { reflexivity. }
  }
  {
    intros c. destruct c.
    { reflexivity. }
    { reflexivity. }
  }
Qed.

Theorem andb3_exchange : forall (b c d : bool),
    andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b. destruct b.
  {
    intros c. destruct c.
    {
      intros d. destruct d.
      + reflexivity.
      + reflexivity.
    }
    {
      intros d. destruct d.
      + reflexivity.
      + reflexivity.
  }}
  {
    intros c. destruct c.
    {
      intros d. destruct d.
      + reflexivity.
      + reflexivity.
    }
    {
      intros d. destruct d.
      + reflexivity.
      + reflexivity.
    }}
Qed.

Theorem plus_1_neg_0' : forall (n : nat),
    beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative'' : forall (b c : bool),
    andb b c = andb c b.
Proof.
  intros [] [].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Theorem andb_true_elim2 : forall (b c : bool),
    andb b c = true -> c = true.
Proof.
  intros [] [].
  + auto.
  + auto.
  + auto.
  + auto.
Qed.

Theorem andb_true_elim3 : forall (b c : bool),
    andb b c = true -> b = true /\ c = true.
Proof.
  intros [] [].
  + auto.
  + auto.
  + auto.
  + auto.
Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                    : nat_scope.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = x) ->
                 forall (b : bool), f (f b) = b.
Proof.
  intros f H b. rewrite H. apply H with ( x := b).
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) ->
                 forall (b : bool), f (f b) = b.
Proof.
  intros f H b. rewrite H. rewrite H.
  rewrite negb_involutive. reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros [] [].
  + auto.
  + auto.
  + auto.
  + auto.
Qed.

Inductive bin :=
| Zero : bin
| D : bin -> bin (* 2 * n *)
| T : bin -> bin. (* 2 * n + 1 *) 

Check Zero. (* 0 *)
Check T Zero. (* 1 *)
Check D (T Zero). (* 2 *)
Check T (T Zero). (* 3 *)
Check D (D (T Zero)). (* 4 *)
Check T (D (T Zero)). (* 5 *)
Check D (T (T Zero)). (* 6 *)

Fixpoint incr (b : bin) : bin :=
  match b with
  | Zero => T Zero
  | D n => T n
  | T n => D (incr n)
  end.

Compute (incr Zero).
Compute (incr (incr Zero)).
Compute (incr (incr (incr Zero))).
Compute (incr (incr (incr (incr Zero)))).
Compute (incr (incr (incr (incr (incr Zero))))).
Compute (incr (incr (incr (incr (incr (incr Zero)))))).
Compute (incr (incr (incr (incr (incr (incr (incr Zero))))))).

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Zero => O
  | D n => let v := bin_to_nat n in plus v v
  | T n => let v := bin_to_nat n in plus 1 (plus v v)
  end.                     

Compute (bin_to_nat (D (T (T Zero)))).
Compute (bin_to_nat (D (T Zero))).  

Theorem bin_correctness :
  forall (b : bin), plus 1 (bin_to_nat b) = bin_to_nat (incr b).  
Proof.
  intros b. induction b.
  + auto.
  + auto.
  + simpl. rewrite <- IHb. Require Import Omega.
    omega.
Qed.

