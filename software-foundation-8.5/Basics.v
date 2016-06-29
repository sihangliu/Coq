
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
