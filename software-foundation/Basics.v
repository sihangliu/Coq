
Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day .

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

Eval compute in next_weekday friday.
Eval compute in next_weekday (next_weekday saturday).

Example test_next_weekday :
  next_weekday (next_weekday saturday) = tuesday.
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

Definition andb (a b : bool) : bool :=
  match a with
    | true   => b
    |  false => false
  end.

Definition orb (a b : bool) : bool :=
  match a with
    | true => true
    | false  => b
  end.


Definition xorb (a b : bool) : bool :=
  match a, b with
    | true, true => false
    | false, false => false
    |_, _ => true
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.
Example test_xor: xorb true true = false.
Proof. reflexivity. Qed.

Definition nandb (a b : bool) : bool :=
  match a, b with
    | true, true => false
    | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. auto. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. auto. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. auto. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. auto. Qed.

Definition andb3 (a b c : bool) : bool :=
  andb (andb a b) c.

Example test_andb31: (andb3 true true true) = true.
Proof. auto. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. auto. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. auto. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. auto. Qed.

Check true.
Check (negb true).
Check negb.

Module Playground1.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb: oddb 10 = false.
Proof. auto. Qed.
Example test_evenb: evenb 10 = true.
Proof. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (a b : nat) : nat :=
    match a with
      | O => b
      | S n' => S (plus n' b)
    end.

  Eval compute in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | _, O => n
      | S n', S m' => minus n' m'
    end.
  Eval compute in minus 7 8.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => base
    | S n' => mult base (exp base n')
  end.

Fixpoint fact (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => fact n' * n
  end.

Example fact_five: fact 4 = 24.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x × y" := (mult x y) 
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

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


Eval compute in beq_nat 4 5.
Eval compute in beq_nat 5 4.
Eval compute in beq_nat 5 5.

Fixpoint ble_nat ( n m : nat ) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => ble_nat n' m'
            end
  end.


Eval compute in ble_nat 4 5.
Eval compute in ble_nat 5 4.
Eval compute in ble_nat 5 5.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (negb (beq_nat n m)) (ble_nat n m).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_n_O : forall n : nat, n + O = n.
Proof.
  intros n.
  induction n.

  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 × n = 0.
Proof.
  intros n. reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
                        (0 + n) × m = n × m.
Proof.
  intros n m. eapply plus_O_n.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite H.
  simpl. reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  induction n as [  | n' ].

  reflexivity.

  simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  induction b.

  reflexivity.

  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  induction n.

  reflexivity.

  reflexivity.
Qed.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite H. rewrite H.
  reflexivity.
Qed.

Lemma andb_true: forall b, andb true b = b.
Proof.
  induction b.

  reflexivity.

  reflexivity.
Qed.

Lemma orb_true : forall b, orb true b = true.
Proof.
   induction b.

   reflexivity.

   reflexivity.
Qed.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
   intros b c.  
   induction b.

   simpl.
   intros H.
   rewrite H; reflexivity.

   simpl. intros H. assumption.
Qed.


Inductive bin :=
| Ob : bin (* zero *)
| Db : bin -> bin (* double *)
| Tb : bin -> bin. (*double + one *)
 
(*
zero = Ob
one = Tb Ob
two = Db Tb Ob
three = Tb Tb Ob 
four = Db Db Tb Ob
five = Tb Db Tb Ob
six = Db three 
seven = Tb three 
 *)

Fixpoint incr (b : bin) : bin :=
  match b with
    | Ob => Tb Ob
    | Db n' => Tb n'
    | Tb n' => Db (incr n')
  end.

Eval compute in incr (Db (Tb Ob)).

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | Ob => O
    | Db n' => 2 * bin_to_nat n'
    | Tb n' => S (2 * bin_to_nat n')
  end.

Eval compute in bin_to_nat (Tb (Tb Ob)).



