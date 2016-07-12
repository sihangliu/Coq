Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] -> 
     [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  rewrite <- H1. apply H2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros. apply H0 with (q := n) (r := m).
  assumption.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros. apply H in H0.
  assumption.
Qed.

Theorem silly3 : forall (n : nat),
     true = Basics.beq_nat n 5 ->
     Basics.beq_nat (S (S n)) 7 = true.
Proof.
  intros. simpl. symmetry.
  assumption.
Qed.

Check rev_involutive.
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  symmetry. rewrite H. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite H1. assumption.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with (n := [a;b]) (m := [c;d]).
  assumption. assumption.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (n := n + p) (o := minustwo o) (m := m).
  assumption. assumption.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  inversion H. reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H. reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  inversion H as [H1].
  reflexivity.
Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros. inversion H. inversion H0.
  symmetry. assumption.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros A B f x y H.
  rewrite H. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
    Basics.beq_nat 0 n = true -> n = 0.
Proof.
  intros n H. destruct n.
  + auto.
  + simpl in H. inversion H.
Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n H. inversion H.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m H. inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     Basics.beq_nat (S n) (S m) = b ->
     Basics.beq_nat n m = b.
Proof.
  intros n m b H. simpl in H.
  assumption.
Qed.

Theorem silly3' : forall (n : nat),
  (Basics.beq_nat n 5 = true -> Basics.beq_nat (S (S n)) 7 = true) ->
  true = Basics.beq_nat n 5 ->
  true = Basics.beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2. symmetry in H2. apply H1 in H2.
  symmetry. assumption.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n.
  + intros m H. simpl in H. induction m.
    reflexivity.
    inversion  H.
  + intros m H. simpl in H. induction m.
    inversion H. simpl in H. inversion H.
    rewrite <- plus_n_Sm in H1. rewrite <- plus_n_Sm in H1.
    inversion H1.
    apply IHn in H2. rewrite H2. reflexivity.
Qed.

(* hell yeah. Finally solved in it one go :) *)


Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n.
  + simpl. intros m. induction m.
   {  auto. }
   {  simpl. intros H. inversion H. }
  + intros m. induction m.
    { simpl. intros H. inversion H. }
    { simpl. intros H. apply f_equal.
      inversion H. apply IHn. assumption.
    }
Qed.

Theorem beq_nat_true : forall n m,
    Basics.beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
  + intros m. induction m.
    { auto. }
    { intros H. simpl in H. discriminate. }
  + intros m. induction m.
    { intros H. simpl in H. discriminate. }
    { simpl. intros H. apply f_equal. apply IHn.
      assumption.
    }
Qed.

Theorem beq_id_true : forall x y,
    beq_id x y = true -> x = y.
Proof.
  intros x y. destruct x. destruct y.
  simpl. intros H. apply f_equal. apply beq_nat_true.
  assumption.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l. generalize dependent l. generalize dependent n.
  induction n.
  {
    destruct l.
    intros H. simpl. reflexivity.
    simpl. intros H. inversion H.
  }
  {
    destruct l.
    simpl. intros H; inversion H.
    simpl. intros H. apply IHn. inversion H. reflexivity.
  }
Qed.

Lemma app_length_commute : forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1. induction l1.
  simpl. intros l2. auto.
  simpl. intros l2. apply f_equal. apply IHl1.
Qed. 
  
Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l H. rewrite app_length_commute. rewrite H.
  reflexivity.
Qed.

Theorem app_length_twice' : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n. generalize dependent  l.
  induction l.
  intros n. simpl. intros H. rewrite <- H. auto.
  intros n H. destruct n. inversion H.
  simpl. apply f_equal.
  assert (H1 : forall (X : Type) (x : X) (l1 l2: list X),
             length (l1 ++ x :: l2) = S (length (l1 ++ l2))).
  {
    intros. induction l1.
    simpl. auto.
    simpl. apply f_equal. rewrite IHl1. reflexivity.
  }
  rewrite H1. rewrite <- plus_n_Sm. apply f_equal.
  apply IHl. inversion H. reflexivity.
Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros  P H1 H2 H3 H4. induction m.
  {
    induction n. apply H1. apply H3. assumption.
  }
  {
    induction n. apply H2. apply IHm. apply H4.
    apply IHm.
  }
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m. unfold square.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite mult_assoc. rewrite H. rewrite mult_assoc.
  auto.
Qed.

Definition foo (x: nat) := 5.
Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. simpl. reflexivity.
Qed.

Definition bar (x : nat) : nat :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.  simpl.
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. destruct m.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if Basics.beq_nat n 3 then true
  else if Basics.beq_nat n 5 then true
       else false.
