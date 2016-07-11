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
  + intros m H. simpl in H.
