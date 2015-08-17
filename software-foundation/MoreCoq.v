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
  intros n m o p H1 H2. apply H2 with (q := n). assumption.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m H1 H2. apply H2 with (q := n). assumption.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2. apply H1 with (n := 3). assumption.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl.
Abort.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl. symmetry. assumption.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H. symmetry. rewrite H. apply rev_involutive.
Qed.


Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  rewrite H1. rewrite H2. reflexivity.
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
  apply trans_eq with (m := [c; d]).
  assumption. assumption.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2. rewrite H2. apply H1.
Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m H.
  inversion H. reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n m H.
  inversion H. reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j H1 H2. inversion H1. inversion H2. symmetry.
  assumption.
Qed.

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n H. inversion H.
Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m H. inversion H.
Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
                    x = y -> f x = f y.
Proof.
  intros A B f x y H.
  rewrite H. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  induction n.
  Case "n = O". simpl. intros H. reflexivity.
  Case "n = S n". simpl. intros H. inversion H.
Qed.
(* think of writing n = 0 from goal to hypothesis beq_nat 0 n = true *)

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  induction n.
  Case "n = O". simpl. intros H. reflexivity.
  Case "n = S n". simpl. intros H. inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  simpl. intros n m b H. assumption.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2. symmetry in H2. apply H1 in H2. symmetry.
  assumption.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  induction n.
  Case "n = O". simpl. intros m H. 
