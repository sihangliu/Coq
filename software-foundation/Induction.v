Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c. destruct b.
  simpl. intros H. reflexivity.
  simpl. intros H. assumption.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b.
  simpl. intros H. assumption.
  simpl. intros H. inversion H.
Qed.

Theorem plus_0_r_firsttry : forall n:nat,
                              n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.


Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem minus_diag : forall n,
                       minus n n = 0.
Proof.
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof. 
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n.
  simpl. reflexivity.
  simpl. auto.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n.
  simpl. intros m. rewrite plus_0_r. reflexivity.
  simpl. intros m. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n. induction n.
  simpl. reflexivity.
  simpl. intros m p. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n.
  simpl. reflexivity.
  simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n). reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q. Check plus_comm.
  rewrite plus_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n). rewrite plus_comm. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite plus_comm.
  assert (H : n + p = p + n). rewrite plus_comm. reflexivity.
  rewrite H. rewrite plus_assoc. reflexivity.
Qed.

Lemma plusmult : forall m, S m = (1 + m).
Proof.
  induction m. rewrite plus_0_r. reflexivity.
  simpl. reflexivity.
Qed.

Lemma plusdist : forall n m, n * S m = n + n * m.
Proof.
 intros n. induction n.
 intros m. simpl. reflexivity.
 intros m. simpl. rewrite IHn. rewrite plus_assoc.
 rewrite plus_assoc.
 assert (H : m + n = n + m). rewrite plus_comm. reflexivity.
 rewrite H. reflexivity.
Qed. 

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m. induction m.
  simpl. intros n. rewrite mult_0_r. reflexivity.
  intros n. simpl. rewrite plusdist. rewrite IHm.
  reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  induction n.
  simpl. reflexivity.
  assert (H : evenb (S (S n)) = evenb n). simpl. reflexivity.
  rewrite H. rewrite IHn. rewrite negb_involutive. reflexivity.
Qed.
(* It's should be induction *)
Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n. induction n.
  simpl. reflexivity.
  simpl. assumption.
Qed.

(* Just simplification because first argument is zero *)
Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* destruct because patten matching on first *)
Theorem andb_false_r : forall b : bool,
                         andb b false = false.
Proof.
  destruct b.
  reflexivity. reflexivity.
Qed.

(* Induction *)
Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p.
  simpl. assumption.
  simpl. rewrite IHp. reflexivity.
Qed.

(* simpl *)
Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* destruct or simpl *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl. rewrite plus_0_r. reflexivity.
Qed.

(* destruct *)
Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  destruct b.
  intros c. simpl. destruct c.
  simpl. reflexivity. reflexivity.
  destruct c. reflexivity. reflexivity.
Qed.

(* Induction *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  induction n.
  simpl. reflexivity.
  intros m p. simpl. rewrite IHn. rewrite plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  induction n.
  intros m p. reflexivity.
  intros m p. simpl. rewrite IHn. rewrite  mult_plus_distr_r.
  reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
Abort.  

Theorem bin_to_nat_pres_incr :
  forall (b : bin), bin_to_nat (incr b) = S(bin_to_nat b).
Proof.
  intro b. induction b as [ | n' | n'].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite plus_n_O. rewrite plus_n_O.
  rewrite IHn'. rewrite plus_n_Sm. simpl.
  reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | O => Ob
    | S n' => incr (nat_to_bin n')
  end.

Eval compute in nat_to_bin 10.

Theorem identity_conv : forall (n : nat),
                          bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n.
  simpl. reflexivity.
  simpl. rewrite bin_to_nat_pres_incr.
  rewrite IHn. reflexivity.
Qed.

(*
(b) You might naturally think that we should also prove the opposite direction: 
that starting with a binary number, converting to a natural, and then back to 
binary yields the same number we started with. However, it is not true! 
Explain what the problem is. 

Because zero can be written in many different ways. 
zero = Ob, Db Ob, Db (Db Ob) and likewise so other numbers can have 
multiple representation. We have to work with structural induction on
structure of number.
*)


