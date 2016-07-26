Require Import Omega.
Require Import Coq.Program.Wf.

Definition minus_decrease :
  forall x y : nat, Acc lt x -> x <> 0 -> y <> 0 -> Acc lt (x - y).
Proof.
  intros x y H Hx Hy.
  destruct H; apply H; omega.
Defined.

Print minus_decrease.

Fixpoint div_aux (x y : nat) (H : Acc lt x) {struct H} : nat.
Proof.
  intros.
  refine (if eq_nat_dec x 0 then 0
          else if eq_nat_dec y 0 then y
               else S (div_aux (x - y) y _)).
  apply (minus_decrease x y H n n0).
Qed.

Definition div x y := div_aux x y (lt_wf x).
Print lt_wf.

Program Fixpoint div_aux' (x y : nat) (H : y <> 0) {measure  x} : nat :=
  if eq_nat_dec x 0 then 0
  else S (div_aux' (x - y) y _).
Next Obligation.
  omega.
Qed.

Lemma not30 : 3 <> 0.
Proof.
  omega.
Qed.

Compute (div_aux' 6 3 not30).
Print div_aux'.
Compute (leb 2 4).

(*
Definition mod'' (x y : nat) (H : y <> 0) : {z : nat * nat | x = y * (fst z) + (snd z)} .
Proof.
  exists (div x y, mod x y).
 *)



Program Fixpoint remainder (x y : nat) (H : y <> 0) {measure x} : nat :=
  match (leb x y) with
  | false => remainder (x - y) y H
  | _ => x
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  SearchAbout (_ <=? _).
  apply leb_iff_conv in Heq_anonymous.
  omega.
Qed.

Compute  (remainder 10 3 not30).

Inductive rem : nat -> nat -> nat -> Prop :=
| cons_0 n1 n2 : n1 < n2 -> rem n1 n2 n1
| cons_1 n1 n2 n3 : n1 >= n2 -> rem (n1 - n2) n2 n3 -> rem n1 n2 n3.  

Lemma rem_1 : rem 2 4 2. 
Proof.
  constructor 1. omega.
Qed.

Lemma rem_2 : rem 10 4 2.
Proof.  
  constructor 2. omega.
  simpl.  constructor 2. omega.
  simpl. constructor 1. omega.
Qed.

Lemma rem_3 : forall n : nat, n <> 0 -> rem n n 0.
Proof.
  intros. constructor 2. omega.
  assert (H1 : n - n = 0) by omega.
  rewrite H1. constructor 1.  omega.
Qed.

Lemma rem_4 : forall n m p : nat, p <> 0 -> rem n m p -> rem (n + m) m p.
Proof.
  constructor 2. omega.
  assert (H1 : n + m - m = n) by omega.
  rewrite H1. trivial.
Qed.

Inductive gcd : nat -> nat -> nat -> Prop :=
|cons_a a b : a = 0 -> gcd a b b
|cons_b a b c : b > a -> gcd b a c -> gcd a b c
|cons_c a b c : a >= b -> gcd (a - b) b c -> gcd a b c. 

Lemma gcd_0 : gcd 10 3 1.
Proof.
  constructor 3. omega. constructor 3. omega. simpl.
  constructor 3. omega. simpl. constructor 2. omega.
  constructor 3. omega. simpl. constructor 3. omega.
  simpl. constructor 3. omega. simpl. constructor 1.
  reflexivity.
Qed.

Print gcd_0.

Lemma gcd_1 : forall n : nat, gcd n n n.
Proof.
  intros. constructor 3. omega. assert (H : n - n = 0 ) by omega.
  rewrite H. constructor 1. reflexivity.
Qed.



  Program Fixpoint gcd (x y : nat) (H : y <= x) : nat :=
  
