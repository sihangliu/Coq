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
| cons_1 n1 n2 n3 : rem n1 n2 n3 -> rem (n1 + n2) n2 n3.  

Lemma rem_1 : rem 2 4 2. 
Proof.
  constructor 1. omega.
Qed.

Lemma rem_2 : rem 10 4 2.
Proof.  
  constructor 2 with (n1 := 6).
  simpl.  constructor 2 with (n1 := 2).
  constructor 1. omega.
Qed.

Lemma rem_3 : forall n : nat, n <> 0 -> rem n n 0.
Proof.
  intros. constructor 2 with (n1 := 0).
  constructor 1.  omega.
Qed.

Lemma rem_4 : forall n m p : nat, p <> 0 -> rem n m p -> rem (n + m) m p.
Proof.
  intros. apply (cons_1 n m p H0).
Qed.

Inductive gcd : nat -> nat -> nat -> Prop :=
|cons_a a b : a = b -> gcd a b b
|cons_b a b c : b > a -> gcd a (b - a) c -> gcd a b c  (* b > a *)
|cons_c a b c : a > b -> gcd (a - b) b c -> gcd a b c. (* a > b *)

Lemma gcd_0 : gcd 10 3 1.
Proof.
  constructor 3. omega. simpl.
  constructor 3. omega. simpl.
  constructor 3. omega. simpl.
  constructor 2. omega. simpl.
  constructor 2. omega. simpl.
  constructor 1. auto.
Qed.

Print gcd_0.

Lemma gcd_1 : forall n : nat, gcd n n n.
Proof.
  intros. constructor 1. auto.
Qed.



Inductive pow2n : nat -> nat -> Prop :=
| val_0 : pow2n 0 1
| val_n n m : pow2n n m -> pow2n (S n) (2 * m).


Lemma pow_0 : pow2n 3 8.
Proof.
  constructor 2 with (n := 2) (m := 4).
  constructor 2 with (n := 1) (m := 2).
  constructor 2 with (n := 0) (m := 1).
  constructor 1.
Qed.

SearchAbout (_ <=? _).
Print pow_0.

Inductive expo : nat -> nat -> nat -> Prop :=
| pval_0 n : expo n 0 1
| pval_1 n m p : expo n m p -> expo n (S m) (n * p).

Lemma expo_1 : expo 2 4 16.
Proof.
  constructor 2 with (n := 2) (m := 3) (p := 8).
  constructor 2 with (n := 2) (m := 2) (p := 4).
  constructor 2 with (n := 2) (m := 1) (p := 2).
  constructor 2 with (n := 2) (m := 0) (p := 1).
  constructor 1 with (n := 2).
Qed.

Print expo_1.

Lemma mod_add_back: forall n m : nat, m <> 0 -> ((n + m) mod m) = (n mod m).
Proof.
  intros. SearchAbout ((_ + _) mod _ = _ mod _).
  rewrite Nat.add_mod. SearchAbout (_ mod _ = 0).
  rewrite Nat.mod_same. rewrite plus_0_r.
  SearchAbout ((_ mod _) mod _). rewrite Nat.mod_mod.
  auto. auto. auto. auto.
Qed.

Print mod_add_back.

Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (div2 n')
  end.

Lemma nat_ind_alt : forall P : nat -> Prop,
  P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof.
  intros P H1 H2 H3. Check lt_wf_ind.
  induction n as  [[| [| n]] H4] using lt_wf_ind.
  auto. auto. auto.
Qed.

