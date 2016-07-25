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
