Require Import Omega.

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


