Require Export MoreLogic.

Print beautiful.
Check b_sum.

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n := 3) (m := 5).
    apply b_3.
    apply b_5.
Qed.

Check eight_is_beautiful.
Print eight_is_beautiful.

Check (b_sum 3 5 b_3 b_5).

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply (b_sum 3 3 b_3 b_3).
Qed.

Definition six_is_beautiful' : beautiful 6 := b_sum 3 3 b_3 b_3.

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  apply (b_sum 3 6 b_3 (b_sum 3 3 b_3 b_3)).
Qed.

Definition nine_is_beautiful' : beautiful 9 := b_sum 3 6 b_3 (b_sum 3 3 b_3 b_3).

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

Definition b_plus3' : forall n, beautiful n -> beautiful (3 + n) :=
  fun (n : nat) => fun (H : beautiful n) => b_sum 3 n b_3 H.

Check b_plus3'.

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3 + n) :=
  b_sum 3 n b_3 H.

Definition beautiful_plus3 : Prop :=
  forall n, forall (E : beautiful n), beautiful (n+3).

Definition beautiful_plus3' : Prop :=
  forall n, forall (_ : beautiful n), beautiful (n+3).

Definition beatiful_plus3'' : Prop :=
  forall n, beautiful n ->  beautiful (n+3).

(* In general, "P → Q" is just syntactic sugar for "∀ (_:P), Q". *)


Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n) :=
  fun (n : nat) => fun (H : gorgeous n) => g_5 (8 + n) (g_5 (3 + n) (g_3 n H)).

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  apply b_0. apply b_3.
Qed.

Print conj.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H. Show Proof.
  apply conj. inversion H.
  Show Proof. assumption. inversion H. assumption.
  Show Proof.
Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) =>
    match H1, H2 with
      | conj HP _, conj _ HR => conj P R HP HR
    end.

      
