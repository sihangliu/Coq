Require Export MoreLogic.

Check b_sum.
Theorem eight_is_beautiful : beautiful 8.
Proof.
  apply b_sum with ( n := 3 ) ( m := 5 ).
  apply b_3. apply b_5.
  Show Proof.
Qed.


Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Theorem n2beautiful : forall n, beautiful n -> beautiful ( 2 * n ).
Proof.
  intros n H.
  simpl. apply b_sum with ( n := n ) ( m := ( n + 0 ) ).
  assumption. SearchAbout ( _ + O = _ ).
  rewrite -> Plus.plus_0_r. assumption.
Qed.

Definition nine_is_beautiful' : beautiful 9 :=
  b_sum 3 6 b_3 ( b_sum 3 3 b_3 b_3 ).

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) :=
  fun ( n : nat ) => fun ( H : beautiful n ) => b_sum 3 n b_3 H.

Definition b_times2': forall n, beautiful n -> beautiful (2 * n) :=
  fun ( n : nat ) => fun ( H : beautiful n ) =>
                       b_times2 n H.


Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n) :=
  fun ( n : nat ) => fun ( H : gorgeous n ) =>
                       gorgeous_plus13 n H.

Print conj.
Theorem and_commutes : forall P Q, P /\ Q -> Q /\ P.
Proof.
  intros P Q H. inversion H as [ HP  HQ ].
  split. assumption. assumption.
Qed.

Print and_commutes.


Definition and_commutes' : forall P Q, P /\ Q -> Q /\ P :=
      fun ( P Q : Prop ) ( H : P /\ Q ) =>
        match H with
          | conj HP HQ => conj Q P HQ HP
        end.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun ( P Q R : Prop )
  => fun ( HPQ : P /\ Q ) => fun ( HQR : Q /\ R ) 
     =>
       match HPQ, HQR with
         | conj HP _, conj _ HR => conj P R HP HR
       end.

Theorem beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n.
Proof.
  intros n. split.
  apply beautiful__gorgeous.
  apply gorgeous__beautiful.
  Show Proof.
Qed.

Definition beautiful_iff_gorgeous' :
  forall n, beautiful n <-> gorgeous n :=
  fun ( n : nat ) =>
    conj ( beautiful n -> gorgeous n ) ( gorgeous n -> beautiful n )
         ( beautiful__gorgeous n ) ( gorgeous__beautiful n ). 

Theorem or_commute : forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q H. inversion H as [ HP | HQ ].
  right. assumption.
  left. assumption.
  Show Proof.
Qed.

Definition or_commute' : forall P Q, P \/ Q -> Q \/ P :=
  fun ( P Q : Prop ) ( H : P \/ Q ) =>
    match H with
      | or_introl HP => or_intror Q P HP
      | or_intror HQ => or_introl Q P HQ
    end.

Check ex.

Definition some_nat_is_even : Prop :=
  ex _ ev.

Check ev.
Check ex.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 ( ev_SS 2 ( ev_SS O ev_O )).

Theorem p : ex _ (fun n => beautiful (S n)).
Proof.
  exists 2. apply b_3.
  Show Proof.
Qed.
Definition p' : ex _ (fun n => beautiful (S n)) :=
  ex_intro nat ( fun n : nat => beautiful ( S n ) ) 2 b_3.

Check plus_comm.

Lemma plus_comm_r : forall a b c, c + ( b + a ) = c + ( a + b ).
Proof.
  intros a b c.
  rewrite plus_comm with ( m := c ) ( n := b + a ).
  rewrite plus_comm with ( m := c ).
  rewrite plus_comm with ( m := a ).
  reflexivity.
Qed.


Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2. inversion H1. inversion H2.
  reflexivity.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  Print trans_eq.
  intros a b c d e f H1 H2.
  apply trans_eq with ( m := [ c; d ] ). assumption.
  assumption.
Qed.

(* trans_eq = 
fun (X : Type) (n m o : X) (H1 : n = m) (H2 : m = o) =>
eq_ind_r (fun n0 : X => n0 = o) H2 H1
     : forall (X : Type) (n m o : X), n = m -> m = o -> n = o *)

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply ( trans_eq ( list nat )  [ a ; b ] [ c ; d ] [ e ; f ] H1 H2 ).
  Show Proof.
Qed.

Definition addOne : nat -> nat.
  intros n. Show Proof. apply S. Show Proof.
  apply n. Show Proof.
Defined.

