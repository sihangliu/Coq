Require Export Logic.

Definition even ( n : nat ) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
 | ev_O : ev O
 | ev_SS : forall n : nat,  ev n -> ev ( S ( S n ) ).

Theorem double_even : forall n ,
 ev ( double n ).
Proof.
  intros n. induction n as [ | n' ].
  Case "n = O".
    simpl. apply ev_O.
  Case "n = S n'".
    simpl. apply ev_SS. apply IHn'.
Qed.

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
 intros n H. induction H as [ | n' E' ].
 Case "n = O".
   unfold even. simpl. reflexivity.
 Case "n = S n'".
   unfold even.  simpl. apply IHE'.
Qed.

Theorem l : forall n,  
  ev  n.
Proof.
 intros n. induction n as [ | n' ].
 Case "n = O". apply ev_O.
 Case "n = S n'".
(* Now here  Case := "n = S n'" : String.string
  n' : nat
  IHn' : ev n'
  ============================
   ev (S n')
And this can't be proved because we have proof of ev n' and all we can prove 
that ev ( S ( S n ' ) ) is even but here goal is ev ( S n' ).
*)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n + m).
Proof.
 intros n m En. induction En as [ | n' En' ].
 Case "En = ev_O".
   intros Em. destruct Em as [ | m' Em' ].
   SCase "Em' = ev_O ".  simpl. apply ev_O.
   SCase "Em = ev_SS m' Em'". simpl. apply ev_SS. apply Em'.
 Case "En = ev_SS n' En'".
   intros Em. destruct Em as [ | m' Em' ].
   SCase "Em = ev_O". 
      simpl.  apply ev_SS. apply IHEn'. apply ev_O.
   SCase "Em = ev_SS m' Em'".
     simpl. apply ev_SS. apply IHEn'. apply ev_SS. apply Em'.

Inductive beautiful : nat -> Prop :=
 | b_O : beautiful 0
 | b_3 : beautiful 3
 | b_5 : beautiful 5
 | b_sum : forall n m : nat , beautiful n -> beautiful m -> beautiful ( n + m ).

Theorem three_is_beautiful: beautiful 3.
Proof.
  apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  apply b_sum with ( n := 3 ) (  m := 5 ).
  apply b_3.
  apply b_5.
Qed.

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
 intros n E.
 apply b_sum with ( n := 8 ) ( m := n ).
 apply eight_is_beautiful.
 apply E.
Qed.

Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
Proof.
 intros n E. simpl.
 apply b_sum with ( n := n ) ( m := ( n + 0 )).
 apply E. 
 apply b_sum with ( n := n ) ( m := 0).
 apply E. apply b_O.
Qed.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m * n).
Proof.
 intros n m E. induction m.
 Case "m = O".     
   apply b_O.
 Case "m = S m'".
   simpl. apply b_sum with ( n := n ) ( m := m * n ).
   apply E. apply IHm.
Qed.

Inductive gorgeous : nat -> Prop :=
 | g_0 : gorgeous 0
 | g_plus3 : forall n , gorgeous n -> gorgeous ( 3 + n )
 | g_plus5 : forall n , gorgeous n -> gorgeous ( 5 + n ).

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
 intros n E.
 apply g_plus5 with ( n := 8 + n ). apply g_plus3 with ( n := 5 + n ).
 apply g_plus5 with ( n := n ). apply E.
Qed.


