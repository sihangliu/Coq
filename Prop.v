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


Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
 intros n H. induction H as [ a | b | c ].
 Case "g_0". apply b_O.
 Case "g_plus3". apply b_sum with ( n := 3 ) ( m := b ).
         apply b_3. apply IHgorgeous.
 Case "g_plus5". apply b_sum with ( n := 5 ) ( m := c ).
         apply b_5. apply IHgorgeous.
Qed.

Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
 intros n H. induction n as [ | n'].
 Case "n = O".
  apply b_O.
 Case "n = S n'".
Abort.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 intros n m E1 E2. induction E1 as [ | b | c ].
 Case "g_0".
    simpl. apply E2.
 Case "g_plus3".
    apply g_plus3 with ( n := b + m ). apply IHE1.
 Case "g_plus5".
     apply g_plus5 with ( n := c + m ). apply IHE1.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 intros n E. induction E as [ a | b | c | d ].
 Case "a = b_O". apply g_0.
 Case "b = b_3". apply g_plus3. apply g_0.
 Case "c = b_5". apply g_plus5. apply g_0.
 Case "d = b_sum". apply gorgeous_sum with ( n := d ) ( m := m ).
     SCase "n = d". apply IHE1.
     SCase "m = m". apply IHE2.
Qed.

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z. induction x. 
  Case "x = O".
    simpl. rewrite -> plus_0_r_firsttry. reflexivity.
  Case "x = S x'".
   assert ( H : z + S x = S x + z ).
       apply plus_comm. 
   rewrite -> H. simpl. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n E. simpl. induction E as [ | b | c ].
   Case "g_0". simpl. apply g_0.
   Case "g_plus3".
       rewrite -> plus_0_r_firsttry. rewrite plus_0_r_firsttry in IHE.
       apply g_plus3 with ( n := b + ( 3 + b ) ). rewrite -> plus_comm.
       apply g_plus3 with ( n := b + b ). apply IHE.
   Case "g_plus5".
       rewrite plus_0_r_firsttry. rewrite plus_0_r_firsttry in IHE.
       apply g_plus5 with ( n := c + ( 5 + c ) ). rewrite -> plus_comm.
       apply g_plus5 with ( n := c + c ). apply IHE.
Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. induction E.
  Case "E = ev_O".
   simpl. apply ev_O.
  Case "E = ev_SS".
   simpl. apply E.
Qed.

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)).
Proof.
 intros n E. inversion E as [ | n' E'].
 Case "E = ev_O".
   simpl. rewrite H. apply E.
 Case "E = ev_SS".
   simpl. apply E'.
Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
 intros n E. inversion E as [ | n' E' ].
 apply E'.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
 intros n E. inversion E as [ | n' E'].
 apply SSev__even in E'. apply E'.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof. 
 intros H. inversion H. inversion H1. inversion H3.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
 intros n m E1 E2. generalize dependent E1. induction  E2.
 Case "ev_O".  simpl.  intros E. apply E.
 Case "ev_SS".
     simpl. intros H. apply IHE2. inversion H. apply H1.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
 intros n m p E1 E2. 
Abort.

Inductive pal { X : Type } : list X -> Prop :=
 | emptyC : pal nil
 | oneC : forall ( a : X ) , pal ( a :: nil )
 | consC : forall ( a : X ) ( l : list X ) , pal l -> pal ( a :: l ++ [a]).




Theorem reverseonlist : forall { X : Type } ( l : list X ), pal ( l ++ rev l). 
Proof.
 intros X l. induction l as [ | v' l'].
 Case "l = nil".
   simpl. apply emptyC.
 Case "l = Cons v' l'".
   simpl. rewrite -> snoc_list. rewrite <- list_assoc.
   apply consC with ( a := v' ) ( l := l' ++ rev l' ).
   apply IHl'.
Qed.


Theorem revpal : forall ( X : Type ) ( l : list X ) , 
  l = rev l -> pal l.
Proof.
 intros X l H. 