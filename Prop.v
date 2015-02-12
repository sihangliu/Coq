Require Export Logic.

Definition even n : Prop :=
  evenb n = true.
Eval compute in even 4.

Inductive ev : nat ->  Prop :=
 | ev_O : ev 0
 | ev_SS : forall n,  ev n -> ev ( S ( S n ) ).
Print ev_ind.

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
And this can't be proved because we don't have proof of ev n' and all we can prove 
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
      simpl.  apply ev_SS. apply IHEn'.  apply ev_O.
   SCase "Em = ev_SS m' Em'".
     simpl. apply ev_SS. apply IHEn'. apply ev_SS. apply Em'.
Qed.

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

Theorem b_timesm' : forall n m , beautiful n -> beautiful ( m * n ).
Proof.
  intros n m E. induction E as [ | | | m' n' Em En ].
  Case "b_0". SearchAbout (_ * _ ).
    rewrite -> Mult.mult_0_r. apply b_O.
  Case "b_3".
Abort.    

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
  gorgeous n -> gorgeous (13 + n ).
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
 intros n E. induction E as [ | | | d ].
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
 Case "E = ev_SS". Print ev.
   simpl. apply E'.
Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
 intros n E. inversion E as [ | n' E' ].
 apply E'.
Qed.

Print ev.


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

Theorem  addzero : forall n m , m + n = 0 -> m = 0 /\ n = 0. 
Proof.
  intros n m H. generalize dependent m. induction m as [ | m'].
  Case "m = O". simpl. intros H. split.
   SCase "left". reflexivity.
   SCase "right". apply H.
  Case "m = S m'". simpl. intros H. inversion H.
Qed.   




Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E1 E2. 
  inversion E1.
  induction E1 as [ | n' En' ].
  Show Proof.
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
   simpl. rewrite -> snoc_list.  rewrite <- list_assoc.
   apply consC with ( a := v' ) ( l := l' ++ rev l' ).
   apply IHl'.
Qed.

Theorem rev_list : forall ( X : Type ) ( a : X ) ( l : list X ),
  rev ( l ++ [a] ) = a :: rev l.
Proof.
  intros X a l. induction l as [ | v' l'].
  Case "l = nil".
     reflexivity.
  Case "l = Cons v' l'".
    simpl. rewrite -> snoc_list. rewrite -> snoc_list.
    rewrite IHl'. simpl. reflexivity.
Qed.

Theorem palrev : forall ( X : Type ) ( l : list X ) , 
   pal l -> l = rev l.
Proof.
  intros X l E. induction E.
  Case "emptyC".
     reflexivity.
  Case "oneC".
     simpl. reflexivity.
  Case "consC".
     simpl. rewrite -> snoc_list. rewrite -> rev_list.
     simpl. rewrite <- IHE. reflexivity.
Qed.   

Theorem revpal : forall ( X : Type ) ( l : list X ) , 
  l = rev l -> pal l.
Proof.
 intros X l. induction l as [ | v' l'].
 Case "l = nil".
    intros H. apply emptyC.
 Case "l = Cons v' l'". 
    simpl. rewrite -> snoc_list.  intros H. 
Abort.   
   


Inductive R : nat -> list nat -> Prop :=
 | c1 : R 0 []
 | c2 : forall n l, R n l -> R ( S n ) (  n :: l )
 | c3 : forall n l, R ( S n ) l -> R n l.

Theorem a : R 2 [ 1 ; 0].
Proof.
 apply c2. apply c2. apply c1.
Qed.

Theorem b :  R 1 [1 ; 2 ;1 ; 0 ].
Proof.
(* This can't be proved *)
Abort.

Theorem c :  R 6 [3; 2; 1 ;0] .
Proof.
(* Not able to prove this one also *)
Abort.

(* 
a two-argument proposition can be thought of as a relation
*)

Inductive le : nat -> nat -> Prop := 
 | le_n : forall n, le n n
 | le_S : forall n m , le n m -> le n ( S m ).

Notation "m <= n" := ( le m n ).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
 apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
 intros H. simpl. inversion H. inversion H2.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
 | sq : forall n , square_of n ( n * n ).
 
Inductive next_nat ( n : nat ) : nat -> Prop :=
 | nn :  next_nat n ( S n ).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
 intros m n o R1 R2. generalize dependent m.
 induction R2. 
 intros m H. apply H.
 intros m0 H. apply IHR2 in H. apply le_S. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [ | n'].
  Case "n = O". apply le_n.
  Case "n = S n'". apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
 intros n m H. induction H.
 apply le_n. apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m ,
       S n <= S m -> n <= m.
Proof.
  intros n m. generalize dependent n.
  induction m as [ | m' ].
  Case "m = O". intros n H.
    inversion H.
    SCase "le_O". apply le_n.
    SCase "le_S". inversion H2.
  Case "m = S m'". intros n H.
    inversion H.
    SCase "le_O". rewrite <- H2. apply le_n.
    SCase "le_S". apply le_S. apply IHm'.
      apply H2.
Qed.


  
SearchAbout ( _ <= _ ).  
Theorem le_plus_l : forall a b,
                      a <= a + b.
Proof.
  intros a b. generalize dependent  a.
  induction b.   
  Case "b = O".  intros a. SearchAbout ( _ + 0 = _ ).
   rewrite -> plus_0_r_firsttry. apply le_n.
  Case "b = S b'". intros a. inversion a.
  SearchAbout ( _ + S _ ). rewrite <- Induction.plus_n_Sm.
  apply le_S. apply IHb. rewrite <- Induction.plus_n_Sm.
  apply le_S. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
                    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt. intros n1 n2 m H. generalize dependent n1.
  generalize dependent n2.
  induction m.
  Case "m = O".
  intros n1 n2 H. inversion H.
  Case "m = S m'".
  intros n1 n2 H. apply le_S.



Theorem lt_S : forall n m,
                 n < m -> n < S m.
Proof.
  unfold lt. intros n m H. apply le_S. apply H.
Qed.


Theorem ble_nat_true : forall n m,
                         ble_nat n m = true -> n <= m.
Proof.
  intros n. induction n.
  Case "n = O".
    intros m. destruct m.
    SCase "m = O". simpl. intros H. apply le_n.
    SCase "m = S m'". simpl. intros H. apply le_S.
Abort.     

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros n m.  generalize dependent n. induction m as [ | m'].
  Case "m = O".
  intros n H. inversion H. simpl. reflexivity.
  Case "m = S m'". intros n H.
  inversion H. simpl. rewrite <- ble_nat_refl. reflexivity.
Abort.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros n m o H1 H2.
  (* prove that ble_nat n m = true -> n <= m and then prove this *)
Abort.

(* I am missing something fundamental about relations! *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~ (n <= m).
Proof.
  intros n m H. unfold not.
Abort.

Abort All.
Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Theorem rone :  R 1 1 2 .
Proof.
  apply c2. apply c3. apply c1.
Qed.

Theorem rtwo : R 2 2 6.
Proof.
  apply c2. apply c2. apply c5. apply c2. apply c2.
Abort.

End R.

Theorem plus_2_2_4 :
  2 + 2 = 4.
Proof.
  simpl. reflexivity.
Qed.

Definition plus_fact : Prop :=
  2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof.
  reflexivity.
Qed.

Definition between ( n m o : nat ) : Prop :=
  andb ( ble_nat n o ) ( ble_nat o m ) = true.

Definition teen : nat -> Prop :=
  between 13 19.

Theorem teen_15 : teen 15.
Proof.
  unfold teen. compute.
  reflexivity.
Qed.

Definition true_for_zero (P : nat -> Prop ) : Prop :=
  P 0.

Definition true_for_all_numbers ( P : nat -> Prop ) : Prop :=
  forall n, P n.

Definition preserved_by_S ( P : nat -> Prop ) : Prop :=
  forall n, P n -> P ( S n ).

Definition natural_number_induction_valid : Prop :=
  forall ( P : nat -> Prop ),
    true_for_zero P -> preserved_by_S P ->
    true_for_all_numbers P.
(*
Definition combine_odd_even ( Podd Peven : nat -> Prop) : nat -> Prop :=
  forall n, if oddb n then Podd else Peven.

Learn more about relation and try to solve it later
*)