Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
 intros m n o p H1 H2.
 rewrite <- H1. apply H2.
Qed.

Theorem silly2 : forall ( n m o p : nat ) , 
    n = m -> ( forall ( q r : nat ) , q = r -> [ q ; o ] = [ r ; p ] ) ->
    [ n ; o ] = [ m ; p ].
Proof.
 intros n m o p H1 H2. 
 apply H2. apply H1.
Qed.
(* Not able to write this proof using rewrite. I stuck with second hypothesis
forall ( q r : nat ) , q = r -> [ q ; o ] = [ r ; p ] *)

Theorem silly2a : forall ( n m : nat ) , 
 (n, n ) = ( m, m ) -> 
 ( forall ( q r : nat ), ( q, q ) = ( r, r ) -> [ q ] = [ r] ) ->
 [ n ] = [ m ].
Proof.
 intros n m H1 H2.
 apply H2. apply H1.
Qed.

Theorem silly_ex : 
  ( forall n, evenb n = true -> oddb ( S n ) = true ) ->
  evenb 3 = true -> oddb 4 = true.
Proof.
 intros H1 H2. apply H1. apply H2.
Qed.

Theorem silly3_firsttry : forall ( n : nat ), 
 true = beq_nat n 5 -> 
 beq_nat ( S ( S n ) ) 7 = true.
Proof.
 intros n H. simpl.
Abort.

Theorem silly3 : forall ( n : nat ), 
 true = beq_nat n 5 -> 
 beq_nat ( S ( S n ) ) 7 = true.
Proof.
 intros n H. symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall ( l l' : list nat ), 
  l = rev l' -> 
  l' = rev l.
Proof.
 intros l l' H. symmetry. rewrite -> H. 
 SearchAbout ( rev ( rev _ ) = _ ).
 apply rev_involutive.
Qed.

Example trans_eq_example : forall ( a b c d e f : nat ), 
 [ a ; b ] = [ c ; d ] -> 
 [ c ; d ] = [ e ; f ] -> 
 [ a ; b ] = [ e ; f ].
Proof.
 intros a b c e d f H1 H2.
 rewrite -> H1. apply H2.
Qed.

Theorem trans_eq : forall ( X : Type ) ( n m o : X ) , 
 n = m -> m = o -> n = o.
Proof.
 intros X n m o H1 H2.
 rewrite -> H1. apply H2.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
 intros a b c d e f H1 H2.
 apply trans_eq with ( m := [ c ; d ]). apply H1.  apply H2.
Qed.

Example trans_eq_exercise : forall ( n m o p : nat ) , 
 m = ( minustwo o ) -> 
 ( n + p ) = m -> 
 ( n + p ) = (minustwo o).
Proof.
 intros n m o p H1 H2.
 apply trans_eq with ( m := m ). apply H2. apply H1.
Qed.


Theorem eq_add_S : forall ( n m : nat ) ,
  S n = S m -> n = m.
Proof.
 intros n m H. inversion H. reflexivity.
Qed.

(* See inversion is propogating the things into goal also *)

Theorem silly4 : forall ( n m : nat ) , 
 [ n ] = [ m ] ->
 n = m.
Proof.
 intros n m H. inversion H. reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
 intros n m o H. inversion H.
 reflexivity.
Qed.

Example sillyex1 : forall (  X : Type ) ( x y z : X ) ( l j : list X ) ,
 x :: y :: l = z :: j  ->
 y :: l  = x :: j -> 
 x = y .
Proof.
 intros X x y z l j H1 H2. inversion H2. reflexivity.
Qed.

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
 intros n H. inversion H.
Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
 intros n m H. inversion H.
Qed.

Example sillyex2 : forall ( X : Type ) ( x y z : X ) ( l j : list X ), 
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
 intros X x y z l j H1 H2. inversion H1.
Qed.

Theorem f_equal : forall ( A B : Type ) ( f : A -> B )  ( x y : A ),  
  x = y -> f x = f y. 
Proof. 
  intros A B f x y H. rewrite -> H.  reflexivity.
Qed.

Theorem beq_nat_0_1 : forall n , 
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n H. destruct n as [ | n' ].
  Case "n = O".
   reflexivity.
  Case "n = S n'".
   inversion H.
Qed.


Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
 intros n H. destruct n as [ | n' ].
 Case "n = O".
  reflexivity.
 Case "n = S n'".
  inversion H.
Qed.

Theorem S_inj : forall ( n m : nat ) ( b : bool ) , 
 beq_nat ( S n ) ( S m ) = b ->
 beq_nat n m = b.
Proof.
 intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
 intros n H1 H2. symmetry in H2. apply H1 in H2. symmetry. apply H2.
Qed.

Theorem plus_n_Sm : forall ( n m : nat ),
   n + S m = S ( n + m ).
Proof.
  intros n m. induction n as [ | n' ].
  Case "n = O".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
 intros n. induction n as [ | n'].
 Case "n = O".
   intros m H. induction  m as [ | m'].
   SCase "m = O".
      reflexivity.
   SCase "m = S m'".
      inversion H.
 Case "n = S n'".
    intros m H. induction m as [ | m' ].
    SCase "m = O".
     inversion H.
    SCase "m = S m'".
       simpl in H. inversion H.  rewrite plus_n_Sm in H1.
       rewrite plus_n_Sm in H1. inversion H1. apply IHn' in H2.
       rewrite -> H2. reflexivity.
Qed.


Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.  induction n as [ | n' ].
  Case "n = O".
   simpl. intros H. destruct m as [ | m'].
   SCase "m = O".
     reflexivity.
   SCase "m = S m'".
     simpl in H. inversion H.
  Case "n = S n'".
     intros H. destruct m as [ | m']. 
     SCase "m = O".
       inversion H.
     SCase "m = S m'".
       apply f_equal.
Abort.

Theorem double_injective : forall (  n m : nat ), 
 double m = double n -> m = n.
Proof. 
  intros n. induction n as [ | n' ].
  Case "n = O".
    simpl. intros m. destruct m as [ | m' ].
    SCase "m = O".
      simpl. reflexivity.
    SCase "m = S m'".
      simpl. intros H. inversion H.
  Case "n = S n'".
     simpl. intros m. destruct m as [ | m' ].
     SCase "m = O".
        simpl. intros H. inversion H.
     SCase "m = S m'".
       simpl. intros H. inversion H. apply IHn' in H1.
       apply f_equal. apply H1.
Qed.

Theorem beq_nat_true : forall ( n m : nat ) , 
   beq_nat n m = true -> n = m.
Proof.
 intros n. induction n as [ | n' ].
 Case "n = O".
   intros m. destruct m as [ | m' ].
   SCase "m = O".
       simpl. reflexivity.
   SCase "m = S m'".
       simpl. intros H. inversion H.
  Case "n = S n'".
   intros m. destruct m as [ | m' ].
   SCase "m = O".
     simpl. intros H. inversion H.
   SCase "m = S m'".
     simpl. intros H. apply IHn' in H.
     apply f_equal. apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [ | m'].
  Case "m = O".
     simpl. intros H. destruct n as [ | n' ].
     SCase "n = O".
      reflexivity.
     SCase "n = S n'".
      simpl in H. inversion H.
  Case "m = S m'".
     simpl. intros H. destruct n as [ | n' ].
     SCase "n = O".
      simpl in H. inversion H.
     SCase "n = S n'".
        simpl in H. inversion H. 
(* Watch carefull that our induction hypothesis is not going to help us.
    SCase := "n = S n'" : String.string
  Case := "m = S m'" : String.string
  n' : nat
  m' : nat
  IHm' : double (S n') = double m' -> S n' = m'
  H : S (S (double n')) = S (S (double m'))
  H1 : double n' = double m'
  ============================
   S n' = S m'
*)
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [ | m' ].
  Case "m = O".
    simpl. intros n. destruct n as [ | n' ].
    SCase "n = O".
      reflexivity.
    SCase "n = S n'".
      simpl. intros H. inversion H.
  Case "n = S n'".
    simpl. intros n. destruct n as [ | n'].
    SCase "n = O".
      simpl. intros H. inversion H.
    SCase "n = S n'".
      simpl. intros H. inversion H. apply IHm' in H1.
      apply f_equal. apply H1.
Qed.

Theorem length_snoc' : forall ( X : Type ) ( v : X ) ( l : list X ) ( n : nat ) ,
   length l = n ->
   length ( snoc l v ) = S n.
Proof.
 intros X v l. induction l as [ | v' l' ]. 
 Case "l = nil".
   simpl. intros n H. rewrite -> H. reflexivity.
 Case "l = cons v' l'".
   intros n H. simpl. destruct n as [ | n' ].
   SCase "n = O".
     inversion H.
   SCase "n = S n'".
     apply f_equal. apply IHl'. inversion H. reflexivity.
Qed.

(* solved using forward reasoning *)


Theorem length_snoc_bad : forall (X : Type) (v : X)
                                 (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l n H. induction l as [ | v' l'].
  Case "l = nil".
    simpl. simpl in H. rewrite H. reflexivity.
  Case "l = Cons v' l'".
    simpl. apply f_equal.
Abort.


Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [ | v' l' ].
  Case "l = nil".
   simpl. intros n. destruct n as [ | n' ].
   SCase "n = O".
     reflexivity.
   SCase "n = S n'".
     intros H. inversion H.
  Case "l = Cons v' l'".
    intros n. destruct n as [ | n' ].
    SCase "n = O".
      simpl. intros H. inversion H.
    SCase "n = S n'".
      simpl. intros H. inversion H. rewrite -> H1.
      apply IHl' in H1. apply H1.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type)
                               (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
   intros n X v l. generalize dependent n. induction l as [ | v' l' ].
   Case "l = nil".
     simpl. intros n H. rewrite -> H. reflexivity.
   Case "l = Cons v' l'".
     simpl. intros n. destruct n as [ | n' ].
     SCase "n = O".
       intros H. inversion H.
     SCase "n = S n'".
       intros H. inversion H. rewrite -> H1. apply IHl' in H1. 
       apply f_equal. apply H1.
Qed.

Theorem app_length_cons : forall  (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x. induction l1 as [ | v1' l1' ].
  Case "l1 = nil".
   simpl. intros n. destruct n as [ | n' ].
   SCase "n = O".
     intros H. inversion H.
   SCase "n = S n'".
     intros H. inversion H. reflexivity.
  Case "l1 = Cons v1' l1'".
    simpl. intros n. destruct n as [ | n' ].
    SCase "n = O".
      intros H. inversion H.
    SCase "n = S n'".
      intros H. inversion H. rewrite -> H1. apply IHl1' in H1. 
      apply f_equal. apply H1.
Qed.

Lemma length_twice : forall ( X : Type ) ( l1 l2 : list X ) ( v : X ),
     length ( l1 ++ v :: l2 ) = S ( length ( l1 ++ l2 ) ).
Proof.
  intros X l1 l2 v. induction l1 as [ | v1' l1'].
  Case "l1 = nil". 
    simpl. reflexivity.
  Case "l1 = Cons v1' l1'". 
     simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n. induction n as [ | n' ].
  Case "n = O".
     intros l H. destruct l as [ | v' l' ].
     SCase "l = nil".
        simpl. reflexivity.
     SCase "l = Cons v' l'".
        simpl. inversion H.
  Case "n = S n'".
     intros l. destruct l as [ | v' l'].
     SCase "l = nil".
      simpl. intros H. inversion H.
     SCase "l = Cons v' l'".
      simpl. intros H. apply f_equal. rewrite plus_n_Sm.
      rewrite length_twice. apply f_equal. inversion H. apply IHn' in H1.
      inversion H. rewrite H2. apply H1.
Qed.


Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P H1 H2 H3 H4 m. induction m as [ | m' ].
  Case "m = O".
     intros n. induction  n as [ | n' ].
     SCase "n = O".
       apply H1. apply H3. apply IHn'.
  Case "m = S m'".
     intros n.  induction n as [ | n'].
     SCase "n = O".
       apply H2. apply IHm'. apply H4. apply IHm'.
Qed.

(* Finally follow the type *)


Definition sillyfun ( n : nat ) : bool :=
  if beq_nat n 3 then false 
  else if beq_nat n 5 then false 
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct ( beq_nat n 3 ).
    Case "beq_nat n 3 = true".
       reflexivity.
    Case "beq_nat n 3 = false".     
      destruct ( beq_nat n 5 ).
      SCase "beq_nat n 5 = true".
         reflexivity.
      SCase "beq_nat n 5 = false".
         reflexivity.
Qed.

Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override.
  destruct ( beq_nat k1 k2 ). 
  Case "beq_nat k1 k2 = true". 
    reflexivity.
  Case "beq_nat k1 k2 = false".
   reflexivity.
Qed.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [ | v' l' ]. 
  Case "l = nil".
   intros l1 l2. simpl. intros H. inversion H. simpl. reflexivity.
  Case "l = Cons v' l'".
    destruct v'. 
Abort.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
   intros n. unfold sillyfun1.
   destruct ( beq_nat n 3 ). 
   Case "beq_nat n 3 = true".
     intros H.
(* We don't have enough information to proceed the calculation *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
   intros n H. unfold sillyfun1 in H.
   destruct ( beq_nat n 3 ) eqn : Heqn3.
   Case "beq_nat n 3 = true".
     apply beq_nat_true in Heqn3. rewrite -> Heqn3. reflexivity.
   Case "beq_nat n 3 = false".
      destruct ( beq_nat n 5 ) eqn : Heqn5.
      SCase "beq_nat n 5 = true".
         apply beq_nat_true in Heqn5. rewrite -> Heqn5. reflexivity.
      SCase "beq_nat n 5 = false".
         inversion H.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.  apply f_equal. destruct ( f ( f b ) ) eqn : feqn.
  Case "f ( f b ) = true".
     destruct b.
     SCase "b = true".
       reflexivity.
     SCase "b = false".
Abort.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H. unfold override.
  destruct ( beq_nat k1 k2 ) eqn : Heqn.
  Case "beq_nat k1 k2 = true".
   rewrite <- H. apply f_equal. apply beq_nat_true in Heqn.
   apply Heqn.
  Case "beq_nat k1 k2 = false".
    apply f_equal. reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [ | n'].
  Case "n = O".
    intros m. destruct m as [ | m' ].
    SCase "m = O".
      reflexivity.
    SCase "m = S m'".
      simpl. reflexivity.
  Case "n = S n'".
    intros m. destruct m as [ | m' ].
    SCase "m = O".
      simpl. reflexivity.
    SCase "m = S m'".
      simpl. apply IHn'.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p H1 H2.
  apply beq_nat_true in H1. apply beq_nat_true in H2. 
   rewrite -> H1. rewrite <- H2. SearchAbout ( beq_nat ).
   symmetry. apply beq_nat_refl.
Qed.

(*

Exercise: 3 stars, advanced (split_combine)
We have just proven that for all lists of pairs, combine is the inverse of split. 
How would you formalize the statement that split is the inverse of combine?
Complete the definition of split_combine_statement below with a property that 
states that split is the inverse of combine. Then, prove that the property holds. 
(Be sure to leave your induction hypothesis general by not doing intros on more 
things than necessary. Hint: what property do you need of l1 and l2 for split 
combine l1 l2 = (l1,l2) to be true?)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.

*)

Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
 intros X x1 x2 k1 k2 k3 f H. unfold override.
 destruct ( beq_nat k1 k3 ) eqn : Heqn1.
 Case "beq_nat k1 k3 = true".
   destruct ( beq_nat k2 k3 ) eqn : Heqn2.
   SCase "beq_nat k2 k3 = true".
    apply beq_nat_true in Heqn1. apply beq_nat_true in Heqn2.
    rewrite Heqn1 in H. rewrite Heqn2 in H. 
    assert ( Htrue: beq_nat k3 k3 = true ).
        symmetry. apply beq_nat_refl.
    rewrite Htrue in H. inversion H.
   SCase "beq_nat k2 k3 = false".
       reflexivity.
 Case "beq_nat k1 k3 = false".
       reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
 intros X test x l. induction l as [ | v' l' ].
 Case "l = nil".
  simpl. intros lf H. inversion H.
 Case "l = Cons v' l'".
  intros lf. destruct lf as [ | vf' lf'].
  SCase "lf' = nil".
   simpl. intros H. destruct ( test v' ) eqn : Htest.
   SSCase "test v' = true".
     inversion H. rewrite H1 in Htest. apply Htest.
   SSCase "test v' = false".
     apply IHl' in H. apply H.
  SCase "lf' = Cons vf' lf'".
   simpl. intros H. destruct ( test v' ) eqn : Htest.
   SSCase "test v' = true".
    inversion H. rewrite H1 in Htest. apply Htest.
   SSCase "test v' = false".
    apply IHl' in H. apply H.
Qed.

Fixpoint forallb { X : Type } ( f : X -> bool ) ( l : list X ) : bool :=
  match l with
  | nil => true
  | h :: t => andb ( f h ) ( forallb f t )
  end.

Eval compute in forallb oddb [1;3;5;7;9] = true.
Eval compute in forallb negb [false;false] = true.
Eval compute in forallb evenb [0;2;4;5] = false.
Eval compute in forallb (beq_nat 5) [] = true.

Fixpoint existsb { X : Type } ( f : X -> bool ) ( l : list X ) : bool :=
  match l with
  | nil => false
  | h :: t => orb ( f h ) ( existsb f t )
  end.

Eval compute in existsb (beq_nat 5) [0;2;3;6] = false.
Eval compute in existsb (andb true) [true;true;false] = true.
Eval compute in existsb oddb [1;0;0;0;0;3] = true.
Eval compute in existsb evenb [] = false.

(*

Next, define a nonrecursive version of existsb — call it existsb' — using forallb 
and negb.
Prove that existsb' and existsb have the same behavior.

*)


