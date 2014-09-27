Require Export Poly.

Theorem silly1 : forall ( m n o p : nat ), 
     n = m -> [ n ; o ] = [ n ; p ] ->
     [ n ; o ] = [ m ; p ].
Proof.
  intros m n o p H1 H2. rewrite <- H1. apply H2.
Qed.

Theorem silly2 : forall ( n m o p : nat ) , 
  n = m ->
  ( forall ( q r : nat ), q = r -> [ q ; o ] = [ r ; p ] ) ->
  [ n ; o ] = [ m ; p ].
Proof.
  intros n m o p H1 H2. rewrite -> H1. apply H2.
  reflexivity.
Qed.

Theorem silly2a : forall ( n m : nat ),
   ( n , n ) = ( m , m ) -> 
   ( forall ( q r : nat ), ( q , q ) = ( r , r ) -> [ q ] = [ r ] ) ->
   [ n ] = [ m ].
Proof.
  intros n m H1 H2. apply H2. apply H1.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true ->  oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2. compute. discriminate.
Qed.

Theorem silly_ex' :
     (forall n, evenb n = true ->  oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
   intros H1 H2. apply H1. apply H2.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
 intros n H1. simpl. rewrite <- H1. reflexivity.
Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
 intros n H. symmetry. simpl. apply H.
Qed.


Theorem rev_exercise1 : forall ( X : Type ) (l l' : list X),
     l = rev l' ->
     l' = rev l.
Proof.
 intros X l l' H. SearchAbout ( rev ( rev _ )). symmetry. rewrite -> H. 
 apply rev_involutive.
Qed.


Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
 intros a b c d e f H1 H2. rewrite -> H1. apply H2.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
 intros X n m o H1 H2. rewrite -> H1. apply H2.
Qed. 

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
 intros a b c d e f H1 H2. apply trans_eq with ( m := [ c ; d ] ).
 apply H1. apply H2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
 intros n m o p H1 H2. apply trans_eq with m. apply H2. apply H1.
Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j H1 H2. inversion H1. inversion H2.  symmetry. apply H0.
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


Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
 intros X x y z l j H1 H2. inversion H1.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
 intros A B f x y H. rewrite -> H. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
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

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof. 
  intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3'mine : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
 intros n H1 H2. simpl in H1. simpl. apply H2. 
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
 intros n H1 H2. symmetry in H2. apply H1 in H2. symmetry. apply H2.
Qed.

(*
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
 intros n. induction n as [ | n'].
 Case "n = nil".
  intros m H. 

*)

Theorem double_injective: forall n m, double n = double m -> n = m. 
Proof.
 intros n m. induction n as [ | n'].
 Case "n = nil". 
    simpl. intros eq. destruct m as [ | m'].
    SCase "m = nil".
      reflexivity.
    SCase "m = S m'". 
      inversion eq.
  Case "n = S n'".
    simpl. intros eq. destruct m as [ | m'].
    SCase "m = O".
      inversion eq.
    SCase "m = S m'".
     apply f_equal.
     Abort.


Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [ | n'].
  Case "n = O".
   simpl. intros m eq. destruct m as [ | m'].
   SCase "m = O".
      reflexivity. 
   SCase "m = S m'".
      inversion eq.
  Case "n =  S n'".
   simpl. intros m eq. destruct m as [ | m'].
   SCase "m = O".
     inversion eq.
   SCase "m = S m'".
     inversion eq. apply IHn' in H0.  rewrite -> H0. reflexivity.
Qed.


Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [ | n'].
  Case "n = O".
    intros m eq. destruct m as [ | m'].
    SCase "m = O".
        reflexivity.
    SCase "m = S m'".
        inversion eq.
  Case "n = S n'".
    intros m eq. destruct m as [ | m'].
    SCase "m = O".
      inversion eq.
    SCase "m = S m'".
     apply IHn' in eq. rewrite -> eq. reflexivity.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [ | m'].
  Case "m = O".
   simpl. intros eq. destruct n as [ | n'].
   SCase "n = O". 
     reflexivity.
   SCase "n = S n'".
     inversion eq.
  Case "m = S m'".
     simpl. intros eq. destruct n as [ | n' ].
     SCase "n = O".
      inversion eq.
     SCase "n = S n'".
      apply f_equal.
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  generalize dependent n.
  induction m as [ | m'].
  Case "m = O".
   simpl. intros n eq. destruct n as [ | n'].
   SCase "n = O".
     reflexivity.
   SCase "n = S n'".
    inversion eq.
  Case "m = S m'".
    simpl. intros n eq. destruct n as [ | n'].
    SCase "n = O".
      inversion eq.
    SCase "n = S n'".
      inversion eq. apply IHm' in H0. rewrite -> H0.
      reflexivity.
Qed.

Theorem length_snoc' : forall (X : Type) (v : X) (l : list X) (n : nat),
     length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [ | v' l' ].
  Case "l = nil".
    simpl. intros n eq. rewrite <- eq. reflexivity.
  Case "l = cons v' l'".
    simpl. intros n eq. destruct n as [ | n']. 
    SCase "n = O".
       inversion eq.
    SCase "n = S n'".
      inversion eq. apply IHl' in H0. rewrite -> H0. rewrite -> eq.
      reflexivity.
Qed.


Theorem length_snoc_bad : forall (X : Type) (v : X) (l : list X) (n : nat),
     length l = n -> length (snoc l v) = S n.
Proof.
 intros X v l n H. induction n as [ | n'].
 Case "n = O".
   destruct l as [ | v' l' ].
   SCase "l = nil".
     simpl. reflexivity.
   SCase "l = cons v' l'".
     simpl. inversion H. rewrite H in IHn'.
Abort. (* I am getting 

 X : Type
  v : X
  l : list X
  n' : nat
  H : length l = S n'
  IHn' : S n' = n' -> length (snoc l v) = S n'
  ============================
   length (snoc l v) = S (S n')
*)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [ | v' l'].
  Case "l = nil".
   simpl. intros n eq. reflexivity.
  Case "l = cons v' l'".
    simpl. intros n eq. destruct n as [ | n'].
    SCase "n = O".
     simpl. inversion eq.
    SCase "n = S n'".
     simpl. inversion eq. rewrite -> H0. apply IHl' in H0.
     rewrite -> H0. reflexivity.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type) (v : X) (l : list X),
     length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l. generalize dependent n.
  induction l as [ | v' l'].
  Case "l = nil".
    simpl. intros n eq. inversion eq. reflexivity.
  Case "l = cons v' l'".
    simpl. intros n eq. induction n as [ | n'].
    SCase "n = O".
      inversion eq.
    SCase "n = S n'".
       inversion eq. apply IHl' in H0. rewrite -> H0. inversion eq.
       reflexivity.
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x. induction l1 as [ | v1' l1'].
  Case "l1 = nil".
   simpl. intros n H. apply H.
  Case "l1 = cons v1' l1'".
   simpl. intros n H. induction n as [ | n'].
   SCase "n = O".
     inversion H.
   SCase "n = S n'".
     inversion H. apply IHl1' in H1. rewrite -> H1. rewrite -> H.
     reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l H. generalize dependent n.
  induction l as [ | v' l'].
  Case "l = nil".
   simpl. intros n H. rewrite <- H. reflexivity.
  Case "l = cons v' l'".
   intros n H. destruct n as [ | n'].
   SCase "n = O".
    simpl. discriminate.
   SCase "n = S n'".
    inversion H. apply IHl' in H1. inversion H. symmetry in H1. 
    symmetry in H2. rewrite H2 in H1. symmetry in H1. 

(*
I am stuck with this goal.
SCase := "n = S n'" : String.string
  Case := "l = cons v' l'" : String.string
  X : Type
  v' : X
  l' : list X
  IHl' : forall n : nat, length l' = n -> length (l' ++ l') = n + n
  n' : nat
  H : length (v' :: l') = S n'
  H1 : length (l' ++ l') = length l' + length l'
  H2 : n' = length l'
  ============================
   length ((v' :: l') ++ v' :: l') = S (length l') + S (length l')

*)
Abort.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n. 
Proof.
 intros P H1 H2 H3. induction m as [ | m'].
 Case "m = O".
  induction n as [ | n'].
  SCase "n = O".
    apply H1. apply H3. apply IHn'.
 Case "m = S m'".
  induction n as [ | n'].
  SCase "n = O".
   apply H2.  apply IHm'. apply H in IHn'. apply H.
   apply IHm'.
Qed.
(* Frankly speaking I just followed the rules. I don't what is going behind
   this proof. :(
*)

Definition sillyfun ( n : nat ) : bool := 
 if beq_nat n 3 then false 
 else if beq_nat n 5 then false 
 else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct ( beq_nat n 3 ).
  Case "beq_nat n 3 = True". 
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
  destruct ( beq_nat k1 k2 ). reflexivity.
  reflexivity.
Qed.
 
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
 intros X Y l. induction l as [ | v' l'].
 Case "l = nil".
  intros l1 l2 H.
 inversion H. reflexivity.
 Case "l = cons v' l'".
(*

 Case := "l = cons v' l'" : String.string
  X : Type
  Y : Type
  v' : X * Y
  l' : list (X * Y)
  IHl' : forall (l1 : list X) (l2 : list Y),
         split l' = (l1, l2) -> combine l1 l2 = l'
  ============================
   forall (l1 : list X) (l2 : list Y),
   split (v' :: l') = (l1, l2) -> combine l1 l2 = v' :: l'

*)
Abort.

Definition sillyfun1 ( n : nat ) : bool :=
  if beq_nat n 3 then true 
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n H. unfold sillyfun1 in H.
  destruct ( beq_nat n 3 ).
(* no enough information in context to prove the goal*)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n H. unfold sillyfun1 in H.
  destruct ( beq_nat n 3 ) eqn : Heqn3.
  Case "e3 = true".
   apply beq_nat_true in Heqn3.
   rewrite -> Heqn3. reflexivity.
  Case "e3 = false".
   destruct ( beq_nat n 5 ) eqn : Heqn5.
   SCase "e5 = true ".
     apply beq_nat_true in Heqn5. rewrite -> Heqn5. reflexivity.
   SCase "e5 = false".
     inversion H.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
Abort.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
Abort.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
 intros n. induction n as [ | n'].
 Case "n = O".
   destruct m as [ | m'].
   SCase "m = O".
    reflexivity.
   SCase "m = S m'".
    simpl. reflexivity.
 Case "n = S n'".
   destruct m as [ | m'].
   SCase "m = O".
    simpl. reflexivity.
   SCase "m = S m'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
 intros n. induction n as [ | n'].
 Case "n = O".
  intros m. destruct m as [ | m'].
  SCase "m = O".
    intros p H1 H2. apply H2.
  SCase "m = S m'".
    intros p. destruct p as [ | p'].
    SSCase "p = O".
      intros H1 H2. reflexivity.
    SSCase "p = S p'".
      intros H1 H2. discriminate.
 Case "n = S n'".
  intros m. destruct m as [ | m'].
  SCase "m = O".
    intros p. destruct p as [ | p'].
    SSCase "p = O".
      intros  H1 H2. inversion H1.
    SSCase "p = S p'".
      intros H1 H2. inversion H1.    
  SCase "m = S m'".
    intros p. destruct p as [ | p'].
    SSCase "p = O".
     intros H1 H2. discriminate.
    SSCase "p = S p'".
     intros H1 H2. inversion H1. inversion H2. simpl.
     apply beq_nat_true in H0. apply beq_nat_true in H3.
     rewrite -> H0. rewrite -> H3. reflexivity.
Qed.

Locate beq_nat_true.


Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f. 
  generalize dependent k3. generalize dependent k2. generalize dependent k1.
  intros k1. induction  k1 as [ | k1'] eqn : Hk1.  unfold override.
  Case "k1 = O".
    intros k2. destruct k2 as [ | k2' ] eqn : Hk2'.
    SCase "k2 = O".
      intros k3 H. inversion H.
    SCase "k2 = S k2'".
      intros k3 H. destruct k3 as [ | k3' ] eqn : Hk3.
      SSCase "k3 = O".
          simpl. reflexivity.
      SSCase "k3 = S k3'".
          simpl. reflexivity.
  Case "k1 = S k1'".
    intros k2. destruct k2 as [ | k2' ] eqn : Hk2.
    SCase "k2 = O".
      intros k3 H. induction k3 as [ | k3' ] eqn : Hk3.
      SSCase "k3 = O".
        unfold override. rewrite -> S_nbeq_0. simpl. reflexivity.
      SSCase "k3 = S k3'".
        unfold override. simpl. reflexivity.
    SCase "k2 = S k2'".
      intros k3 H. destruct k3 as [ | k3' ] eqn : Hk3.
      unfold override.
      SSCase "k3 = O".
        simpl. reflexivity.
      SSCase "k3 = S k3'".
        unfold override. simpl. inversion H. 
(*
1 subgoals, subgoal 1 (ID 2479)
  
  SSCase := "k3 = S k3'" : String.string
  SCase := "k2 = S k2'" : String.string
  Case := "k1 = S k1'" : String.string
  X : Type
  x1 : X
  x2 : X
  f : nat -> X
  k1 : nat
  k1' : nat
  Hk1 : k1 = S k1'
  IHk1' : k1 = k1' ->
          forall k2 k3 : nat,
          beq_nat k2 k1' = false ->
          override (override f k2 x2) k1' x1 k3 =
          override (override f k1' x1) k2 x2 k3
  k2 : nat
  k2' : nat
  Hk2 : k2 = S k2'
  k3 : nat
  H : beq_nat (S k2') (S k1') = false
  k3' : nat
  Hk3 : k3 = S k3'
  H1 : beq_nat k2' k1' = false
  ============================
   (if beq_nat k1' k3' then x1 else if beq_nat k2' k3' then x2 else f (S k3')) =
   (if beq_nat k2' k3' then x2 else if beq_nat k1' k3' then x1 else f (S k3'))
*)
Abort.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
 intros X test x l lf. generalize dependent l.
 induction lf as [ | vl' lf' ] eqn : Hlf.
 Case "lf = nil".
   intros l. destruct l as [ | v' l'] eqn : Hl.
   SCase "l = nil".
    simpl. intros H. inversion H.
   SCase "l = cons v' l'".
    intros H. simpl in H.
    destruct ( test v' ) eqn : Htest.
    SSCase "test v' = true".
      inversion H. rewrite <- H1. rewrite -> Htest. reflexivity.
    SSCase "test v' = false".
Abort.


Fixpoint forallb { X : Type } ( f : X -> bool ) ( l : list X ) : bool :=
  match l with
  | nil => true
  | h :: t => andb ( f h )  ( forallb f t )
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

Definition existsb' { X : Type } ( f : X -> bool ) ( l : list X ) : bool :=
   
