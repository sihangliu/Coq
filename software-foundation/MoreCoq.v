Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  rewrite <- H1. apply H2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p H1 H2. apply H2 with (q := n). assumption.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m H1 H2. apply H2 with (q := n). assumption.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2. apply H1 with (n := 3). assumption.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl.
Abort.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl. symmetry. assumption.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H. symmetry. rewrite H. apply rev_involutive.
Qed.


Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite H1. assumption.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with (m := [c; d]).
  assumption. assumption.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2. rewrite H2. apply H1.
Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m H.
  inversion H. reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n m H.
  inversion H. reflexivity.
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
  intros X x y z l j H1 H2. inversion H1. inversion H2. symmetry.
  assumption.
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
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
                    x = y -> f x = f y.
Proof.
  intros A B f x y H.
  rewrite H. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  induction n.
  Case "n = O". simpl. intros H. reflexivity.
  Case "n = S n". simpl. intros H. inversion H.
Qed.
(* think of writing n = 0 from goal to hypothesis beq_nat 0 n = true *)

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  induction n.
  Case "n = O". simpl. intros H. reflexivity.
  Case "n = S n". simpl. intros H. inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  simpl. intros n m b H. assumption.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2. symmetry in H2. apply H1 in H2. symmetry.
  assumption.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  induction n.
  Admitted.

Theorem double_injective: forall n m, double n = double m -> n = m. 
Proof.
  induction n.
  Case "n = O".
  {
    induction m.
    SCase "m = O". intros H. reflexivity.
    SCase "m = S m". intros H. inversion H.
  }
  Case "n = S n".
  {
    induction m.
    SCase "m = O". intros H. inversion H.
    SCase "m = S m". intros H. inversion H. apply f_equal. apply IHn.
    assumption.
  }
Qed.

Theorem beq_nat_true : forall n m, beq_nat n m = true -> n = m.
Proof.
  induction n.
  Case "n = O".
  {
    induction m.
    SCase "m = O". intros H. reflexivity.
    SCase "m = S m". simpl. intros H. inversion H.
  }
  Case "n = S n".
  {
    induction m.
    SCase "m = O". simpl. intros H. inversion H.
    SCase "m = S m". simpl. intros H. apply f_equal. apply IHn. assumption.
  }
Qed.

Theorem double_injective_take2_FAILED : forall n m, double n = double m ->
     n = m.
Proof.
  induction n.
  Case "n = O".
  {
    induction m.
    SCase "m = O". intros H. reflexivity.
    SCase "m = S m". intros H. inversion H.
  }
  Case "n = S n".
  {
    induction m.
    SCase "m = O". intros H. inversion H.
    SCase "m = S m". intros H. inversion H. apply f_equal. apply IHn. assumption.
  }
Qed.

(* the idea here is try to delay the intros as much as possilbe. Atleast this 
is my feeliing *)

Theorem double_injective_take2 : forall n m, double n = double m -> n = m.
Proof.
  induction n.
  Case "n = O".
  {
    induction m.
    SCase "m = O". intros H. reflexivity.
    SCase "m = S m". intros H. inversion H.
  }
  Case "n = S n".
  {
    induction m.
    SCase "m = O". intros H. inversion H.
    SCase "m = S m". intros H. inversion H. apply f_equal. apply IHn. assumption.
  }
Qed.

Theorem length_snoc' : forall (X : Type) (v : X) (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  induction l.
  Case "l = []".
  {
    intros n H. simpl in H. simpl. apply f_equal. assumption.
  }
  Case "l = Cons n l".
  {
    induction n.
    SCase "n = O". simpl. intros H. inversion H.
    SCase "n = S n". simpl. intros H. inversion H. apply f_equal. rewrite H1.
    apply IHl. assumption.
  }
Qed.

Theorem length_snoc_bad : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l n H. induction l.
  Case "l = []". simpl. apply f_equal. simpl in H. assumption.
  Case "l = Cons v l".
  {
    simpl. apply f_equal. Abort.

(* In general, a good rule of thumb is to make the induction hypothesis as general as possible.  Yes this is what I had in mind when I proved bad one *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  induction n.
  Case "n = O".
  {
    simpl. induction l.
    SCase "l = []". simpl. intros H. reflexivity.
    SCase "l = Cons n l". simpl. intros H. inversion H.
  }
  Case "n = S n".
  {
    induction l.
    SCase "l = []". simpl. intros H. reflexivity.
    SCase "l = Cons n l". simpl. intros H. apply IHn. inversion H. reflexivity.
  }
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  induction n.
  Case "n = O".
  {
    induction l.
    SCase "l = []". simpl. intros H. reflexivity.
    SCase "l = Cons n l". simpl. intros H. inversion H.
  }
  Case "n = S n".
  {
    induction l.
    SCase "l = []". simpl. intros H. inversion H.
    SCase "l = Cons n l". simpl. intros H. inversion H. apply f_equal.
    rewrite H1. apply IHn. assumption.
  }
Qed.

(* we can prove this by induciton on n *)

Theorem length_snoc'''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros. generalize dependent n. induction l.
  Case "l = []". simpl. intros n H. apply f_equal. assumption.
  Case "l = Cons n l".
  {
    induction n.
    SCase "n = O". simpl. intros H. inversion H.
    SCase "n = S n". simpl. intros H. apply f_equal. apply IHl. inversion H.
    reflexivity.
  }
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x. induction l1.
  Case "l1 = []". simpl. intros. assumption.
  Case "l1 = Cons n l1".
  {
    induction n.
    SCase "n = O". simpl. intros H. inversion H.
    SCase "n = S n". simpl. intros H. apply f_equal. apply IHl1. inversion H.
    reflexivity.
  }
Qed.

Lemma length_twice : forall ( X : Type ) ( l1 l2 : list X ) ( v : X ),
     length ( l1 ++ v :: l2 ) = length l1 + S (length l2 ).
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
  intros X n l. generalize dependent n.
  induction l.
  Case "l = []". simpl. intros n H. rewrite <- H. reflexivity.
  Case "l = Cons n l".
  {
    induction n.
    SCase "n = O". simpl. intros. inversion H.
    SCase "n = S n". simpl. intros H.  apply f_equal.
    rewrite length_twice. inversion H. reflexivity.
  }
Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P H1 H2 H3 H4 m. induction m.
  Case "m = O".
     intros n. induction  n.
     SCase "n = O". apply H1.
     SCase "n = S n". apply H3. apply IHn.
  Case "m = S m".
     intros n.  induction n.
     SCase "n = O". apply H2. apply IHm.
     SCase "n = S n". apply H4. apply IHm.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  Case "beq_nat n 3 = true". reflexivity.
  Case "beq_nat n 3 = false".
  {
    destruct (beq_nat n 5).
    SCase "beq_nat n 5 = true". reflexivity.
    SCase "beq_nat n = false". reflexivity.
  }
  Show Proof.
Qed.
Print sillyfun_false.

Theorem override_shadow : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y. induction l.
  Case "l = []". simpl. intros l1 l2 H. inversion H.  simpl. reflexivity.
  Case "l = Cons v l".
  {
    destruct l. destruct x.
    induction l1.
    induction l2.
    simpl. intros H. inversion H.
    simpl. intros H. inversion H.
    induction l2.
    simpl. intros H. inversion H.
    simpl. intros H. inversion H. simpl. reflexivity.
    destruct x. destruct p. intros l1 l2.
    simpl.
Abort.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.
Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n H.  unfold sillyfun1 in H.
  destruct (beq_nat n 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n H. unfold sillyfun1 in H.
  destruct (beq_nat n 3) eqn : Heqn3.
  Case "beq_nat n 3 = true". apply beq_nat_true in Heqn3.
  rewrite Heqn3. reflexivity.
  Case "beq_nat n 3 = false".
  {
    destruct (beq_nat n 5) eqn : Heqn5.
    SCase "beq_nat n 5 = true". apply beq_nat_true in Heqn5.
    rewrite Heqn5. reflexivity.
    SCase "beq_nat n 5 = false". inversion H.
  }
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn:H.
  destruct (f true) eqn: H1.
  rewrite H1. assumption.
  destruct (f false) eqn: H2. assumption. assumption.
  destruct (f false) eqn : H1.
  destruct (f true) eqn: H2. assumption. assumption.
  rewrite H1. assumption.
Qed.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H. unfold override.
  destruct (beq_nat k1 k2) eqn: H1. apply beq_nat_true in H1.
  rewrite <- H1. symmetry. assumption.
  reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  SearchAbout beq_nat.
  induction n.
  Case "n = O".
  {
    induction m.
    SCase "m = O". reflexivity.
    SCase "m = S m". simpl. reflexivity.
  }
  Case "n = S n".
  {
    induction m.
    SCase "m = O". simpl. reflexivity.
    SCase "m = S m". simpl. apply IHn.
  }
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p H1 H2. apply beq_nat_true in H1.
  apply beq_nat_true in H2.
  rewrite H1. rewrite H2. symmetry. apply beq_nat_refl.
Qed.

(* 

We have just proven that for all lists of pairs, combine is the inverse of split. How would you formalize the statement that split is the inverse of combine? When is this property true?
Complete the definition of split_combine_statement below with a property that states that split is the inverse of combine. Then, prove that the property holds. (Be sure to leave your induction hypothesis general by not doing intros on more things than necessary. Hint: what property do you need of l1 and l2 for split combine l1 l2 = (l1,l2) to be true?)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

*)

Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f H.
  SearchAbout (beq_nat _ _ = false). unfold override.
  destruct (beq_nat k1 k3) eqn: H1.
  Case "beq_nat k1 k3 = true".
  {
    apply beq_nat_true in H1. rewrite <- H1. rewrite H. reflexivity.
  }
  Case "beq_nat k1 k3 = false". reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l. induction l.
  Case "l = []". simpl. intros lf H. inversion H.
  Case "l = Cons v l".
  {
    induction lf.
    SCase "lf = []".
    {
      simpl. destruct (test x0) eqn : Ht.
      SSCase "test x0 = true". intros H. inversion H. rewrite <- H1. assumption.
      SSCase "test x0 = false". intros H. apply IHl in H. assumption.
    }
    SCase "lf = Cons v l".
    {
      simpl. intros H. destruct (test x0) eqn : Htest.
      SSCase "test x0 = true". inversion H. rewrite <- H1. assumption.
      SSCase "test x0 = false". apply IHl in H. assumption.
    }
  }
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

Definition existsb' {X : Type} (f : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (f x)) l).

Eval compute in existsb' (beq_nat 5) [0;2;3;6] = false.
Eval compute in existsb' (andb true) [true;true;false] = true.
Eval compute in existsb' oddb [1;0;0;0;0;3] = true.
Eval compute in existsb' evenb [] = false.

Theorem equalboth : forall (X : Type) (f : X -> bool) (l : list X),
                      existsb f l = existsb' f l.
Proof.
  intros X f. induction l.
  Case "l = []". simpl. unfold existsb'. simpl. reflexivity.
  Case "l = Cons v l".
  {
    unfold existsb' in IHl. unfold existsb'. simpl.
    destruct (f x) eqn: Ht.
    SCase "f x = true". simpl. reflexivity.
    SCase "f x = false". simpl. assumption.
  }
Qed.

(* finally solved this. feeling high :) *)
