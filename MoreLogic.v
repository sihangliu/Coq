Require Export "Prop".

Inductive ex ( X : Type ) ( P : X -> Prop ) : Prop :=
  ex_intro : forall ( witness : X ) ,  P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with ( witness := 2 ).
  reflexivity.
Qed.

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  ( exists m, n = 4 + m) ->
  ( exists o, n = 2 + o).
Proof.
  intros n H. inversion H as [ m Hm ].
  exists ( 2 + m ). apply Hm.
Qed.


Lemma exists_example_3 :
  exists ( n : nat ), even n /\ beautiful n.
Proof.
  exists 8.
  split. unfold even. simpl. reflexivity.
  apply b_sum with ( n := 3 ) ( m := 5 ).
  apply b_3. apply b_5.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros E. inversion E. 
  apply H0. apply H with ( x := witness ).
  Show Proof.
Qed.

(*
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).

 *)

Theorem dist_exists_or : forall ( X : Type ) ( P Q : X -> Prop ),
  ( exists x, P x \/ Q x) <-> ( exists x, P x) \/ ( exists x, Q x).
Proof.
 intros X P Q . split.
 Case "left". 
   intros H. inversion H. inversion H0 as [ HP | HQ ].
   SCase "left". left. exists witness. apply HP.
   SCase "right". right. exists witness. apply HQ.
 Case "right".
   intros H. inversion H as [ HP | HQ ].
   inversion HP. exists witness.
   SCase "left". left. apply H0.
   inversion HQ. exists witness.
   right. apply H0.
Qed.


Inductive sumbool ( A B : Prop ) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.
Theorem eq_nat_dec : forall n m : nat, { n = m } + { n <> m }.
Proof.
  intros n. induction n as [ | n' ].
  Case "n = O".
  intros m.  induction m as [ | m'].
  SCase "m = O". left. reflexivity.
  SCase "m = S m'". right. unfold not. intros H.
  inversion H.
  Case "n = S n'".
  intros m. induction m as [ | m'].
  SCase "m = O". right. unfold not. intros H.
  inversion H.
  SCase "m = S m'".
  destruct IHn' with ( m := m' ) as [ eq | neq].
  left. apply f_equal. assumption.
  right. unfold not. intros H. inversion H. unfold not in neq. apply neq.
  assumption.
Defined.

Definition override' { X : Type } ( f : nat -> X ) ( k : nat ) ( x : X ) : nat -> X :=
  fun ( k' : nat ) => if eq_nat_dec k k' then x else f k'.
Theorem override_same' : forall ( X : Type ) x1 k1 k2 ( f : nat -> X ),
                           f k1 = x1 -> ( override' f k1 x1 ) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H.
  unfold override'.
  destruct ( eq_nat_dec k1 k2 ). rewrite <- e. rewrite -> H.
  reflexivity. apply f_equal. reflexivity.
Qed.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override' at 1.
  destruct ( eq_nat_dec k1 k2 ).
  Case "K1 = K2". unfold override'.
  destruct ( eq_nat_dec k1 k2 ). reflexivity.
  unfold not in n. apply n in e. inversion e.
  unfold override'. destruct ( eq_nat_dec k1 k2 ). unfold not in n.
  apply n in e. inversion e. reflexivity.
Qed.
