Require Export "Prop".

Inductive ex (X : Type) (P : X -> Type) : Prop :=
  ex_intro: forall (witness : X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n × n) = 6.
Proof.
  apply ex_intro with (witness := 2).
  reflexivity.
Qed.

Example exists_example_1' : exists n, n + (n × n) = 6.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H. inversion H as [m Hm].
  exists (2 + m). assumption.
Qed.

Lemma exists_example_3 : exists (n:nat), even n /\ beautiful n.
Proof.
  exists 8. split.
  Case "left". unfold even. reflexivity.
  Case "right". apply b_sum with (n := 3) (m := 5). apply b_3. apply b_5.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros H1. inversion H1 as [x Hx].
  apply Hx.  apply H.
Qed.


Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  Case "left".
  {
    intros H. inversion H as [m Hm]. inversion Hm as [Hp | Hq].
    SCase "left". left. exists m. assumption.
    SCase "rigth". right. exists m. assumption.
  }
  Case "right".
  {
     intros H. inversion H as [Hp | Hq].
     inversion Hp.
     SCase "left". exists witness. left. assumption.
     inversion Hq.
     SCase "rigth". exists witness. right. assumption.
  }
Qed.

Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n. induction n.
  Case "n = O".
  {
    intros m. destruct m.
    SCase "m = O". apply left. reflexivity.
    SCase "m = S m". apply right. intros H. inversion H.
  }
  Case "n = S n".
  {
    intros m. destruct m.
    SCase "m = O". apply right. intros H. inversion H.
    SCase "m = S m". destruct IHn with (m := m) as [Heq | Hneq].    
    apply left. apply f_equal. assumption.
    apply right.  intros H. inversion H. apply Hneq. assumption.
  }
Qed.

Definition override' {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X : Type) x1 k1 k2 (f : nat -> X),
                           f k1 = x1 -> (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H. unfold override'.
  destruct (eq_nat_dec k1 k2). rewrite <- H. apply f_equal. assumption.
  reflexivity.
Qed.


Theorem override_shadow' : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override'.
  destruct (eq_nat_dec k1 k2). reflexivity. reflexivity.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| empty : all X P []
| cons : forall (x : X) (xs : list X),  P x -> all X P xs -> all X P (x :: xs).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_and_all :
  forall (X : Type) (test : X -> bool) (l : list X),
    forallb test l = true <-> all X (fun x => test x = true) l.
Proof.
  intros X test l. split.
  Case "->".
  {
    induction l.
    SCase "[]". intros H. apply empty.
    SCase "Cons n l". simpl. intros H. apply cons. destruct (test x).
    reflexivity. inversion H. apply andb_prop in H. inversion H. apply IHl.
    assumption.
  }
  Case "<-".
  {
    intros H. induction H.
    SCase "empty". reflexivity.
    SCase "cons". simpl. apply andb_true_intro. split. assumption.
    assumption.
  }
Qed.


Inductive merge {X : Type} : list X -> list X -> list X -> Prop :=
| emptym : merge [] [] []
| firstm : forall (x : X) (l m n : list X), merge l m n -> merge (x :: l) m (x :: n)
| secondm : forall (x : X) (l m n : list X), merge l m n -> merge l (x :: m) (x :: n).


Theorem filter_challenge : forall (X:Type) (test: X->bool) (l1 l2 l:list X),
  merge l1 l2 l ->
  all X (fun x => test x = true) l1 ->
  all X (fun x => test x = false) l2 ->
  filter test l = l1.
Proof. Abort.

Inductive appears_in {X : Type} (a : X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a :: l)
| ai_later : forall b l, appears_in a l -> appears_in a (b :: l).

Lemma appears_in_app : forall (X : Type) (xs ys : list X) (x : X),
   appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
 intros X xs ys x H. induction xs.
 Case "nil". right. assumption.
 Case "Cons n l".
 {
   inversion H.
   SCase "left". left. apply ai_here.
   SCase "right".  apply IHxs in H1. inversion H1. left. apply ai_later.
   assumption.  right. assumption.
 }
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x : X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x H. destruct H.
  induction xs. inversion H. inversion H.
  constructor. simpl. constructor. auto.
  induction xs. assumption.
  simpl. constructor. assumption.
Qed.
