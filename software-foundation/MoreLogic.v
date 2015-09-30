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

