Require Import Arith.
Require Import ZArith.
Require Import Bool.
Require Import List.
Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
 | sortedzer : sorted nil
 | sortedone : forall x : Z, sorted ( x :: nil )
 | sortedres : forall ( x y : Z ) ( l : list Z ) ,
                  x <= y -> sorted ( y :: l ) -> sorted ( x :: y :: l ).

Theorem sorted_inv : forall ( z : Z ) ( l : list Z ),
                       sorted ( z :: l ) -> sorted l.
Proof.
  intros z l H. inversion H. apply sortedzer. auto.
Qed.

Print  Z_le_gt_dec.
Fixpoint aux ( n : Z ) ( l : list Z ) : list Z :=
  match l with
    | nil => n :: nil
    | ( p :: l' ) => if Z_le_gt_dec n p then p :: ( aux n l' )
                     else n :: p :: l'
  end.

Theorem aux_equiv :
  forall ( x : Z ) ( l : list Z ), aux x l = x :: l.
Proof.
  intros x l. unfold aux. Admitted.

Theorem imp_trans :
  forall ( P Q R : Prop ), ( P -> Q ) -> ( Q -> R ) -> P -> R.
Proof.
  intros P Q R H1 H2 p. apply H2. apply H1. apply p.
Qed.

Lemma weak_peirce :
  forall ( P Q : Prop ), (((( P -> Q ) -> P ) -> P ) -> Q ) -> Q.
Proof.                      
  intros P Q H. apply H. intros H1. apply H1. intros H2.
  apply H. intros H3. apply H2.
Qed.

Check le 3 4.
Check and.
Check fst.
Check ( forall ( P : Prop ), P -> P ).
Check ( true = false ).
Check list Prop.
Open Scope nat_scope.
Definition lt ( n p : nat ) : Prop := S n <= p.

Theorem conv_example :
  forall n : nat , 7 * 5 < n -> 6 * 6 <= n.
Proof.
  intros n H. assumption.
Qed.

Print conv_example.
Check ( imp_trans _ _ _ ( le_S 0 1 ) ( le_S 0 2 ) ).

Definition neutral_left ( A : Set ) ( op : A -> A -> A ) ( e : A ) : Prop :=
  forall x : A, op e x = x.

Theorem one_neutral_left : neutral_left Z Zmult 1%Z.
Proof.
  unfold neutral_left. intros x. omega.
Qed.

Theorem all_imp_dist :
  forall ( A : Type ) ( P Q : A -> Type ),
    (forall x : A, P x -> Q x ) -> ( forall y : A , P y ) -> forall z : A , Q z.
Proof.
  intros A P Q H1 H2 z.
  apply H1. apply H2.
Qed.


Theorem le_mult_mult:
  forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros a b c d H1 H2.
  apply le_trans with ( m := c * b ).
  Search ( _ <= _ -> _ * _ <= _ * _ ).
  apply mult_le_compat_r. assumption.
  apply mult_le_compat_l. assumption.
Qed.

Theorem le_mult_mult' :
  forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros a b c d H1 H2.
  eapply le_trans.
  eapply mult_le_compat_l. eexact H2.
  apply mult_le_compat_r. assumption.
Qed.

Theorem lt_S :
  forall n p : nat, n < p -> n < S p.
Proof.
  intros n p H. apply le_S. trivial.
Qed.

Definition opaque_f : nat -> nat -> nat.
  intros. assumption.
Qed.

Print opaque_f.
Open Scope Z_scope.

Definition Zsquare_diff ( x y : Z ) : Z := (x * x - y * y).
Theorem unfold_example:
  forall x y : Z, x * x = y * y  ->
                  ( Zsquare_diff x y )%Z * Zsquare_diff ( x + y ) ( x + y ) = 0.
Proof.
  intros x y H. unfold Zsquare_diff at 1. rewrite -> H.
  SearchAbout ( _ * _ - _ * _ ).
Admitted.


Section ex_falso_quodlibet.
  Hypothesis ff : False.
  Lemma ex1 : 220 = 284.
  Proof.
    apply False_ind. exact ff.
  Qed.
  Lemma ex2 : 220 = 284.
  Proof.
    elim ff.
  Qed.
End ex_falso_quodlibet.

Print ex2.
Theorem absurd : forall P Q : Prop, P -> ~P -> Q.
Proof.
  intros P Q p H. elim H. assumption.
Qed.

Theorem double_neg_i :
  forall P : Prop, P -> ~~P.
Proof.
  intros P p H. elim H. assumption.
Qed.

Theorem modus_ponens :
  forall P Q : Prop, P -> ( P -> Q ) -> Q.
Proof.
  intros P Q p H. apply H. assumption.
Qed.

Theorem double_neg_i' :
  forall P : Prop, P -> ~~P.
Proof.
  intros P. Proof ( modus_ponens P False ).

Theorem contrap :
     forall A B : Prop, ( A -> B ) -> ( ~B -> ~A ).
Proof.
  intros A B. unfold not.
  intros H1 H2 a. apply H2. apply H1. assumption.
Qed.

Theorem not_false : ~False.
Proof.
  unfold not. intros H. assumption.
Qed.

Theorem not_not_not_p :
  forall P Q : Prop, ~~~P -> P -> Q.
Proof.
  intros P Q. unfold not. intros H p. elim H.
  intros H1. apply H1. assumption.
Qed.

Theorem ex_imp_ex :
  forall ( A : Type ) ( P Q : A -> Prop ),
    ( ex P ) -> ( forall x : A, P x -> Q x ) -> ex Q.
Proof.
  intros A P Q H1 H2.
  inversion H1. exists x.
  apply H2. assumption.
Qed.

Theorem ex_PQ :
  forall ( A : Set ) ( P Q : A -> Prop ),
    ( exists  x : A, ( P x \/ Q x )) ->  ( ex P ) \/ ( ex Q ).
Proof.
  intros A P Q H.
  inversion H. inversion H0 as [ HP | HQ ].
  left. exists x. assumption.
  right. exists x. assumption.
Qed.

Theorem diff_square :
  forall a b : Z,
    ( a + b ) * ( a - b ) = a * a - b * b .
Proof.
  intros a b.
  Require Import ZArithRing.
  ring.
Qed.

(*
Definition my_true : Prop :=
  forall P : Prop, P -> P.
Definition my_false : Prop :=
  forall P : Prop, P.
Theorem my_I : my_true.
proof.
  unfold my_true. intros P p. assumption.
*)
  
Section inject_example.
  Variables A B : Set.
  Inductive T : Set :=
  | cone : A -> T
  | ctwo : B -> T.
  Theorem inject_ctwo :
    forall x y : B, ctwo x = ctwo y -> x = y.
  Proof.
    intros x y H.
    change ( let phi :=  fun ( v : T ) =>
      match v with
       | cone _ => x
       | ctwo v' => v'
      end in phi ( ctwo x ) = phi ( ctwo y )).
    rewrite H. reflexivity.   
  Qed.
End inject_example.

Print nat_ind.

Variable div_pair :
  forall a b : Z, 0 < b ->
                  { p : Z * Z | a = ( fst p ) * b + snd p /\ 0 <= snd p < b}.

Eval compute in div_pair 4 5.

Definition pred' :
  forall n : nat, { p : nat | n = S p }+{ n = O }.
  intros n. case n.
  right. apply refl_equal.
  intros p.left. exists p. reflexivity.
Defined.

