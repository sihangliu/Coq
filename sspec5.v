Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Section Schulze.

(* type of candidates *)
Variable cand: Type.

Require Import ZArith.
(* assuming that link strength has already been calculated *)

(* links with strength >= n measured by margin *)
Definition margin (t: cand -> cand -> Z) (n: Z) : cand -> cand -> Prop :=
  fun c d => (t c d - t d c >= n)%Z.
  
(* transitive closure of a relation *)
Inductive path (r: cand -> cand -> Prop) : cand -> cand -> Type :=
  psimp: forall c d, r c d -> path r c d
| pconc: forall c d e, r c d -> path r d e -> path r c e.

(* existence of a path of strength >= n relative to given tally *)
Definition strong (t: cand -> cand -> Z) (n: Z) (a b: cand) : Type :=
  path (margin t n) a b.

(* non-existence of a path with strength >= n *)
(* operator generating the complement of the trans. closure of r0 as gfp *)
Definition W (r0: cand -> cand -> Prop) (r: cand -> cand -> Prop) : cand -> cand -> Prop :=
  fun x z =>  ~ (r0 x z) /\ forall y, r0 x y -> r y z.

(* co-closed relations *)
Definition co_closed (r0 r: cand -> cand -> Prop) := forall a b, r a b -> (W r0 r) a b.

Inductive npath (r0: cand -> cand -> Prop) : cand -> cand -> Type :=
  nyet : forall  a b: cand, forall r: cand -> cand -> Prop, co_closed r0 r -> r a b -> npath r0 a b.

Definition nstrong (t: cand -> cand -> Z) (n:  Z) (a b: cand) : Type :=
  npath (margin t n) a b.

(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.



Section Symmetric_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive symprod : A * B -> A * B -> Prop :=
    | left_sym (x x':A) : leA x x' -> forall y:B, symprod (x, y) (x', y)
    | right_sym (y y':B) : leB y y' -> forall x:A, symprod (x, y) (x, y').

End Symmetric_Product.

Inductive Pf (t: cand -> cand -> Z) (l: list cand): Type :=
  win: forall c: cand,
  (In c l -> forall d: cand, existsT n,  (strong t n c d * nstrong t n d c)) -> 
  Pf t l.
End Schulze.

Inductive Arc : nat -> nat -> Set :=
  Adj x y :  Arc x y.

Inductive Path : nat -> nat -> nat -> Prop :=
| Unit x y z : Arc x y -> Path x y z
| Multi x y z w v : Path x y w -> Path y z v -> Path x z (min w v).

Check Arc 1 2.
Check (Unit 1 2 3 (Adj 1 2)).
Check (Multi _ _ _ _ _ (Unit 1 2 5 (Adj 1 2)) (Unit 2 3 6 (Adj 2 3))).

Section MergeSort.
  Require Import List.
  Require Program.Wf.
  Require Omega.

  Variable A : Type.
  Variable le : A -> A -> Prop. 
  Hypothesis le_trans : forall (x y z : A),  le x y -> le y z -> le x z.
  Hypothesis le_total : forall (x y : A), le x y \/ le y x.
  Variable le_dec : forall (x y : A), {le x y} + {~le x y}.

  Lemma le_refl : forall (x : A), le x x.
  Proof.
    intros. destruct (le_total x x); auto.
  Qed.

  Lemma le_not : forall (x y : A), ~le x y -> le y x.
  Proof.
    unfold not; intros. destruct (le_total x y).
    apply H in H0; inversion H0.
    trivial.
  Qed.

  Inductive Sorted : list A -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_cons hd tl : (forall x, In x tl -> le hd x)-> Sorted tl -> Sorted (hd :: tl).

  Remark Sorted_1 : forall x : A, Sorted (x :: nil).
  Proof.
    intros. constructor; intros.
    inversion H. constructor.
  Qed.

  Remark Sorted_2 : forall x y : A, le x y -> Sorted (x :: y :: nil). 
  Proof.
    intros. constructor.
    intros.  simpl in H0. destruct H0. subst x0. auto. contradiction.
    apply Sorted_1.
  Qed.

  Definition eqv (x y : A) : bool :=
    if le_dec x y then if le_dec y x then true else false
    else false.

  Lemma eqv_spec :
    forall x y, eqv x y = true <-> le x y /\ le y x.
  Proof.
    intros. unfold eqv.
    destruct (le_dec x y).
    destruct (le_dec y x). tauto.
    intuition congruence.
    intuition congruence.
  Qed.

  Definition Stable (l l' : list A) : Prop :=
    forall x : A, filter (eqv x) l = filter (eqv x) l'.

  Lemma Stable_refl : forall l : list A, Stable l l.
  Proof.
    simple induction l.
    - unfold Stable. tauto.
    - unfold Stable. intros. tauto.
  Qed.

  Lemma Stable_trans : forall l1 l2 l3 : list A,
      Stable l1 l2 -> Stable l2 l3 -> Stable l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (eqv x) l2); auto.
  Qed.

  Remark filter_app :
    forall (A : Type) (l1 l2 : list A) (f : A -> bool),
      filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    simple induction l1; intros; simpl. auto.
    destruct (f a); simpl. f_equal; auto. auto.
  Qed.

  Lemma Stable_app :
    forall l l' m m', Stable l l' -> Stable m m' -> Stable (l ++ m) (l' ++ m').
  Proof.
    intros; red; intros. repeat rewrite filter_app.
    rewrite H, H0; trivial.
  Qed.

  Lemma Stable_swap :
    forall (a b : A) (l : list A), ~le a b -> Stable (a :: b :: l) (b :: a :: l). 
  Proof.
    intros; red; intros. simpl.
    case_eq (eqv x a); intros ; auto.
    case_eq (eqv x b); intros; auto.
    rewrite eqv_spec in H0, H1.
    destruct H0, H1. elim H. (* exfalso; apply H *)
    eauto.
  Qed.

  Remark filter_empty :
    forall (A : Type) (l : list A) (f : A -> bool),
      (forall x : A, In x l -> f x = false) -> filter f l = nil.
  Proof.
    induction l; simpl; intros.
    eauto.
    replace (f a) with false. apply IHl. auto. symmetry. auto.
  Qed.

  Lemma Stable_cons_app:
    forall (a : A) (l l1 l2 : list A),
      Stable l (l1 ++ l2) ->
      (forall b : A, In b l1 -> ~(le b a /\ le a b)) -> Stable (a :: l) (l1 ++ a :: l2).
  Proof.
    intros; red; intros. rewrite filter_app. simpl.
    generalize (H x). rewrite filter_app.
    case_eq (eqv x a); intro; auto.
    rewrite (filter_empty _ l1 (eqv x)); simpl. intros. congruence.
    intros. case_eq (eqv x x0); intros; auto.
    elim (H0 x0). trivial.
    rewrite eqv_spec in H1, H3. destruct H1, H3.
    split; eapply le_trans; eauto.
  Qed.

  Lemma Stable_cons_app' :
    forall a b l l1 l2,
      Stable l (b :: l1 ++ l2) ->
      Sorted (b :: l1) -> ~le b a ->
      Stable (a :: l) (b :: l1 ++ a :: l2).
  Proof.
    intros. change (Stable (a :: l) ((b :: l1) ++ a :: l2)).
    apply Stable_cons_app. simpl; auto.
    intros. simpl in H2. destruct H2. subst b0. tauto.
    inversion H0. subst. red; intros [P Q]. elim H1. apply le_trans with b0; auto.
  Qed.

  Lemma filter_sublist :
    forall (A : Type) (x : A) (f : A -> bool) (l l1' l2' : list A),
      filter f l = l1' ++ x :: l2' ->
      exists l1, exists l2, l = l1 ++ x :: l2 /\ filter f l1 = l1' /\ filter f l2 = l2'.
  Proof.
    induction l; intros until l2'; simpl.
    intro. destruct l1'; simpl in H; discriminate.
    case_eq (f a); intros.
    destruct l1'; simpl in H0; injection H0; clear H0; intros.
    subst x. exists (@nil A0); exists l. auto.
    subst a0. destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. congruence. auto.
    destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. auto. auto.
  Qed.

  Lemma Stable_decomp:
    forall l l',
      Stable l l' ->
      forall l1 x l2 y l3,
        l = l1 ++ x :: l2 ++ y :: l3 ->
        le x y -> le y x ->
        exists l1', exists l2', exists l3', l' = l1' ++ x :: l2' ++ y :: l3'.
  Proof.
    intros.
    generalize (H x). subst l. rewrite filter_app. simpl.
    rewrite filter_app. simpl.
    assert (eqv x x = true).
    unfold eqv.
    destruct (le_dec x x). auto. elim n. apply le_refl.
    rewrite H0; clear H0.
    assert (eqv x y = true).
    unfold eqv. destruct (le_dec x y); try contradiction.
    destruct (le_dec y x); try contradiction. auto.
    rewrite H0; clear H0.
    intro.
    destruct (filter_sublist _ _ _ _ _ _ (sym_equal H0)) as [m1 [m2 [P [Q R]]]].
    destruct (filter_sublist _ _ _ _ _ _ R) as [m3 [m4 [S [T U]]]].
    exists m1; exists m3; exists m4. congruence.
  Qed.


  
End MergeSort.
