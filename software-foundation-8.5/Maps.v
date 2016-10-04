Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1, id2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_refl : forall id, true = beq_id id id.
Proof.
  intros H. destruct H.
  simpl. induction n.
  simpl. reflexivity.
  simpl. auto.
Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
    beq_id id1 id2 = true <-> id1 = id2.
Proof.
  destruct id1, id2. simpl. split. intros H.
  SearchAbout (( _ =? _ ) = true).
  specialize (beq_nat_true n n0 H); intros.
  rewrite H0. reflexivity.

  intros H. inversion H.
  SearchAbout (( _ =? _ ) = true).
  apply Nat.eqb_eq. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
    beq_id x y = false <-> x <> y.
Proof.
  destruct x, y. split. simpl.
  intros H. unfold not. intros H1.
  inversion H1. SearchAbout (( _ =? _ ) = false).
  specialize (beq_nat_false n n0 H); intros. unfold not in H0.
  apply H0. assumption.

  intros H. simpl. unfold not in H.
  SearchAbout (( _ =? _ ) = false ).
  apply Nat.eqb_neq. unfold not; intros. apply H.
  apply f_equal. assumption.
Qed.

Theorem false_beq_id : forall x y : id,
    x <> y -> beq_id x y = false.
Proof.
  intros x y H. rewrite beq_id_false_iff.
  assumption.
Qed.

Definition total_map (A : Type) := id -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

Example update_example1 : examplemap (Id 0) = false.
Proof. compute. reflexivity. Qed.

Lemma t_apply_empty: forall A x v, @t_empty A v x = v.
Proof.
  intros A x v. compute. reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v. unfold t_update.
  rewrite <- beq_refl. reflexivity.
Qed.


Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
    = t_update m x v2.
Proof.
  intros A m v1 v2 x. unfold t_update.
  apply functional_extensionality_dep. intros x0.
  destruct (beq_id x x0) eqn:H. reflexivity.
  reflexivity.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros x y.
  apply iff_reflect. split.
  intros. rewrite H. symmetry. apply beq_refl.

  intros H. specialize (beq_id_true_iff x y); intros.
  destruct H0. apply H0. assumption.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
    t_update m x (m x) = m.
Proof.
  intros X x m. unfold t_update.
  apply functional_extensionality_dep. intros x0.
  destruct (beq_id x x0) eqn: Ht.
  apply f_equal. specialize (beq_id_true_iff x x0); intros.
  destruct H. apply H. auto.
  auto.
Qed.

Theorem t_update_permute :
  forall (X:Type) v1 v2 x1 x2 (m : total_map X),
    x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
    = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m H. unfold t_update.
  apply functional_extensionality_dep. intros x.
  destruct (beq_id x1 x) eqn:Ht.
  destruct (beq_id x2 x) eqn:Ht1.
  specialize (beq_id_true_iff x1 x); intros. destruct H0.
  specialize (beq_id_true_iff x2 x); intros. destruct H2.
  specialize (H0 Ht). specialize (H2 Ht1). congruence. reflexivity.
  reflexivity.
Qed.


Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
           (x : id) (v : A) :=  t_update m x (Some v).

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
    x1 <> x2 ->
    (t_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m H. unfold not in H.
  unfold t_update. destruct (beq_id x1 x2) eqn:Ht.
  specialize (beq_id_true_iff x1 x2); intros.
  destruct H0.  specialize (H0 Ht). congruence.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
    x2 <> x1 ->  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                           (m : partial_map X),
    x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
    = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.
