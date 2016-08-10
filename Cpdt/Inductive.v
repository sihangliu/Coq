Require Import CpdtTactics.


Check (fun x : nat => x).
Check I.
Check (fun _ : False => I).

Program Definition safe_sub (a b : nat) (pf : a >= b) := a - b.

Lemma safe : 3 >= 2.
  Require Import Omega. omega.
Qed.


Check False.

Inductive unit : Set :=
| tt : unit.

Check unit_ind.

Inductive type : Set :=
| a : type
| b : type
| c : type -> type.

Check type_ind.

Inductive Empty_set : Set :=.

Theorem from_false_you_can_prove_anything : Empty_set -> 2 + 2 = 5.
Proof.
  intros; inversion H.
Qed.

Print from_false_you_can_prove_anything.

Definition e2u (e : Empty_set) : unit :=
  match e with end.

Check e2u.

Theorem n_plus_O : forall n : nat, n + O = n.
Proof.
  Check nat_ind.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conj : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conj f1 f2 => (pformulaDenote f1) /\ (pformulaDenote f2)
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And x y => (formulaDenote x) /\ (formulaDenote y)
  | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq n1 n2 => Eq n2 n1
  | And x y => And (swapper y) (swapper x)
  | Forall f' => Forall (fun n => swapper (f' n))
  end.

Theorem swapper_preserv_truth : forall f : formula,
    formulaDenote f ->  formulaDenote (swapper f).
Proof.
  induction f; crush.
Qed.                              

Check formula_ind.

Print nat_ind.
Print nat_rect.

Fixpoint nat_rect' (P : nat -> Type) (H0 : P 0)
         (Hn : forall n,  P n -> P (S n)) (n : nat) :=
  match n return (P n) with
  | 0 => H0
  | S n' => Hn n' (nat_rect' P H0 Hn n')
  end.

Section formula_ind'.
  Variable P : formula -> Prop.
  Hypothesis Eq_case : forall n1 n2 : nat, P (Eq n1 n2).
  Hypothesis And_case : forall f1 f2 : formula,
      P f1 -> P f2 -> P (And f1 f2).
  Hypothesis Forall_case : forall (f : nat -> formula),
      (forall n : nat, P (f n)) -> P (Forall f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
    | Eq n1 n2 => Eq_case n1 n2
    | And f1 f2 => And_case f1 f2 (formula_ind' f1)  (formula_ind' f2)
    | Forall f' => Forall_case f' (fun n => formula_ind' (f' n))
    end.
End formula_ind'.

Print formula_ind'.

Print and.
Check (1 = 2).
Check (conj eq_refl eq_refl).

Inductive False : Prop :=.
Theorem false_imp : False -> 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Theorem or_comm' : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  tauto.
Qed.

Theorem arith_comm : forall (X : Type) (ls1 ls2 : list X),
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6 ->
    length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
Proof.
  intuition. Require Import List. SearchAbout (length (_ ++ _) = _).
  rewrite app_length. tauto.
Qed.

Check (ex_intro (fun x => x >= 3) 3).
Print ex.

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  |Cons : A -> stream -> stream.

End stream.

CoFixpoint zeros : stream nat := Cons nat 0 zeros.
CoFixpoint true_false : stream bool := Cons _ true false_true
with false_true : stream bool := Cons _ false true_false.

CoFixpoint map (A B : Type) (f : A -> B) (l : stream A) : stream B :=
  match l with
  | Cons _ h t => Cons _ (f h) (map _ _ f t)
  end.

Check (sig (fun x => x = 3)).

Print pred.

Extraction pred.

Lemma zgtz : 0 > 0 -> False.
Proof. crush. Qed.
  
Program Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
  | O => fun pf : 0 > 0 => match zgtz pf with end
  | S n' => fun _ => n'
  end.

Program Definition two_gt0 : 2 > 0.
Proof. crush. Qed.

Compute (pred_strong1 2 two_gt0).
Print two_gt0.

Extraction pred_strong1.

Print sig.
Print ex.

Locate "{ _ : _ | _ }".

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
  | exist _ O pf => match zgtz pf with end
  | exist _ (S n') _ => n'
  end.


Compute (pred_strong2 (exist _ 2 two_gt0)).

Extraction pred_strong2.

Program Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m}.
Proof.
  destruct s. exists (pred x). simpl.
  SearchAbout (S (pred _) = _).
  rewrite Nat.succ_pred_pos. auto.
  auto.
Qed.

Print pred_strong3.
Eval compute in (pred_strong3 (exist _ 2 two_gt0)).

Definition pred_strong4 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
  | exist _ 0 pf => match zgtz pf with end
  | exist _ (S n') pf => exist _ n' (eq_refl _)
  end.

Eval compute in (pred_strong4 (exist _ 2 two_gt0)).


