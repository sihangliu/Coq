Require Export Induction.
Module Natlist.
  Inductive natprod :=
    | pair : nat -> nat -> natprod.

  Check (pair 3 5).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.
  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Compute (fst (pair 2 3)).
  Compute (snd (pair 2 3)).

  Notation "( x , y )" := (pair x y).
  Compute (fst (2, 3)).
  Compute (snd (2, 3)).

  
