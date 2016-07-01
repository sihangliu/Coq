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

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

  Check [1; 2; 3]  ++ [2; 3; 4].
  Example test_app1 : [ 1 ; 2 ; 3 ] ++ [ 4 ; 5 ] = [ 1 ; 2 ; 3 ; 4 ; 5 ].
  Proof. auto. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: _ => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | _ :: t => t
    end.

  Example test_hd1: hd 0 [1;2;3] = 1.
  Proof. reflexivity. Qed.
  Example test_hd2: hd 0 [] = 0.
  Proof. reflexivity. Qed.
  Example test_tl: tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => if beq_nat h O then nonzeros t else h :: nonzeros t
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. auto. Qed.

  
