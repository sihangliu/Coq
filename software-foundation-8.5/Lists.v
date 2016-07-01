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

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
      if evenb h then oddmembers t else h :: oddmembers t
    end.

  Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. simpl. reflexivity. Qed.

  Fixpoint countoddmembers (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => if evenb h then countoddmembers t else S (countoddmembers t)
    end.

  
  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. auto. Qed.

  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  Proof. auto. Qed.

  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. auto. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    end.
  
  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. auto. Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. auto. Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. auto. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => if beq_nat h v then S (count v t) else count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. auto. Qed.

  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. auto. Qed.

  Definition sum : bag -> bag -> bag :=
    app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. auto. Qed.

  Definition add (v:nat) (s:bag) : bag :=
    app [v] s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. auto. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.

  Check beq_nat.
  Definition member (v:nat) (s:bag) : bool :=
    negb (Basics.beq_nat O (count v s)).

  Example test_member1: member 1 [1;4;1] = true.
  Proof. auto. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. auto. Qed.

  Fixpoint remove_one (v : nat) (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => if Basics.beq_nat h v then t else h :: remove_one v t
    end.
             
  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. auto. Qed.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. auto. Qed.

  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. auto. Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if Basics.beq_nat h v then remove_all v t else h :: remove_all v t
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. auto. Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. auto. Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. auto. Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. auto. Qed.

  
  
      
                    
    
    
