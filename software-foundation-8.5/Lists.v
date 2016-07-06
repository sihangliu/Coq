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

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | nil => true
    | h :: t =>
      if member h s2 then subset t (remove_one h s2)
      else false
    end.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

  Theorem nil_app : forall l : natlist,
      nil ++ l = l.
  Proof. auto. Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tl l).
  Proof.
    intros l. induction l.
    + auto.
    + simpl. reflexivity.  
  Qed.

 
  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1.  induction l1.
    {
      intros l2 l3. auto.
    }
    {
      intros l2 l3. simpl. rewrite <- IHl1. reflexivity.
    }
  Qed.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  
    
  Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l. induction l.
    + auto.
    + simpl.
      assert (H : forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2).
      {
        intros l1. induction l1.
        + auto.
        + intros l2. simpl. rewrite IHl1.
          auto.
      }
      rewrite H. simpl. rewrite IHl.
      rewrite plus_comm. simpl. reflexivity.
  Qed.

  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    intros l. induction l.
    + auto.
    + simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intros l. induction l.
    + auto.
    + simpl.
      assert (H : forall (n : nat) (l : natlist) , rev (l ++ [n]) = n :: rev l).
      {
        intros n0 l0. induction l0.
        + auto.
        + simpl. rewrite IHl0. simpl. reflexivity.
      }
      rewrite H. rewrite IHl.
      reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite app_assoc. rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1. induction l1.
    + reflexivity.
    + intros l2. destruct n.
      {
        simpl. rewrite IHl1. reflexivity.
      }
      {
        simpl. rewrite IHl1. reflexivity.
      }
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | nil, _ | _, nil => false
    | h1 :: t1, h2 :: t2 => Basics.beq_nat h1 h2 && beq_natlist t1 t2
    end.

  Example test_beq_natlist1 :
    (beq_natlist nil nil = true).
  Proof. auto. Qed.

   Example test_beq_natlist2 :
     beq_natlist [1;2;3] [1;2;3] = true.
   Proof. auto. Qed.
  
    
    Example test_beq_natlist3 :
      beq_natlist [1;2;3] [1;2;4] = false.
    Proof. auto. Qed.

    Theorem beq_natlist_refl : forall l:natlist,
        true = beq_natlist l l.
    Proof. intros l. induction l.
           + auto.
           + simpl. rewrite <- IHl.
             assert (forall n : nat, Basics.beq_nat n n = true).
             {
               intros n0. induction n0.
               + auto.
               + simpl. rewrite IHn0. reflexivity.
             }
             rewrite H. reflexivity.
    Qed.

    Theorem count_member_nonzero : forall (s : bag),
        Basics.leb 1 (count 1 (1 :: s)) = true.
    Proof.
      intros s. induction s.
      + auto.
      + simpl. reflexivity.
    Qed.

    Theorem ble_n_Sn : forall n,
        Basics.leb n (S n) = true.
    Proof.
      intros n. induction n as [| n' IHn'].
      - simpl. reflexivity.
      - simpl. rewrite IHn'. reflexivity.
    Qed.

    Theorem remove_decreases_count: forall (s : bag),
        Basics.leb (count 0 (remove_one 0 s)) (count 0 s) = true.
    Proof.
      intros s. induction s.
      + auto.
      + simpl. destruct n.
        {
          simpl. rewrite ble_n_Sn. reflexivity.
        }
        {
          simpl. rewrite IHs. reflexivity.
        }
    Qed.

    Theorem rev_injective : forall l1 l2 : natlist,
        rev l1 = rev l2 -> l1 = l2.
    Proof.
      intros l1 l2 H.
      rewrite <- rev_involutive.
      rewrite <- H. rewrite rev_involutive.
      reflexivity.
    Qed.

    Inductive natoption : Type :=
    | Some : nat -> natoption
    | None : natoption.

    Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
      match l with
      | nil => None
      | a :: l' => match Basics.beq_nat n O with
                  | true => Some a
                  | _ => nth_error l' (pred n)
                  end
      end.

    Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
    Proof. auto. Qed.

    Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
    Proof. auto. Qed.

    Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
    Proof. auto. Qed.

    Definition option_elim (d : nat) (o : natoption) : nat :=
      match o with
      | Some a => a
      | None => d
      end.

    Definition hd_error (l : natlist) : natoption :=
      match l with
      | nil => None
      | h :: t => Some h
      end.

    Example test_hd_error1 : hd_error [] = None.
    Proof. auto. Qed.

    Theorem prove_absurd : forall p : Prop,
        p = True -> p = False -> False.
    Proof.
      intros p H1 H2.
      rewrite <- H2. rewrite H1.
      auto.
    Qed.

    Example test_hd_error2 : hd_error [1] = Some 1.
    Proof. auto. Qed.

    Example test_hd_error3 : hd_error [5;6] = Some 5.
    Proof. auto. Qed.

    Theorem option_elim_hd : forall (l:natlist) (default:nat),
        hd default l = option_elim default (hd_error l).
    Proof.
      intros l N. induction l.
      + simpl. reflexivity.
      + simpl. reflexivity.
    Qed.
End Natlist.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) : bool :=
  match x1, x2 with
  | Id n1, Id n2 => Basics.beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros x. induction x.
  simpl. assert (H : Basics.beq_nat n n = true).
  { induction n.
    + auto.
    + auto.
  }
  rewrite H. auto.
Qed.

Module PartialMap.
  Import Natlist.
  Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

  Definition update (d : partial_map) (key : id) (value : nat) : partial_map :=
    record key value d.

  Fixpoint find (key : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record k v d' =>
      if beq_id k key then Some v
      else find key d'
    end.

  Theorem update_eq : forall (d : partial_map) (k : id) (v: nat),
      find k (update d k v) = Some v.
  Proof.
    intros d k v. simpl.
    assert (H : beq_id k k = true).
    {
      destruct k.
      simpl. assert (H1 : Basics.beq_nat n n = true).
      {
        induction n.
        + auto.
        + auto.
      }
      rewrite H1.
      reflexivity.
    }
    rewrite H. reflexivity.
  Qed.

  Lemma not_equal : forall m n : nat ,
      Basics.beq_nat n m = false -> Basics.beq_nat m n = false.
  Proof.
    intros m. induction m.
    {
      intros n H. induction n.
      + auto.
      + auto.
    }
    {
      intros n. induction n.
      + simpl. intro H. reflexivity.
      + simpl. intros H. apply IHm in H.
        assumption.
    }
  Qed.       

  Theorem update_neg : forall (d : partial_map) (m n : id) (o : nat),
      beq_id m n = false -> find m (update d n o) = find m d.
  Proof.
    intros d m n o H. simpl.
    destruct m. destruct n. simpl in H. simpl.
    rewrite not_equal.
    + reflexivity.
    + assumption.
  Qed.
End PartialMap.  

(* Zero because there is not possible to construct any element of type baz *)

