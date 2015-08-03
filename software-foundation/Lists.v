Require Export Induction.

Module NatList.

  Inductive natprod : Type :=
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

  Eval compute in fst (pair 3 5).

  Notation "( x , y )" := (pair x y).
  Eval compute in fst (3, 5).

  Definition fst' (p : natprod) : nat :=
    match p with
      | (x, y) => x
    end.
  Definition snd' (p : natprod) : nat :=
    match p with
      | (x, y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
      | (x, y) => (y, x)
    end.

  Theorem surjective_pairing' : forall (n m : nat),
                                  (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck : forall (p : natprod),
                                       p = (fst p, snd p).
  Proof.
    simpl.
  Abort.

  Theorem surjective_pairing : forall (p : natprod),
                                 p = (fst p, snd p).
  Proof.
    destruct p. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
                              (snd p, fst p) = swap_pair p.
  Proof.
    destruct p. reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
                              fst (swap_pair p) = snd p.
  Proof.
    destruct p. reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Definition mylist1 := 1 :: (2 :: (3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := [1;2;3].

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | O => nil
      | S cnt => n :: repeat n cnt
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
      | nil => O
      | _ :: l' => S (length l')
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
      | nil => l2
      | h :: t => h :: app t l2
    end.

  
  Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
      | nil => default
      | h :: _ => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => t
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
      | O :: t => nonzeros t
      | S n' :: t => S n' :: nonzeros t
    end.

  Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. simpl. reflexivity. Qed.

  SearchAbout evenb.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t =>
        if negb (evenb h) then h :: oddmembers t
        else oddmembers t
    end.

  Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. simpl. reflexivity. Qed.

  
  Fixpoint countoddmembers (l : natlist) : nat :=
    match l with
      | nil => O
      | h :: t =>
        if negb (evenb h) then S (countoddmembers t)
        else countoddmembers t
    end.

  Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
  Proof. simpl. reflexivity. Qed.
  Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof. simpl. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
      | nil, nil => nil
      | nil, h :: t => h :: t
      | h :: t, nil => h :: t
      | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    end.

  Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate4: alternate [] [20;30] = [20;30].                       
  Proof. simpl. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
      | nil => O
      | h :: t =>
        if beq_nat v h then S (count v t)
        else count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. simpl. reflexivity. Qed.

  Definition sum : bag -> bag -> bag := app. 
  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.

  Definition add (v : nat) (s : bag) : bag :=  v :: s.
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.

  Definition member (v:nat) (s:bag) : bool :=
    negb (beq_nat (count v s) O).

  Example test_member1: member 1 [1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
      | nil => nil
      | h :: t =>
        if beq_nat h v then t
        else h :: remove_one v t
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
      | nil => nil
      | h :: t =>
        if beq_nat h v then remove_all v t
        else h :: remove_all v t
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. simpl. reflexivity. Qed.

  
  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s1 with
      | nil => true
      | h :: t =>
        if member h s2 then subset t (remove_one h s2)
        else false
    end.
  SearchAbout member.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

  Theorem nil_app : forall l : natlist, [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem nil_app_right : forall l : natlist, l ++ [] = l.
  Proof.
    induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem tl_length_pred : forall l:natlist,
                             pred (length l) = length (tl l).
  Proof.
    intros l. destruct l as [ | n l'].
    Case "l = nil". reflexivity.
    Case "l = cons n l'". simpl. reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist,
                        (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    induction l1 as [ | n l'].
    Case "l1 = nil". reflexivity.
    Case "l1 = cons n l'".
    simpl. intros l2 l3. rewrite IHl'. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
                         length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    induction l1 as [ | n l].
    Case "l1 = nil". reflexivity.
    Case "l1 = cons n l".
    intros l2. simpl. rewrite IHl. reflexivity.
  Qed.

  Fixpoint snoc (l : natlist) (v : nat) : natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.

  Eval compute in snoc [1; 2; 3] 5.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem rev_length_firsttry : forall l : natlist,
                                  length (rev l) = length l.
  Proof.
    induction l as [ | n' l'].
    Case "l = nil".
    simpl. reflexivity.
    Case "l = cons n' l'".
    simpl. rewrite <- IHl'.
  Abort.

  Theorem length_snoc : forall n : nat, forall l : natlist,
                          length (snoc l n) = S (length l).
  Proof.
    induction l as [ | n' l'].
    Case "l = nil". reflexivity.
    Case "l = cons n' l'".  simpl. rewrite IHl'. reflexivity.
  Qed.

  
  Theorem rev_length : forall l : natlist, length (rev l) = length l.
  Proof.
    induction l as [ | n' l'].
    Case "l = nil". reflexivity.
    Case "l = cons n' l'". simpl.  rewrite length_snoc. rewrite IHl'.
    reflexivity.
  Qed.

  
  Theorem app_nil_end : forall l : natlist,
                          l ++ [] = l.
  Proof.
    induction l as [ | n' l'].
    Case "l = nil". reflexivity.
    Case "l = cons n' l'". simpl. rewrite IHl'. reflexivity.
  Qed.
  
  Lemma snoc_rev : forall ( n : nat ) ( l : natlist ),
    rev ( snoc l n ) = n :: rev l.
  Proof.
  induction l as [ | n' l'].
  Case "l = nil". reflexivity.
  Case "l = cons n' l'". simpl. rewrite IHl'. simpl. reflexivity.
  Qed.


  Theorem rev_involutive : forall l : natlist,
                             rev (rev l) = l.
  Proof.
    induction l.
    Case "l = nil". reflexivity.
    Case "l = cons n l". simpl. rewrite snoc_rev. rewrite IHl. reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
                         l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4. rewrite app_assoc. rewrite app_assoc.
    reflexivity.
  Qed.

  Theorem snoc_append : forall (l:natlist) (n:nat),
                          snoc l n = l ++ [n].
  Proof.
    induction l.
    Case "l = nil". reflexivity.
    Case "l = cons n l". simpl. intros n0. rewrite IHl. reflexivity.
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
                        rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    induction l1.
    Case "l1 = nil". simpl. intros l2. rewrite app_nil_end. reflexivity.
    Case "l1 = cons n l".  intros l2. simpl. repeat (rewrite snoc_append).
    rewrite IHl1. rewrite app_assoc. reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
                         nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    induction l1.
    Case "l1 = nil". reflexivity.
    Case "l1 = cons n l". intros l2.
    destruct n.
    SCase "n = O". simpl. rewrite IHl1. reflexivity.
    SCase "n = S n". simpl. rewrite IHl1. reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
      | nil, nil => true
      | _ :: _, nil => false
      | nil, _::_ => false
      | h1 :: t1, h2 :: t2 =>
        andb (beq_nat h1 h2) (beq_natlist t1 t2)
    end.

  
  Example test_beq_natlist1 : beq_natlist nil nil = true.
  Proof. simpl. reflexivity. Qed.
  Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
  Proof. simpl. reflexivity. Qed.

  Theorem beq_natlist_refl : forall l : natlist,
                               true = beq_natlist l l.
  Proof.
    induction l.
    Case "l = nil". reflexivity.
    Case "l = cons n l". simpl. rewrite <- beq_nat_refl.
    simpl. rewrite IHl. reflexivity.
  Qed.

 
  Theorem count_member_nonzero : forall (s : bag),
                                   ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    intros s. simpl. reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
                       ble_nat n (S n) = true.
  Proof.
    induction n.
    Case "n = O". reflexivity.
    Case "n = S n".  simpl. rewrite IHn. reflexivity.
  Qed.

  Theorem remove_decreases_count: forall (s : bag),
          ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    induction s.
    Case "s = nil". reflexivity.
    Case "s = cons n l".
    destruct n.
    SCase "n = O". simpl.  apply ble_n_Sn.
    SCase "n = S n". simpl. assumption.
  Qed.

  Theorem rev_injective : forall l1 l2 : natlist,
                            rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H. rewrite <- rev_involutive.
    rewrite <- H. rewrite rev_involutive. reflexivity.
  Qed.

  Fixpoint index_bad (n : nat) (l : natlist) : nat :=
    match l with
      | nil => 42 (* arbitrary! *)
      | a :: l' => match beq_nat n O with
                     | true => a
                     | false => index_bad (pred n) l'
                   end
    end.

  
  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint index (n : nat) (l : natlist) : natoption :=
    match l with
      | nil => None
      | a :: l' => match beq_nat n O with
                     | true => Some a
                     | false => index (pred n) l'
                   end
    end.

  Example test_index1 : index 0 [4;5;6;7] = Some 4.
  Proof. reflexivity. Qed.
  Example test_index2 : index 3 [4;5;6;7] = Some 7.
  Proof. reflexivity. Qed.
  Example test_index3 : index 10 [4;5;6;7] = None.
  Proof. reflexivity. Qed.

  Fixpoint index' (n : nat) (l : natlist) : natoption :=
    match l with
      | nil => None
      | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
    end.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
      | Some n' => n'
      | None => d
    end.

  Definition hd_opt (l : natlist) : natoption :=
    match l with
      | nil => None
      | h :: t => Some h
    end.

  Example test_hd_opt1 : hd_opt [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_opt2 : hd_opt [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_opt3 : hd_opt [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
       hd default l = option_elim default (hd_opt l).
  Proof.
    induction l.
    Case "l = nil". reflexivity.
    Case "l = cons n l". intros default. simpl. reflexivity.
  Qed.

  Module Dictionary.

    Inductive dictionary : Type :=
    | empty : dictionary
    | record : nat -> nat -> dictionary -> dictionary.

    Eval compute in record 3 2 (record 2 2 empty).

    Definition insert (key value : nat) (d : dictionary) : dictionary :=
      (record key value d).

    Fixpoint find (key : nat) (d : dictionary) : natoption :=
      match d with
        | empty => None
        | record k v d' =>
          if (beq_nat key k) then (Some v)
          else (find key d')
      end.

    Theorem dictionary_invariant1' :
      forall (d : dictionary) (k v: nat), (find k (insert k v d)) = Some v.
    Proof.
      induction d.
      Case "d = empty". simpl. intros k v. rewrite <- beq_nat_refl. reflexivity.
      Case "d = record k v d". intros k v. simpl. rewrite <- beq_nat_refl.
      reflexivity.
    Qed.

    Theorem dictionary_invariant2' :
      forall (d : dictionary) (m n o: nat),
        beq_nat m n = false -> find m d = find m (insert n o d).
    Proof.
      intros d m n o H. simpl. rewrite H. reflexivity.
    Qed.

    
