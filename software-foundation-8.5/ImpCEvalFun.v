Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import Imp.
Require Import Maps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | l ::= a1 =>
    t_update st l (aeval st a1)
  | c1 ;; c2 =>
    let st' := ceval_step1 st c1 in
    ceval_step1 st' c2
  | IFB b THEN c1 ELSE c2 FI =>
    if (beval st b) then ceval_step1 st c1
    else ceval_step1 st c2
  | WHILE b1 DO c END => st
  end.


Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | 0 => empty_state
  | S i' =>
       match c with
       | SKIP => st
       | l ::= a1 =>
         t_update st l (aeval st a1)
       | c1 ;; c2 =>
         let st' := ceval_step2 st c1 i' in
         ceval_step2 st' c2 i' 
       | IFB b THEN c1 ELSE c2 FI =>
         if (beval st b) then ceval_step2 st c1 i'
         else ceval_step2 st c2 i'
       | WHILE b1 DO c1 END =>
         if (beval st b1) then
           let st' := ceval_step2 st c1 i' in
           ceval_step2 st' c i'
         else st
       end 
  end.


Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | 0 => None
  | S i' =>
    match c with
    | SKIP => Some st
    | l ::= a1 =>
      Some (t_update st l (aeval st a1))
    | c1;; c2 =>
      match ceval_step3 st c1 i' with
      | None => None
      | Some st' => ceval_step3 st' c2 i'
      end
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b) then ceval_step3 st c1 i'
      else ceval_step3 st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1) then
        match ceval_step3 st c1 i' with
        | None => None
        | Some st' => ceval_step3 st' c i'
        end
      else Some st
    end
  end.


Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
      | Some x => e2
      | None => None
      end)
       (right associativity, at level 60).


        
      

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
      match c with
      | SKIP =>
             Some st
      | l ::= a1 =>
          Some (t_update st l (aeval st a1))
      | c1 ;; c2 =>
           LETOPT st' <== ceval_step st c1 i' IN
           ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
            if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
              if (beval st b1)
              then LETOPT st' <== ceval_step st c1 i' IN
                          ceval_step st' c i'
              else Some st
      end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.



Definition pup_to_n : com :=
  Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
          Y ::= APlus (AId Y) (AId X);;
    X ::= AMinus (AId X) (ANum 1)
      END.

Example pup_to_n_1 :
  test_ceval (t_update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition peven : com :=
  Z ::= AId X;;
    WHILE BNot (BLe (AId Z) (ANum 1)) DO
        Z ::= AMinus (AId Z) (ANum 2)
    END.


Theorem ceval_step_ceval : forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    c / st \\ st'.
Proof.
  intros c st st' [i E].
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i.
  intros c st st' H. inversion H.
  intros c st st' H.
  destruct c; simpl in H; inversion H; subst; clear H.
  apply E_Skip.
  apply E_Ass. auto.
  destruct (ceval_step st c1 i) eqn:Heqr.
  apply E_Seq with s. apply IHi. assumption.
  apply IHi. assumption. inversion H1.
  destruct (beval st b) eqn: Heqr.
  apply E_IfTrue. auto. apply IHi. assumption.
  apply E_IfFalse. auto. apply IHi. assumption.
  destruct (beval st b) eqn: Heqr.
  destruct (ceval_step st c i) eqn:Heqr1.
  apply E_WhileLoop with s. auto.
  apply IHi. auto.
  apply IHi. auto.
  inversion H1.
  inversion H1.
  apply E_WhileEnd. subst. auto.
  Show Proof.
Qed.


Theorem ceval_step_ceval1 : forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    c / st \\ st'.
Proof.
  induction c; intros st st' [n E]; inversion E; subst; clear E; destruct n; inversion H0; subst.
  apply E_Skip.
  apply E_Ass. auto.
  destruct (ceval_step st c1 n) eqn:Ht.
  apply E_Seq with s.
  apply IHc1. exists n. auto. apply IHc2. exists n. auto.
  inversion H1.
  destruct (beval st b) eqn:Ht.
  apply E_IfTrue. auto. apply IHc1. exists n. auto.
  apply E_IfFalse. auto. apply IHc2. exists n. auto.
  destruct (beval st b) eqn: Heqr.
  destruct (ceval_step st c n) eqn:Heqr1.
  apply E_WhileLoop with s. auto.
  apply IHc. exists n. auto.
  (* upto this point everything is good but now goal is impossible to prove because
     c is not general enough to apply induction hypothesis *)
Abort.

Theorem ceval_step_more : forall i1 i2 st st' c,
    i1 <= i2 ->
    ceval_step st c i1 = Some st' ->
    ceval_step st c i2 = Some st'.
Proof.
  induction i1; intros i2 st st' c H1 H2.
  inversion H2. destruct i2.
  inversion H1. assert (Ht : i1 <= i2) by omega.
  destruct c. simpl in *. assumption.
  simpl in *. assumption.
  simpl in *. destruct (ceval_step st c1 i1) eqn:Heqr.
  apply (IHi1 i2) in Heqr; try assumption.
  rewrite Heqr. apply (IHi1 i2) in H2; try assumption.
  inversion H2.
  simpl in *. destruct (beval st b) eqn:Heqr.
  apply IHi1. assumption.
  assumption. apply IHi1. assumption. assumption.
  simpl in *. destruct (beval st b); try assumption.
  destruct (ceval_step st c i1) eqn:Heqn.
  apply (IHi1 i2) in Heqn; try assumption.
  rewrite Heqn.
  apply (IHi1 i2) in H2. assumption.
  assumption. inversion H2.
Qed.

Theorem ceval__ceval_step: forall c st st',
    c / st \\ st' ->
    exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce. exists 1. auto.
  exists 1. simpl. rewrite H. auto.
  destruct IHHce1. destruct IHHce2.
  exists (1 + x + x0). simpl.
  destruct (ceval_step st c1 (x + x0)) eqn:Ht.
  apply ceval_step_more with (i2 := x + x0) in H.
  rewrite H in Ht. inversion Ht. subst.
  apply ceval_step_more with (i1 := x0). omega.
  assumption. omega.
  apply ceval_step_more with (i2 := x + x0) in H.
  rewrite Ht in H. inversion H. omega.
  destruct IHHce. exists (1 + x). simpl. rewrite H. auto.
  destruct IHHce. exists (1 + x). simpl. rewrite H. auto.
  exists 1. simpl. rewrite H. auto.
  destruct IHHce1. destruct IHHce2.
  exists (1 + x + x0). simpl. rewrite H.
  destruct (ceval_step st c (x + x0)) eqn:Ht.
  apply ceval_step_more with (i2 := x + x0) in H0.
  rewrite H0 in Ht. inversion Ht. subst.
  apply ceval_step_more with (i1 := x0). omega. assumption.
  omega.
  apply ceval_step_more with (i2 := (x + x0)) in H0.
  rewrite H0 in Ht. inversion Ht. omega.
Qed.

