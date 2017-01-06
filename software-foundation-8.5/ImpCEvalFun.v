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
Qed.

