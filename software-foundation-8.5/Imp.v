Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => aeval a1 + aeval a2
    | AMinus a1 a2 => aeval a1 - aeval a2
    | AMult a1 a2 => aeval a1 * aeval a2
    end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. compute. auto. Qed.

  Print test_aeval1.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq b1 b2 => beq_nat (aeval b1) (aeval b2)
    | BLe b1 b2 => leb (aeval b1) (aeval b2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum a => ANum a
    | APlus (ANum 0) e2 => e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.


  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a. induction a.
    - auto.
    - destruct a1.
      + destruct n.
        * simpl. auto.
        * simpl. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
    - simpl. auto.
    - simpl. auto.
  Qed.

  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof. try reflexivity. Qed.

  Theorem silly2 : forall (P : Prop), P -> P.
  Proof.
    intros P Hp.
    try reflexivity.     
    apply Hp.
  Qed.

  Lemma foo : forall n, leb 0 n = true.
  Proof.
    intros n. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.

  Lemma foo' : forall n, leb 0 n = true.
  Proof.
    intros n. destruct n; simpl; reflexivity.
  Qed.

  Theorem optimize_0plus_sound': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    reflexivity.
    destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    destruct n; simpl; rewrite <- IHa2; reflexivity.
  Qed.

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try (left; reflexivity)).
  Qed.


  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq b1 b2 => BEq (optimize_0plus b1) (optimize_0plus b2)
    | BLe b1 b2 => BLe (optimize_0plus b1) (optimize_0plus b2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  
  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    assert (Ht : forall a1, aeval (optimize_0plus a1) = aeval a1)
      by apply optimize_0plus_sound.
    intros b. induction b.
    - reflexivity.
    - reflexivity.
    - simpl. repeat (rewrite Ht). reflexivity.
    - simpl. repeat (rewrite Ht). reflexivity.
    - simpl. rewrite IHb. reflexivity.
    - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  Qed.

  
  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega.
  Qed.

  Module aevalR_first_try.

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum n : aevalR (ANum n) n
    | E_APlus e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult e1 e2 n1 n2 : aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

    Notation "e '\\' n" := (aevalR e n) (at level 50, left associativity)
                           : type_scope.
  End aevalR_first_try.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n : (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

  Theorem aeval_iff_aevalR : forall a n, (a \\ n) <-> aeval a = n.
  Proof.
    intros a n. split. intros H.
    induction H; auto; simpl; rewrite IHaevalR1; rewrite IHaevalR2; auto.
    generalize dependent n.
    induction a; simpl; intros; subst; constructor; try apply IHa1; try apply IHa2; auto.
  Qed.

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> bevalR (BEq e1 e2) (beq_nat n1 n2)
  | E_BLe e1 e2 n1 n2 : (e1 \\ n1) -> (e2 \\ n2) -> bevalR (BLe e1 e2) (leb n1 n2)
  | E_BNot e b : bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd e1 e2 b1 b2 : bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2).

  Theorem beval_iff_bevalR : forall a n, (bevalR a n) <-> beval a = n.
  Proof.
    intros a n. split. intros H.
    induction H. auto. auto.
    simpl. specialize (aeval_iff_aevalR e1 n1); intros. destruct H1.
    specialize (aeval_iff_aevalR e2 n2); intros. destruct H3.
    pose proof H1 H. pose proof H3 H0. auto.
    simpl. specialize (aeval_iff_aevalR e1 n1); intros. destruct H1.
    specialize (aeval_iff_aevalR e2 n2); intros. destruct H3.
    pose proof H1 H. pose proof H3 H0. auto.
    simpl. rewrite IHbevalR. auto.
    simpl. rewrite IHbevalR1, IHbevalR2. auto.

    generalize dependent n.
    induction a; simpl; intros; subst.
    apply E_BTrue. apply E_BFalse.
    apply E_BEq. apply aeval_iff_aevalR. reflexivity.
    apply aeval_iff_aevalR. reflexivity.
    constructor. apply aeval_iff_aevalR. reflexivity.
    apply aeval_iff_aevalR. reflexivity.
    constructor. apply IHa. reflexivity.
    constructor. apply IHa1. reflexivity.
    apply IHa2. reflexivity.
  Qed.

  
End AExp.

Module aevalR_division.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.


  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n : (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (AMult e1 e2) \\ (n1 * n2)
  | E_ADiv e1 e2 n1 n2 n3 : e1 \\ n1 -> e1 \\ n2 -> n2 > 0 -> (mult n2 n3 = n1)
                            -> (ADiv e1 e2) \\ n3
  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aexp : Type :=
  | AAny : aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


  Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) : AAny \\ n
  | E_ANum (n : nat) : (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult e1 e2 n1 n2 : e1 \\ n1 -> e2 \\ n2 -> (AMult e1 e2) \\ (n1 * n2)
  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Definition empty_state := t_empty 0.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus e1 e2 => aeval st e1 + aeval st e2
  | AMinus e1 e2 => aeval st e1 - aeval st e2
  | AMult e1 e2 => aeval st e1 * aeval st e2
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq e1 e2 => beq_nat (aeval st e1) (aeval st e2)
  | BLe e1 e2 => leb (aeval st e1) (aeval st e2)
  | BNot e => negb (beval st e)
  | BAnd e1 e2 => andb (beval st e1) (beval st e2)
  end.


Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof.
  compute. reflexivity.
Qed.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | x ::= a1 => t_update st x (aeval st a1)
  | c1 ;; c2 =>
    let st' := ceval_fun_no_while st c1 in
    ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
    if (beval st b)
    then ceval_fun_no_while st c1
    else ceval_fun_no_while st c2
  | WHILE b DO c END => st
  end.

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).


Inductive ceval : com -> state -> state -> Prop :=
| E_Skip st : SKIP / st \\ st
| E_Ass st a1 n x : aeval st a1 = n -> (x ::= a1) / st \\ (t_update st x n)
| E_Seq c1 c2 st st' st'' :
    c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
| E_IfTrue st st' b c1 c2 :
    beval st b = true -> c1 / st \\ st' -> (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_IfFalse st st' b c1 c2 :
    beval st b = false -> c2 / st \\ st' -> (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_WhileEnd b st c :
    beval st b = false -> (WHILE b DO c END) / st \\ st
| E_WhileLoop st st' st'' b c :
    beval st b = true -> c / st \\ st' ->
    (WHILE b DO c END) / st' \\ st'' -> (WHILE b DO c END) / st \\ st''
where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (t_update empty_state X 2).
  apply E_Ass. auto.
  apply E_IfFalse. auto.
  apply E_Ass. auto.                       
Qed.

Print ceval_example1.
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  apply E_Ass. auto.
  apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
  apply E_Ass. auto.
  apply E_Ass. auto.
Qed.

Print ceval_example2.

Definition pup_to_n : com :=
  Y ::= ANum 0;;
    WHILE BLe (ANum 1) (AId X) DO
    Y ::= APlus (AId X) (AId Y);;
    X ::= AMinus (AId X) (ANum 1) END.
  
Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
           t_update (t_update (t_update (t_update (t_update (t_update empty_state
                                                                      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  apply E_Ass. auto.
  apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state
                                                                 X 2) Y 0) Y 2) X 1). auto.
  apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
  apply E_Ass. auto.
  apply E_Ass. auto.
  apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0). auto.
  apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
  apply E_Ass. auto.
  apply E_Ass. auto.
  apply E_WhileEnd. auto.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
    c / st \\ st1 ->
    c / st \\ st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *) assert (EQ1 : st' = st'0).
                { apply IHE1_1; assumption. }
                subst st'0.
                apply IHE1_2. assumption.
  - apply IHE1. assumption.
  - congruence.
  - congruence.
  - apply IHE1. assumption.
  - auto.
  - congruence.
  - congruence.
  - assert (EQ1 : st' = st'0).
    { apply IHE1_1. assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

Theorem plus2_spec : forall st n st',
    st X = n ->
    plus2 / st \\ st' -> st' X = n + 2.
Proof.
  intros st n st' Hx Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
    ~(loop / st \\ st').
Proof.
  intros st st' H. unfold loop in H.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction H. congruence.
  congruence. congruence. congruence.
  congruence. inversion Heqloopdef.
  subst. inversion H.
  congruence.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1;; c2 =>
    andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN c1 ELSE c2 FI =>
    andb (no_whiles c1) (no_whiles c2)
  | WHILE _ DO _ END => false
  end.

Print com.
Inductive no_whilesR : com -> Prop :=
| RSkip : no_whilesR SKIP
| RAss x y : no_whilesR (x ::= y)
| RSeq x y : no_whilesR x -> no_whilesR y -> no_whilesR (x ;; y)
| RIf b x y : no_whilesR x -> no_whilesR y -> no_whilesR (IFB b THEN x ELSE y FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros c. split. intros H.
  induction c. apply RSkip. apply RAss.
  simpl in H. apply andb_true_iff in H. destruct H.
  apply RSeq. apply IHc1. assumption. apply IHc2. assumption.
  simpl in H. apply andb_true_iff in H. destruct H.
  apply RIf. apply IHc1. assumption. apply IHc2. assumption.
  inversion H.

  intros H. induction c; simpl; auto.
  inversion H. apply andb_true_iff. split.
  apply IHc1. assumption. apply IHc2. assumption.
  inversion H. apply andb_true_iff. split.
  apply IHc1. assumption. apply IHc2. assumption.
  inversion H.
Qed.

Print aexp.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.


Definition s_eval (st : state) (stack : list nat) (inst : sinstr) : list nat :=
  match inst with
  | SPush x => x :: stack
  | SLoad id => st id :: stack
  | SPlus =>
    match stack with
    | f :: s :: rest => s + f :: rest
    | _ => []
    end
  | SMinus =>
    match stack with
    | f :: s :: rest => s - f :: rest
    | _ => []
    end
  | SMult =>
    match stack with
    | f :: s :: rest => s * f :: rest
    | _ => []
    end
  end.


    
Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) : list nat :=
  match prog with
  | nil => stack
  | h :: t =>
    s_execute st (s_eval st stack h) t
  end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
     = [2; 5].
Proof.
  reflexivity.
Qed.

Print s_execute.

Example s_execute2 :
  s_execute (t_update empty_state X 3) [3;4]
            [SPush 4; SLoad X; SMult; SPlus]
  = [15; 4].
Proof. compute. auto. Qed.

Print aexp.

                   
Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId id => [SLoad id]
  | APlus e1 e2 =>
    s_compile e1 ++ s_compile e2 ++ [SPlus]
  | AMinus e1 e2 =>
    s_compile e1 ++ s_compile e2 ++ [SMinus]
  | AMult e1 e2 =>
    s_compile e1 ++ s_compile e2 ++ [SMult]
  end.

Example s_compile1 :
  s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. compute. reflexivity. Qed.

Theorem s_concat_program :
  forall (st : state) (prog1 prog2 : list sinstr) (l : list nat),
    s_execute st l (prog1 ++ prog2) = s_execute st (s_execute st l prog1)  prog2.
Proof.
  intros st. induction prog1.
  auto.
  simpl. intros.
  destruct (s_eval st l a); apply IHprog1.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp) (l : list nat),
  s_execute st l (s_compile e) = [ aeval st e ] ++ l.
Proof.  
  intros st. induction e;
  auto; simpl;
  intros l;
  try (repeat (rewrite s_concat_program));
  rewrite IHe1, IHe2; auto.
Qed.

Module BreakImp.

  Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

  Notation "'SKIP'" := CSkip.
  Notation "'BREAK'" := CBreak.
  Notation "x '::=' a" := (CAss x a) (at level 60).
  Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).

  
  Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

  Reserved Notation "c1 '/' st '\\' s '/' st'"
           (at level 40, st, s at level 39).

  
  Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip st : CSkip / st \\ SContinue / st
  | E_Break st : CBreak / st \\ SBreak / st
  | E_Ass st a1 n x : aeval st a1 = n -> (x ::= a1) / st \\ SContinue / (t_update st x n)
  | E_IfTrue st st' b c1 c2 s :
      beval st b = true -> c1 / st \\ s / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ s / st'
  | E_IfFalse st st' b c1 c2 s :
      beval st b = false -> c2 / st \\ s / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ s / st'
  | E_SeqBreak c1 c2 st st' :
      c1 / st \\ SBreak / st' ->
      (c1 ;; c2) / st \\ SBreak / st'
  | E_Seq c1 c2 st st' st'' s:
      c1 / st \\ SContinue / st' -> c2 / st' \\ s / st'' ->
      (c1 ;; c2) / st \\ s / st''
  | E_WhileEnd st b c:
      beval st b = false ->
      (WHILE b DO c END) / st \\ SContinue / st
  | E_WhileLoopNormal st st' st'' b c s :
      beval st b = true ->
      c / st \\ SContinue / st' ->
      (WHILE b DO c END) / st' \\ s / st'' ->
      (WHILE b DO c END) / st \\ SContinue / st''
  | E_WhileBreak st st' b c:
      beval st b = true ->
      c / st \\ SBreak / st' ->
      (WHILE b DO c END) / st \\ SContinue / st'
  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

  Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
  Proof.
    intros c st st' s H.
    inversion H.
    inversion H5. auto. subst. inversion H2.
  Qed.

  
  Theorem while_continue : forall b c st st' s,
      (WHILE b DO c END) / st \\ s / st' ->
      s = SContinue.
  Proof.
    intros b c st st' s H. inversion H; auto.
  Qed.

  Theorem while_stops_on_break : forall b c st st',
      beval st b = true ->
      c / st \\ SBreak / st' ->
      (WHILE b DO c END) / st \\ SContinue / st'.
  Proof.
    intros b c st st' H1 H2.
    specialize (E_WhileBreak _ _ _ _ H1 H2); auto.
  Qed.

  
  Theorem while_break_true : forall b c st st',
      (WHILE b DO c END) / st \\ SContinue / st' ->
      beval st' b = true ->
      exists st'', c / st'' \\ SBreak / st'.
  Proof.
    intros. remember (WHILE b DO c END) as Hloop.
    induction H; try (inversion HeqHloop); subst.
    congruence. apply IHceval2. auto. auto.
    apply IHceval. 
