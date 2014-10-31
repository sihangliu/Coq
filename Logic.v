Require Export MoreCoq.

Check ( 3 = 3 ).

Check ( forall ( n : nat ), n = 2 ).

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

Print silly.

Lemma silly_implication : ( 1 + 1 ) = 2 -> 0 * 3 = 0.
Proof.
  intros H. reflexivity.
Qed.

Print silly_implication.

Inductive and ( P Q : Prop ) : Prop := 
  conj : P -> Q -> ( and P Q ).

Notation "P /\ Q " := ( and P Q ) : type_scope.
Check conj.

Theorem and_example : 
  ( 0 = 0 ) /\ ( 4 = mult 2 2 ).
Proof.
  apply conj. 
  Case "left".
    reflexivity.
  Case "right".
    reflexivity.
Qed.

Theorem and_example' : 
   ( 0 = 0 ) /\ ( 4 = mult 2 2 ).
Proof.
  split.
  Case "left".
    reflexivity.
  Case "right".
    reflexivity.
Qed.

Theorem proj1 : forall P Q : Prop , 
 P /\ Q -> P.
Proof.
 intros P Q H.
 inversion H as [ HP HQ ].
 apply HP.
Qed.

Theorem proj2 : forall P Q : Prop , 
 P /\ Q -> Q.
Proof.
 intros P Q H.
 inversion H as [ HP HQ ].
 apply HQ.
Qed.

Theorem and_commute : forall ( P Q : Prop ), 
 P /\ Q -> Q /\ P.
Proof.
 intros P Q H. inversion H as [ HP HQ ].
 split.
   Case "left".  
     apply HQ.
   Case "right".
     apply HP.
Qed.

Theorem and_assoc : forall ( P Q R : Prop ) , 
  P /\ ( Q /\ R ) -> ( P /\ Q ) /\ R .
Proof.
 intros P Q R H.
 inversion H as [ HP [ HQ HR ] ].
 split.
  Case "left". 
    split.
      SCase "left". apply HP.      
      SCase "right". apply HQ.
  Case "right". apply HR.
Qed.

Definition iff ( P Q : Prop ) : Prop := ( P -> Q ) /\ ( Q -> P ) .

Notation "P <-> Q" := ( iff P Q ) 
                       (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
 ( P <-> Q ) -> ( P -> Q ).
Proof.
 intros P Q H.
 inversion H as [ Hf Hs ].
 apply Hf.
Qed.

Theorem iff_sym : forall P Q : Prop, 
 ( P <-> Q ) -> ( Q <-> P ).
Proof.
 intros P Q H. inversion H as [ HPQ HQP].
 split.
  Case "left". apply HQP.
  Case "right". apply HPQ.
Qed.

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof.
 intros P.
 split.
  Case "left". 
    intros H. apply H.
  Case "right".
    intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  ( P <-> Q ) -> ( Q <-> R ) -> ( P -> R ).
Proof.
  intros P Q R HPQ HQR. inversion HPQ as [ HP HQ]. inversion HQR as [ HQ' HP'].
  intros H. apply HP in H. apply HQ' in H. apply H.
Qed.

Inductive or ( P Q : Prop ) : Prop := 
 | or_introl : P -> or P Q
 | or_intror : Q -> or P Q.

Notation "P \/ Q" := ( or P Q ) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut : forall P Q : Prop, 
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H. 
  inversion H as [ HP | HQ ].
    Case "left". apply or_intror. apply HP.
    Case "right".  apply or_introl. apply HQ.
Qed.

Theorem or_commut' : forall P Q : Prop, 
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [ HP | HQ].
  Case "left". right. apply HP.
  Case "right". left. apply HQ.
Qed.

Theorem or_distribute_over_and_1 : forall P Q R : Prop,
  P \/ ( Q /\ R ) -> ( P \/ Q ) /\ ( P \/ R ).
Proof.
 intros P Q R H. inversion H as [ HP | [ HQ HR ] ].
 Case "left". split.
  SCase "left". left. apply HP.
  SCase "right". left. apply HP.
 Case "right". split.
   SCase "left". right. apply HQ.
   SCase "right". right. apply HR.
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
 intros P Q R H.
 inversion H as [ [ HP | HQ] [ HP' | HQ']].
 Case "left". left. apply HP'.
 Case "right". left. apply HP.
 Case "left". left. apply HP'. 
 Case "right". right. split. 
  SCase "left". apply HQ.
  SCase "right". apply HQ'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
 intros P Q R. split. 
 Case "left". 
     intros H. apply or_distribute_over_and_1. apply H.
 Case "right". 
     intros H. apply or_distributes_over_and_2 . apply H.
Qed.

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". destruct c.
    SCase "c = true". split. reflexivity. reflexivity.
    SCase "c = false". split. reflexivity. inversion H.
  Case "b = false". destruct c.
    SCase "c = true". split. inversion H. reflexivity.
    SCase "c = false". split. inversion H. inversion H.
Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
 intros b c H.  inversion H. rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H. destruct b.
  Case "b = true". destruct c.
   SCase "c = true". 
      left. inversion H.
   SCase "c = false".
      right. reflexivity.
  Case "b = false". destruct c.
   SCase "c = true". 
      left. reflexivity.
   SCase "c = false".
      left. reflexivity.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.  
  destruct b.
  Case "b = true".
    left. reflexivity.
  Case "b = false". destruct c.
    SCase "c = true".
       right. reflexivity.
    SCase "c = false".
       inversion H.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". split.
      SCase "left". inversion H.
      SCase "right". inversion H.
  Case "b = false". destruct c.
      SCase "c = true". split. 
        SSCase "left". reflexivity.
        SSCase "right". inversion H.
      SCase "c = false". split. reflexivity. reflexivity.
Qed.

Inductive False : Prop := .

Theorem false_implies_nonsense : 
  False -> 2 + 2 = 5.
Proof.
 intros H. inversion H.
Qed.

(* 
Conversely, the only way to prove False is if there is already something
 nonsensical or contradictory in the context:
*)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
 intros H. inversion H.
Qed.

(* 
You can prove anything from false assumption *)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P H. inversion H.
Qed.

Inductive True : Prop := tt.
Print True.

Definition not ( P : Prop ) : Prop := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
 unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
 intros P Q H. inversion H as [ HP NHP ].
 unfold not in NHP. apply NHP in HP. inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
 intros P H. unfold not. intros HN.
 apply HN in H. inversion H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
 intros P Q H1 H2. unfold not in H2. unfold not.
 intros Hp. apply H1 in Hp. apply H2 in Hp.
 inversion Hp.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros H.
  inversion H. apply H1 in H0. apply H0.
Qed.

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
 intros P H. unfold not in H.
Abort.

Theorem excluded_middle_irrefutable: forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
 intros P. unfold not. intros H. 
 apply H. right. intros H1.
 apply H. left. apply H1.
Qed. 

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true :forall b : bool,
  b <> false -> b = true.
Proof.
 intros b. destruct b.
 Case "b = true".
   intros H. reflexivity.
 Case "b = false".
   unfold not. intros H. apply ex_falso_quodlibet. apply H.
   reflexivity.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
 intros n m H. unfold not in H.
 Abort.

SearchAbout beq_nat.
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n m H. unfold not.
Abort.  

(* proofs from type theory and functional programming *)
Theorem implication_trans : forall A B C : Prop,
  ( A -> B ) -> ( B -> C ) -> ( A -> C).
Proof.
  intros A B C H1 H2 H3. apply H1 in H3. apply H2 in H3. apply H3.
Qed.

Theorem prob_second : forall  A B C : Prop , 
    ( ( A \/ B ) -> C ) -> ( ( A -> C ) /\ ( B -> C ) ).
Proof.
  intros A B C H. 
Abort.

Theorem prob_thrid : forall A B C : Prop , 
  ( A -> ( B -> C ) ) -> ( ( A /\ B ) -> C ).
Proof.
  intros A B C H1 H2. inversion H2. apply H1 in H. apply H. apply H0.
Qed.

Theorem prob_four : forall A B : Prop , 
  ( A -> B ) -> ( B -> A ).
Proof.
  intros A B H1 H2.
Abort.

Theorem prob_five : forall A B : Prop,
  A -> ~ ~ A.
Proof.
  intros A B H. unfold not. intros Hf. apply Hf in H.
  inversion H.
Qed.
