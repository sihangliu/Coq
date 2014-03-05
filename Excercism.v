Module Excercism.

Inductive bool : Set := 
  | true : bool
  | false : bool.

Check true.
Check false.

Eval compute in true.

Definition not ( b : bool ) : bool :=
   match b with 
       | true => false
       | false => true
   end.

Check not true.

Eval compute in not true.

Example bool_not : not true = false.

Proof. 
  simpl.
  reflexivity.
  Qed.

Definition or ( b1 : bool ) ( b2 : bool ) : bool := 
   match b1 with
       | true => true
       | false => b2
   end.

Inductive nat :=
  | O : nat
  | S : nat -> nat.

Definition  pred ( n : nat ) : nat :=
  match n with
      | O => O
      | S n' => n'
  end.

Eval compute  in ( S ( S ( S O ))).

End Excercism.

Module Excercism2.
  
Fixpoint plus ( n : nat ) ( m : nat ) : nat := 
  match n with 
      | O => m
      | S n' => S ( plus n' m ) 
  end.

Eval compute in ( plus 4 5 ).

Fixpoint mult ( n : nat ) ( m : nat ) : nat := 
   match n with 
    | O => O
    | S n' => plus m ( mult n' m ) 
  end. 

Eval compute in ( mult 12 3 ).


Fixpoint beq_nat ( n m : nat ) : bool := 
   match n with 
    | O => match m with 
               | O => true
               | S m' => false
           end
    | S n' => match m with 
               | O => false
               | S m' => beq_nat n' m'
              end
   end.

End Excercism2.

Fixpoint evenb ( n : nat ) : bool := 
  match n with 
    | O => true
    | S O => false
    | S ( S n' ) => evenb n'
  end.

Extraction Language Haskell.
Extraction plus.

Extraction Language Ocaml.
Extraction plus.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.

Theorem plus_id_example : forall n m : nat, 
   m = n -> m + n = n + n .

Proof.
 intros n m.
 intros H.
 rewrite H.
 reflexivity. 
 Qed.

Require Import Arith.

Theorem plus_1_neg_0 : forall n : nat, 
   beq_nat ( n + 1 ) 0 = false.

Proof. 
  intros n.
  destruct n as [|n'].
  simpl.
  reflexivity.
  simpl.
  reflexivity.
 Qed.

Theorem plus_0_r : forall n : nat, 
   n + 0 = n .

Proof. 
  intros n.
  induction  n as [|n'].
  reflexivity. 
  simpl. 
  rewrite -> IHn'.
  reflexivity.
Qed.

Check Type.

Inductive even :  nat -> Prop := 
   | ev_O : even O
   | ev_SS : forall n : nat, even n -> even ( S ( S n ) ).



