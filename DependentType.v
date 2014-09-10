
Fixpoint typefun ( n : nat ) : Type :=
  match n with
  | O => bool
  | _ => nat 
  end.

Eval compute in typefun 1.

Fixpoint add ( f : nat -> nat ) ( g : nat -> bool )  ( n : nat ) : typefun n :=
   match n with
   | O => g O
   | _ => f n
   end.  

Fixpoint beq_nat ( m n : nat ) : typefun 0 :=
  match m, n with
  | O , O => true
  | S _ , O => false
  | 0 , S _ => false
  | S m' , S n' => beq_nat m' n'
  end.

Eval compute in add ( fun n => n + 1 ) ( fun n => if beq_nat n O then true else false) 1.

Fixpoint typesum ( n : nat ) : Type :=
  match n with 
  | O => nat
  | S n' =>  nat -> typesum n'
  end.

Eval compute in typesum 10.

