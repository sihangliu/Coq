Require Import Bool Arith List.
Set Implicit Arguments.

Inductive binop : Set := Plus | Times.

Inductive exp : Set := 
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.

 
Definition binopDenot ( b : binop ) : nat -> nat -> nat := 
  match b with 
      | Plus => plus
      | Times => mult
  end.


Fixpoint expDenote ( e : exp ) : nat := 
   match e with
    | Const n => n
    | Binop b e1 e2 => ( binopDenot b ) ( expDenote e1 ) ( expDenote e2 )
   end.

Eval simpl in expDenote ( Const 42 ).
Eval simpl in expDenote ( Binop Plus ( Const 2 ) ( Const 2 )). 
Eval simpl in expDenote ( Binop Times ( Binop Plus ( Const 2 ) ( Const 2 )) ( Const 7)).

Inductive instr : Set := 
  | iConst : nat -> instr
  | iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition ( i : instr ) ( s : stack ) : option stack := 
  match i with 
      | iConst n -> Some ( n :: s )
      | iBinop b => match b with 
                        | arg1 :: arg2 :: s' => Some ( ( binopDenote b ) arg1 arg2 :: s' )
                        | _ => None
                    end
  end.