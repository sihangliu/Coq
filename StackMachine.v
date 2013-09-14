Require Import Bool Arith List.
Set Implicit Arguments.

Inductive binop : Set := Plus | Times.

Inductive exp : Set := 
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.

Definition binopDenote ( b : binop ) : nat -> nat -> nat := 
  match b with
      | Plus => plus
      | Times => mult
  end.

Fixpoint expDenote ( e : exp ) : nat := 
  match e with 
      | Const n => n
      | Binop b e1 e2 => ( binopDenote b ) ( expDenote e1 ) ( expDenote e2 )
  end.

Eval simpl in expDenote ( Binop Times ( Const 2 ) ( Const 4 ) ).

Inductive instr : Set := 
  | iConst : nat -> instr 
  | iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.


Definition instrDenot ( i : instr ) ( s : stack ) : option stack :=
  match i with 
      | iConst n =>  Some ( n :: s )
      | iBinop b => 
        match s with 
            | t1 :: t2 :: remain => Some ( ( binopDenote b ) t1 t2 :: remain )
            | _ => None
        end
  end.