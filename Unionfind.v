Require Export FSets.FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Export Coq.Arith.EqNat.

Module M := FSets.FMapAVL.Make  Nat_as_OT.

Definition uniondatastruct  : Type := M.t  ( nat * nat ).
Definition myempty := @M.empty ( nat * nat ).
Check @M.empty ( nat * nat ).

Check M.add 1 ( 1, 1 ) ( M.add 2 ( 2, 1) ( M.add 3 ( 3, 1 ) myempty ) ).

Fixpoint find ( k : nat ) ( m : uniondatastruct ) : option nat :=
  match M.find k m with
  | None  => None
  | Some ( a, _ ) => if beq_nat a k then Some a else find a m
  end.