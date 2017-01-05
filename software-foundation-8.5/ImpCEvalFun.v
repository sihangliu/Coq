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


      

