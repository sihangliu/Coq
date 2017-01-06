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


        
      

