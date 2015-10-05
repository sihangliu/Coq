Require Export "ProofObjects".

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S n". intros n H. simpl. apply H.
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S n". simpl. intros n H. apply f_equal. assumption.
Qed.

Inductive yesno : Type :=
| yes : yesno
| no : yesno.

(*
forall P : yesno -> Prop, P yes -> P no -> forall y, P y *)

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

(* 
forall P : rgb -> Prop, P red -> P green -> P blue -> forall y, P y *)
Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

(*
forall P : natlist -> Prop, P nnil -> (forall (n : nat) (l : natlist), 
P l -> P (ncons n l)) -> forall n : natlist, P n *)
Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* 
 forall P : natlist1 -> Prop, 
   P nnil1 -> (forall (n : nat) (l : natlist1), P l -> P (nsnoc1 l n)) -> 
   forall (n : natlist1), P n *)
Check natlist1_ind.
