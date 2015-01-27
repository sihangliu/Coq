Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(Nat_as_OT).

Definition map_nat_nat: Type := M.t nat.

Definition find k (m: map_nat_nat) := M.find k m.

Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).

Example ex1: find 3 [1 |-> 2, 3 |-> 4] = Some 4.
Proof. reflexivity. Qed.

Example ex2: find 5 [1 |-> 2, 3 |-> 4] = None.
Proof. reflexivity. Qed.