Module InductiveTypes.
Set Implicit Arguments.

Inductive unit : Set :=
   | tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
destruct x.
reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set :=. 

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
destruct 1.
Qed.

Check Empty_set_ind.

Inductive bool : Set :=
 | true
 | false.

Definition negb ( b: bool ) : bool :=
  match b with
  | true => false
  | false => true
 end.

Definition negb' ( b : bool ) : bool := if b then false else true.

Eval simpl in negb false.

Theorem negb_inverse : forall b : bool, negb ( negb b ) = b.
intros.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
intros.
destruct b.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Check bool_ind.

Inductive nat : Set :=
 | O : nat
 | S : nat -> nat.

Definition isZero ( n : nat ) : bool := 
 match n with
  | O => true
  | S _ => false
 end.

Definition pred ( n : nat ) : nat := 
  match n with 
   | O => O
   | S n' => n'
  end.

Fixpoint plus ( n m : nat ) : nat := 
  match n with
   | O => m
   | S n' => S ( plus n' m )
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
intros.
simpl.
reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
injection 1.
trivial.
Qed.


Theorem m_plus_n : forall n m : nat, plus n m = plus m n.
Proof.
 intros.
 induction m.
 induction n.
 reflexivity.
 simpl.
 rewrite IHn.
 simpl.
 trivial.
 simpl.
 Abort.

Inductive nat_list : Set := 
  | NNil : nat_list
  | NCons : nat -> nat_list -> nat_list.

Fixpoint nlength ( ls : nat_list ) : nat :=
  match ls with 
   | NNil => O
   | NCons _ ls' => S ( nlength ls' )
  end.

Fixpoint napp ( ls1 ls2 : nat_list ) : nat_list := 
   match ls1 with 
     | NNil => ls2
     | NCons l ls1' => NCons l ( napp ls1' ls2 )
   end.

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength ( napp ls1 ls2 ) = 
        plus ( nlength ls1 ) ( nlength ls2 ).
Proof.
Abort.

Check nat_list_ind.

Inductive nat_btree : Set :=
 | NLeaf : nat_btree
 | NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize ( nr : nat_btree ) : nat := 
   match nr with
    | NLeaf => S O
    | NNode tr1  _ tr2 => plus ( nsize tr1 ) ( nsize tr2 )
   end.

Check nat_btree_ind.

Inductive list ( T : Set ) : Set := 
   | Nil : list T
   | Cons : T -> list T -> list T.

Fixpoint length T ( ls : list T ) : nat := 
   match ls with 
     | Nil => O
     | Cons _ ls' => S ( length  ls' )
   end.

Fixpoint app T ( ls1 ls2 : list T ) : list T := 
   match ls1 with 
     | Nil => ls2 
     | Cons  x ls1' => Cons x ( app  ls1' ls2 )
   end.

Check list_ind.

Inductive even_list : Set :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list

with odd_list : Set := 
  | OCons : nat -> even_list -> odd_list.

Fixpoint elength ( el : even_list ) : nat := 
   match el with 
     | ENil => O
     | ECons _ ol => S ( olength ol )
   end
with olength ( ol : odd_list ) : nat := 
    match ol with 
     | OCons _ el => S ( elength el )
    end. 

Fixpoint eapp ( el1 el2 : even_list ) : even_list := 
  match el1 with
   | ENil => el2
   | ECons x ol => ECons x ( oapp ol el2 )
  end

with oapp ( ol : odd_list ) ( el : even_list ) : odd_list := 
   match ol with
    | OCons n el' => OCons n ( eapp el' el )
   end.

Check even_list_ind.

Inductive pformula : Set :=
  | Truth : pformula
  | Falsehood : pformula
  | Conjunction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote ( f : pformula ) : Prop :=
  match f with 
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 =>  pformulaDenote f1 /\ pformulaDenote f2 
  end. 

Inductive formula  : Set := 
   | Eq : nat -> nat -> formula
   | And : formula -> formula -> formula
   | Forall : ( nat -> formula ) -> formula.

Example forall_refl : formula := Forall ( fun x => Eq x x ).

Fixpoint formulaDenote ( f : formula ) : Prop :=
  match f with
   | Eq n1 n2 => n1 = n2 
   | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
   | Forall f' => forall n : nat, formulaDenote ( f' n ) 
  end.


Fixpoint swapper ( f : formula ) : formula := 
  match f with 
   | Eq n1 n2 => Eq n2 n1
   | And f1 f2 => And ( swapper f1 ) ( swapper f2 )
   | Forall f' => Forall ( fun n => swapper ( f' n ))
  end.

Check formula_ind.


Check nat_ind.
Print nat_ind.

Print nat_rect.

Fixpoint plus_recursive ( n : nat ) : nat -> nat :=
  match n with 
  | O => fun m => m
  | S n' => fun m => S ( plus_recursive n' m )
  end.

Definition plus_rec : nat -> nat -> nat := 
   nat_rect ( fun _ : nat => nat -> nat ) ( fun m => m ) ( fun _ r m  => S ( r m )).

Eval simpl in plus_rec ( S O ) ( S O ).


Theorem plus_equivalend : plus_recursive = plus_rec.

Proof.
reflexivity.
Qed.

