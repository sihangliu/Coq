Require Import String ZArith List.
Open Scope Z_scope.

Inductive aexpr : Type :=
 | anum ( x : Z ) : aexpr
 | avar ( s : string ) : aexpr
 | aplus ( e1 e2 : aexpr ) : aexpr.

Inductive bexpr : Type :=
 | blt ( e1 e2 : aexpr ) : bexpr.

Inductive instr : Type :=
 | assign ( x : string ) ( e : aexpr )
 | seq ( i1 i2 : instr ) : instr
 | while ( b : bexpr ) ( i : instr ) : instr.

Fixpoint af ( g : string -> Z ) ( e : aexpr ) : Z :=
 match e with
 | anum n => n
 | avar x => g x
 | aplus e1 e2 => af g e1 + af g e2
 end.

SearchAbout ( Z -> Z -> bool ).
Fixpoint bf ( g : string -> Z ) ( b : bexpr )  :=
 match b with
 | blt b1 b2 => Z.ltb ( af g b1 ) ( af g b2 )
 end.


Inductive assert : Type :=
 | pred ( p : string ) ( l : list aexpr )
 | a_b ( b : bexpr )
 | a_conj ( a1 a2 : assert )
 | a_not ( a : assert )
 | a_true
 | a_false.

Fixpoint ia  ( m : string -> list Z -> Prop ) ( g : string -> Z ) 
  ( a : assert ) : Prop :=
 match a with
 | pred s l => m s ( map ( af g ) l )
 | a_b b => bf g b = true
 | a_conj a1 a2 => ( ia m g a1 ) /\ ( ia m g a2 )
 | a_not a => not ( ia m g a )
 | a_true => True
 | a_false => False
 end.

Inductive a_instr : Type :=
 | pre ( a : assert ) ( i : a_instr ) 
 | a_assign ( x : string ) ( e : aexpr )
 | a_seq ( i1 i2 : a_instr )
 | a_while ( b : bexpr ) ( a : assert ) ( i : a_instr ).

Fixpoint asubst ( x : string ) ( s : aexpr ) ( e : aexpr ) : aexpr :=
 match e with
 | anum n => anum n
 | avar x1 => if string_dec x x1 then s else e
 | aplus e1 e2 => aplus ( asubst x s e1 ) ( asubst x s e2 )
 end.

Definition bsubst ( x : string ) ( s : aexpr ) ( b : bexpr ) : bexpr :=
 match b with
 | blt e1 e2 => blt ( asubst x s e1 ) ( asubst x s e2 )
 end.

Fixpoint subst ( x : string )  ( s : aexpr ) ( a : assert ) : assert :=
 match a with
 | pred p l => pred p ( map ( asubst x s ) l )
 | a_b b => a_b ( bsubst x s b )
 | a_conj a1 a2 => a_conj ( subst x s a1 ) ( subst x s a2 )
 | a_not a => a_not ( subst x s a)
 | any => any
 end.

