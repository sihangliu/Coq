Module Monoid.
Require Import List.

Theorem Closure : forall ( X : Type ) ( l1 l2 : list X ) , exists ( l3 : list X ),
   l1 ++ l2 = l3.
Proof.
 intros X l1 l2. exists ( l1 ++ l2) .
 reflexivity.
Qed.

Theorem Association : forall ( X : Type ) ( l1 l2 l3 : list X ) , 
  l1 ++ ( l2 ++ l3 ) = l1 ++ ( l2 ++ l3 ).
Proof.
  intros X l1 l2 l3.
  simpl. reflexivity.
Qed.

Theorem Existence_identity_left : forall ( X : Type ) ( l : list X ), exists e,
 e ++ l = l.
Proof.
 intros X l. exists nil. simpl.
 reflexivity.
Qed.

Theorem Existence_identify_right : forall ( X : Type ) ( l : list X ) , exists e,
  l ++ e = l.
Proof.
 intros X l. exists nil.
 apply app_nil_r.
Qed.

