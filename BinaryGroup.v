
Inductive bin  : Type :=
 | Zero : bin
 | One  : bin.

Definition add ( x : bin ) ( y : bin ) :=
  match x, y  with
  | Zero , _ => y
  | _ , Zero => x
  | One, One => Zero
  end. 

Definition sub ( x : bin ) ( y : bin ) := add.

Theorem Closure : forall ( a b : bin ) , exists ( c : bin ) ,
    c = add a b.
Proof.
  intros a b. exists ( add a b).
  reflexivity. 
Qed.

Theorem Associativity: forall ( a b c : bin ) ,
   add a  ( add b c ) = add ( add a b ) c.
Proof.
  intros a b c. destruct a. simpl. reflexivity.
  destruct b. unfold add. reflexivity. 
  destruct c. simpl. reflexivity. simpl. reflexivity.
Qed.

Theorem Identity_left : forall ( a : bin ) , exists ( e : bin ), 
  add e a = a.
Proof.
  intros a. exists Zero. reflexivity.
Qed.

Theorem Identity_right : forall ( a : bin ) , exists ( e : bin ),
  add a e = a.
Proof.
  intros a. exists Zero. destruct a. reflexivity. 
  reflexivity.
Qed.

Theorem Inverse_left : forall ( a  : bin ) , exists ( b : bin ),
    add a b = Zero. 
Proof.
 intros a. destruct a. exists Zero. reflexivity.
 exists One. reflexivity.
Qed.

Theorem Inverse_righ : forall ( a : bin ), exists ( b : bin ) , 
   add b a = Zero.
Proof.
  intros a. destruct a. exists Zero. reflexivity.
  exists One. reflexivity.
Qed.

Theorem Abelian_group : forall ( a b : bin ),
   add a b = add b a.
Proof.
  intros a b. destruct a.
  assert ( H1 : add Zero b = add b Zero ).
    destruct b. reflexivity. reflexivity.
  apply H1.
  assert ( H2 : add One b = add b One ). 
    destruct b. reflexivity. reflexivity.
  apply H2.
Qed.