Require Export Lists.
Require Export Basic.
Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Inductive boollist : Type :=
 | bool_nil : boollist
 | bool_cons : bool -> boollist -> boollist.

Inductive list (  X : Type ) : Type :=
 | nil : list X
 | cons : X -> list X -> list X.

Check nil.
Check cons.

Check ( cons nat 2 ( cons nat 1 ( nil nat ) )).

Fixpoint length ( X : Type ) ( l : list X ) : nat :=
 match l with
 | nil => O
 | cons h t => S ( length X t )
 end.

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof.
  simpl. reflexivity. 
Qed.

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof.
 simpl. reflexivity.
Qed.

Fixpoint app ( X : Type ) ( l1 l2 : list X ) : list X :=
 match l1 with
 | nil   => l2
 | cons h t => cons X h ( app X t l2)
 end.

Fixpoint snoc ( X : Type ) ( l : list X ) ( v : X ) : list X :=
 match l with
 | nil => cons X v ( nil X )
 | cons h t => cons X h ( snoc X t v )
 end.

Fixpoint rev ( X : Type ) ( l : list X ) : list X := 
 match l with
 | nil => nil X 
 | cons h t => snoc X ( rev X t ) h
 end.

Example test_rev1 : 
  rev nat ( cons nat 1 ( cons nat 2 ( nil nat ))) 
 = ( cons nat 2 ( cons nat 1 ( nil nat ))).
Proof.
 simpl. reflexivity.
Qed.

Example test_rev2 : 
  rev bool ( nil bool ) = nil bool.
Proof.
 simpl. reflexivity.
Qed.

Module MumbleBaz.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.


(* not correct because d expects a Type ( nat, bool or mumble )
Check d ( b a 5 ).
so correct expression can be d bool ( b a 5 ) , d nat ( b a 5 )
d mumble ( b a 5 )
*)
Check d mumble ( b a 5 ).
Check d bool ( b a 5 ).
Check e bool true.
Check e mumble ( b c 0 ).
(* 
Not correct because the type of b c 0 is mumble not bool so correct expression
is e mumble ( b c 0 ) or e bool true or e bool false or 
e mumble c , e mumble a 
Check e bool ( b c 0 ).
*)
Check e mumble a.
Check e mumble c.
Check e mumble ( b ( b a 5 ) 5 ).

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(* Initial thought =>  I think infinite elements *)
(* final tought zero. I am not able to contruct any element of type 
   baz *)
Check x.
Check y.

End MumbleBaz.

Fixpoint app' X l1 l2 : list X := 
 match l1 with
 | nil => l2 
 | cons h t => cons X h ( app' X t l2 )
 end.

Check app'.
Check app.

Fixpoint length' (  X : Type ) ( l : list X ) : nat :=
 match l with
 | nil => O
 | cons h t => S ( length _ t )
 end.

Definition list123 := 
 cons nat 1 ( cons nat 2 ( cons nat 3 ( nil nat ))).
Print list123.

Definition list123' :=
 cons _ 1 ( cons _ 2 ( cons _ 3 ( nil _ ) ) ) .
Print list123'.

Arguments nil {X}.
Arguments cons { X } _ _. 
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' :=  cons 1 ( cons 2 ( cons 3 nil ) ).
Check ( length list123'').

Fixpoint length'' { X : Type } ( l : list X ) : nat :=
 match l with
 | nil => O
 | cons h t => S ( length'' t )
 end.

(*
Definition mynil := nil.
*)

Definition mynil : list nat :=  nil.
Check mynil.
Check @nil.

Definition mynil' := @nil.
Check mynil'.

Definition mynil'' := @nil nat.
Check mynil''.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [ 1 ; 2 ; 3 ].
Check ( [ 3 + 4 ] ++ @nil nat ).

Fixpoint repeat { X : Type } ( n : X ) ( count : nat ) : list X := 
 match count with
 | O => nil
 | S count' => n :: repeat n count' 
 end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof.
 simpl. reflexivity.
Qed.

Theorem nil_app: forall X : Type, forall l : list X , 
  app [] l = l.
Proof. 
  intros X l. simpl. reflexivity.
Qed.

Theorem app_nil : forall X : Type , forall l : list X,
  app l [] = l.
Proof.
  intros X l. induction l as [ | h' l' ].
  Case "l = nil".
   simpl. reflexivity.
  Case "l = cons h' l'".
   simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem snoc_list : forall X : Type , forall v : X , forall s : list X,
 snoc s v = s ++ [v].
Proof.
 intros X v s. induction s as [ | h' s'].
 Case "s = nil".
  simpl.  reflexivity.
 Case "s = cons h' s'".
  simpl. rewrite -> IHs'. reflexivity.
Qed.

Theorem rev_snoc : forall X : Type, forall v : X , forall s : list X, 
  rev ( snoc s v ) = v :: ( rev s ).
Proof.
 intros X v s. induction s as [ | h' s'].
 Case "s = nil".
  simpl. reflexivity.
 Case "s = cons h' s'". 
  simpl. rewrite -> IHs'. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type , forall l : list X , 
  rev ( rev l ) = l.
Proof.
 intros X l. induction l as [ | h' l' ].
 Case "l = nil".
  simpl. reflexivity.
 Case "l = cons h' l'".
  simpl. rewrite -> rev_snoc. rewrite -> IHl'.
  reflexivity.
Qed.

Theorem list_assoc : forall X : Type , forall l1 l2 l3 : list X ,
 ( l1 ++ l2 ) ++ l3 = l1 ++ ( l2 ++ l3 ).
Proof.
  intros X l1 l2 l3. induction l1 as [ | h' l1'].
  Case "l1 = nil".
    simpl. reflexivity.
  Case "l1 = cons h' l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type , forall l1 l2 : list X, 
    forall v : X , snoc ( l1 ++ l2 ) v = l1 ++ snoc l2 v.
Proof.
 intros X l1 l2 v.
 rewrite -> snoc_list. rewrite -> snoc_list. rewrite -> list_assoc.
 reflexivity.
Qed.

Inductive prod ( X Y : Type ) : Type := 
  pair : X -> Y -> prod X Y.

Check ( pair nat bool 3 true ).

Arguments pair { X } { Y } _ _.
Check ( pair 3 true ).

Notation "( x , y )" := ( pair x y ).

Notation "X * Y" := ( prod X Y ) : type_scope.

Definition fst { X Y : Type } ( p : X * Y ) : X :=
 match p with
 | ( x , y ) => x
 end.

Definition snd { X Y : Type } ( p : X * Y ) : Y :=
 match p with
 |( x , y ) => y 
 end.

Fixpoint combine { X Y : Type } ( l1 : list X ) ( l2 : list Y ) 
             : list ( X * Y ) :=
  match l1 , l2 with 
  | nil , _ => nil
  | _ , nil => nil
  | h1 :: t1 , h2 :: t2 => ( h1 , h2 ) :: combine t1 t2
  end. 

Check @combine.  
Eval compute in (combine [1;2] [false;false;true;true]). 

Fixpoint split { X Y : Type } ( l : list ( X * Y ) ) :  list X * list Y  :=
  match l with
  | nil => ( nil , nil )
  | ( x , y ) :: t => let ( a , b ) := split t in ( x :: a , y :: b )
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
 simpl. reflexivity.
Qed.

Inductive option ( X : Type ) : Type :=
 | None : option X
 | Some : X -> option X.

Arguments None {X}.
Arguments Some {X} _ .

Fixpoint index { X : Type } ( n : nat ) ( l : list  X ) : option X :=
 match l with
  | nil => None
  | h :: t => if beq_nat n O then Some h else index ( pred n ) t 
 end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X := 
 match l with
  | nil => None
  | h :: _ => Some h
 end.

Check @hd_opt.
Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof.
  simpl. reflexivity.
Qed.

Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof.
  simpl. reflexivity.
Qed.

(* Function as Data *)

Definition doit3times { X : Type } ( f : X -> X ) ( n : X ) : X :=
  f ( f ( f n ) ).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof.
 compute. reflexivity.
Qed.

Example test_doit3times': doit3times negb true = false.
Proof.
  compute. reflexivity.
Qed.

Check plus.

Definition plus3 := plus 3.
Check @plus3.

Example test_plus3 : plus3 4 = 7.
Proof.
 compute. reflexivity.
Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof.
  compute. reflexivity.
Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof.
 compute. reflexivity.
Qed.

Definition prod_curry { X Y Z : Type }
  ( f : X * Y -> Z ) ( x : X ) ( y : Y ) : Z :=
  f ( x , y ) .

Definition prod_uncurry { X Y Z : Type } 
  ( f : X -> Y -> Z ) ( p : X * Y ) : Z :=
  f ( fst p ) ( snd p ).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall ( X Y Z : Type ) ( f : X -> Y -> Z ) 
  ( x : X ) ( y : Y ) , 
    prod_curry ( prod_uncurry f ) x y = f x y. 
Proof.
  intros X Y Z f x y.
  compute. reflexivity.
Qed.

Theorem curry_uncurry : forall ( X Y Z : Type ) ( f : X * Y -> Z ) ( p : X * Y ),
   prod_uncurry ( prod_curry f ) p = f p.
Proof.
 intros X Y Z f p.
 destruct p as ( x , y ).
 compute. reflexivity.
Qed.

Fixpoint filter { X : Type } ( test : X -> bool ) ( l : list  X ) : list X :=
 match l with
 | nil => nil
 | h :: t => if test h then h :: filter test t else filter test t
 end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof.
 compute. reflexivity.
Qed.

Definition length_is_1 { X : Type } ( l : list X ) : bool :=
 beq_nat ( length l ) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof.
 compute. reflexivity.
Qed.

Definition countoddmembers'  ( l : list nat ) : nat :=
  length ( filter oddb l ).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof.
 compute. reflexivity.
Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof.
 compute. reflexivity.
Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof.
 compute. reflexivity.
Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof.
 compute. reflexivity.
Qed.

Example test_filter2' : 
  filter ( fun l => beq_nat ( length l ) 1 ) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
 = [ [3]; [4]; [8] ].
Proof.
 compute. reflexivity.
Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter ( fun n => negb ( orb ( oddb n ) ( blt_nat n 7 ) ) ) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
 compute. reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
 compute. reflexivity.
Qed.

Theorem list_monoid : forall ( X : Type ) ( l1 l2 : list X ), exists ( l3 : list X ),
  l1 ++ l2  = l3.  
Proof.
 intros X l1 l2. destruct l1 as [ | h' l1'].
 Case "l1 = nil".
   simpl. exists l2. reflexivity.
 Case "l1 = cons h' l1'".
   simpl. exists (  h' :: l1' ++ l2 ). reflexivity.
Qed.

Fixpoint partition {  X : Type } 
     ( test : X -> bool )  ( l : list X ) : list X * list X :=
 match l with
 | nil => ( nil , nil )
 | h :: t => let ( xs , ys ) := partition test t in 
             if test h then ( h :: xs, ys ) else ( xs , h :: ys )
 end.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
 compute. reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
 compute. reflexivity.
Qed.

Fixpoint map { X Y : Type } ( f : X -> Y ) ( l : list X ) : list Y :=
 match l with
 | nil => nil
 | h :: t => f h :: map f t 
 end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof.
 compute. reflexivity.
Qed.

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof.
 compute. reflexivity.
Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof.
 compute. reflexivity.
Qed.


Theorem map_snoc : forall (X Y : Type) (f : X -> Y) ( h : X ) ( l : list X ),
  map f ( snoc l h ) = snoc ( map f l ) ( f h ).
Proof.
 intros X Y f h l. induction l as [ | h' l' ].
 Case "l = nil".
  simpl. reflexivity.
 Case "l = cons h' l'".
  simpl. rewrite -> IHl'. reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
 intros X Y f l. induction l as [ | h' l'].
 Case "l = nil".
  simpl. reflexivity.
 Case "l = cons h' l'".
  simpl. rewrite <- IHl'. rewrite -> map_snoc. reflexivity.
Qed.

Definition compose { X Y Z : Type } 
   ( f :  Y ->  Z ) ( g : X -> Y ) ( x : X ) := 
   f ( g x ).

Theorem map_compose : forall ( X Y Z : Type )
     ( f :  Y ->  Z ) ( g : X ->  Y ) ( l : list X ),
     compose ( map f ) ( map g )  l = map ( compose f g ) l.  
Proof.
  intros X Y Z f g l. induction l as [ | h' l'].
  Case "l = nil".
   compute. reflexivity.
  Case "l = cons h' l'".
   simpl. rewrite <- IHl'. reflexivity.
Qed.

Fixpoint flat_map { X Y : Type } ( f : X -> list Y ) ( l : list X ) : list Y :=
 match l with
 | nil => nil
 | h :: t => f h ++ flat_map f t
 end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
 simpl. reflexivity.
Qed.

Definition option_map { X Y : Type } ( f : X -> Y ) ( xo : option X ) : option Y :=
 match xo with
 | None => None
 | Some x => Some ( f x )
 end.

Fixpoint filter' ( X : Type ) ( f : X -> bool ) ( l : list X ) : list X :=
 match l with
 | nil => nil
 | h :: t => if f h then h :: filter' X f t else filter' X f t
 end.

Example test_filter2'' : 
  filter' ( list nat ) ( fun l => beq_nat ( length l ) 1 ) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
 = [ [3]; [4]; [8] ].
Proof.
 compute. reflexivity.
Qed.

Fixpoint map' ( X Y : Type ) ( f : X -> Y ) ( l : list X ) : list Y :=
 match l with
 | nil => nil
 | h :: t => f h :: map' X Y f t
 end.

Example test_map3':
    map' nat ( list bool ) (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof.
 compute. reflexivity.
Qed.

Fixpoint fold { X Y : Type } ( f : X -> Y -> Y ) ( l : list X ) ( b : Y ) : Y :=
 match l with
 | nil => b
 | h :: t => f h ( fold f t b )
 end.

Eval compute in fold plus [ 1 ; 2 ; 3 ; 4 ] 0.

Check fold andb.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof.
 simpl. reflexivity.
Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof.
 simpl. reflexivity.
Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof.
 simpl. reflexivity.
Qed.

Definition constfun { X : Type } ( x : X ) : nat -> X :=
 fun ( k : nat ) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. 
 simpl. compute. reflexivity.
Qed.

Example constfun_example2 : (constfun 5)  99 = 5.
Proof. 
 simpl. compute. reflexivity.
Qed.

Definition override { X : Type } ( f : nat -> X ) ( k : nat ) ( x : X ) : nat -> X :=
 fun ( k' : nat ) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. 
  simpl. compute. reflexivity. 
Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof.
  compute. reflexivity. 
Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof.
 compute. reflexivity. 
Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. 
 compute. reflexivity. 
Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
 intros b. compute. reflexivity.
Qed.


Theorem unfold_example_bad : forall m n,
  3 + n = m -> plus3 n + 1 = m + 1.
Proof.
 intros m n H. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Theorem unfold_example_bad' : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
 intros n m H. 
 Abort.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
 intros m n H.
 unfold plus3.
 rewrite <- H. 
 reflexivity.
Qed.

Require Export Induction.
Theorem override_eq : forall { X:Type } x k (f:nat -> X),
  (override f k x) k = x.
Proof.
 intros X x k f.
 unfold override. rewrite <- beq_nat_refl.
 reflexivity.
Qed.

Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
 intros X x1 x2 k1 k2 f H1 H2.
 unfold override. rewrite -> H2. rewrite -> H1.
 reflexivity.
Qed.

Definition fold_length { X : Type } ( l : list X ) : nat :=
  fold ( fun _ n => S n ) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. 
 unfold fold_length. simpl. 
 reflexivity. 
Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
 intros X l. induction l as [ | h' l'].
 Case "l = nil".
  reflexivity.
 Case "l = cons h' l'".
  simpl. unfold fold_length. simpl.
  rewrite <- IHl'. unfold fold_length.
  reflexivity.
Qed.

Definition  fold_map { X Y : Type } ( f : X -> Y ) ( l : list X ) : list Y := 
  fold ( fun x y => f x :: y ) l [].

Example test_map1': map (plus 3) [2;0;2] = fold_map ( plus 3 ) [2;0;2].
Proof.
compute. reflexivity.
Qed.

Example map_foldmap_equal : forall ( X Y : Type ) ( f : X -> Y ) ( l : list X ) ,
  map f l = fold_map f l.
Proof.
 intros X Y f l. induction l as [ | h' l' ].
 Case "l = nil".
  simpl.  reflexivity.
 Case "l = cons h' l'".
  simpl. unfold fold_map. simpl. rewrite -> IHl'. reflexivity.
Qed.

