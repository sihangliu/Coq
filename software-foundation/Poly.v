Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X  -> list X.

Check nil.
Check cons.

Check nat.
Check Set.

Check cons nat 1 (cons _ 3 (nil nat)).

Fixpoint length (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length X t)
  end.

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : list X :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X : Type) (l : list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.


Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.       

Module MumbleBaz.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

  Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  
  
  (* well typed *)
   Check (d nat (b a 5)). 
   Check  d mumble (b a 5).   
   Check  d bool (b a 5).
   Check  e bool true.
   Check  e mumble (b c 0).
   (* No because b c 0 is of type mumble.*)
   Check c.

   Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.
   (* zero because there is no way to construct baz value*)
   Check baz.
End MumbleBaz.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.
Check app'.
Check app.

Fixpoint length' (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length _ t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _. (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Fixpoint length'' {X : Type} (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length'' t)
  end.

Check @nil.
Definition mynil' := @nil nat.                                               

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | O => @nil X
    | S cnt =>  n :: (repeat n cnt)
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
                    app [] l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc: forall X : Type, forall v : X,
                   forall s : list X, rev (snoc s v) = v :: rev s.
Proof.                   
  induction s.
  Case "s = nil". simpl. reflexivity.
  Case "s = cons n l". simpl. rewrite IHs. simpl. reflexivity.
Qed.

Lemma snoc_rev : forall (X : Type) (n : X) (l : list X),
                   rev (snoc l n) = n :: rev l.
Proof.
  induction l as [ | n' l'].
  Case "l = nil". reflexivity.
  Case "l = cons n' l'". simpl. rewrite IHl'. simpl. reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l.
  Case "l = nil". reflexivity.
  Case "l = cons n l". simpl. rewrite snoc_rev. rewrite IHl. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X, forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  induction l1.
  Case "l1 = nil". simpl. reflexivity.
  Case "l1 = cons n l". intros l2 v. simpl. rewrite IHl1. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
    | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match (l1, l2) with
    | ([], _) => []
    | (_, []) => []
    | (x :: tx, y :: ty) =>
     (x, y) :: combine tx ty
  end.
Check combine.
Check @combine.               

Eval compute in (combine [1;2] [false;false;true;true]). 

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | [] => ([], [])
    | (x, y) :: l' =>
      let (p, q) := split l'
      in ( x :: p, y :: q)
      
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | h :: t => if beq_nat n O then Some h
                else index (pred n) t
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Fixpoint hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | h :: _ => Some h
  end.

Check @hd_opt.
Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f : X * Y -> Z) (x : X) (y : Y) := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem curry_uncurry : forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
                   prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.  reflexivity.
Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
    | nil => nil
    | h :: t => if test h then h :: filter test t
                else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.


Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (ble_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. compute. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. compute. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool)
           (l : list X) : list X * list X :=
  (filter (fun x => test x) l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. compute. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
    | [] => []
    | h :: t => f h :: map f t
  end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_snoc : forall (X Y : Type) (f : X -> Y) ( h : X ) ( l : list X ),
  map f ( snoc l h ) = snoc ( map f l ) ( f h ).
Proof.
 induction l.
 Case "l = nil".
  simpl. reflexivity.
 Case "l = cons h' l'".
  simpl. rewrite IHl. reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type)  (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  induction l.
  Case "l = nil". simpl. reflexivity.
  Case "l = cons n l". simpl. rewrite map_snoc. rewrite IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. compute. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (x : option X) : option Y :=
  match x with
    | None => None
    | Some x => Some (f x)
  end.


Fixpoint filter' (X Y : Type) (f : X -> bool) (l : list X) : list X :=
  match l with
    | [] => []
    | h :: t => if f h then h :: filter' X Y f t
                else filter' X Y f t
  end.

Fixpoint map' (X Y:Type) (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

Fixpoint fold {X Y:Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    | [] => b
    | h :: t => f h (fold f t b)
  end.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat)  => if beq_nat k k' then x else f k'. 

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  destruct b.
  reflexivity. reflexivity.
Qed.

Theorem unfold_example_bad : forall m n,
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
  rewrite  H.
  reflexivity.
Qed.

Theorem override_eq : forall {X:Type} x k (f:nat -> X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite  <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 -> 
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override. rewrite H2. rewrite H1. reflexivity.
Qed.


Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l O.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall (X : Type) (l : list X),
  fold_length l = length l.
Proof.
  induction l.
  Case "l = nil". reflexivity.
  Case "l = cons n l". simpl. unfold fold_length. simpl.
  rewrite <- IHl. unfold fold_length. reflexivity.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => f x :: y  ) l [].

Theorem fold_map_correct : forall (X Y : Type) (l : list X) (f : X -> Y),
                 map f l = fold_map f l.
Proof.
  induction l.
  Case "l = nil". reflexivity.
  Case "l = cons n l". intros f. simpl.
  unfold fold_map. simpl. rewrite IHl. unfold fold_map. reflexivity.
Qed.

Module Church.

  Definition nat := forall (X : Type), (X -> X) -> X -> X.

  Definition one : nat :=
    fun (X : Type) (f : X -> X ) (x : X) => f x.
  Definition two : nat := 
    fun (X : Type) (f : X -> X ) (x : X) => f (f x).
  Definition zero : nat := 
    fun (X : Type) (f : X -> X ) (x : X) => x.
  Definition three : nat := @doit3times.

  Definition succ (n : nat) : nat :=
    fun X f x => f (n X f x).

  Example succ_1 : succ zero = one.
  Proof. compute. reflexivity. Qed.
  Example succ_2 : succ one = two.
  Proof. compute. reflexivity. Qed.
  Example succ_3 : succ two = three.
  Proof. compute. reflexivity. Qed.

  Definition plus (n m : nat) : nat :=
    fun X f x => m X f (n X f x).
  Example plus_1 : plus zero one = one.
  Proof. compute. reflexivity. Qed.
  Example plus_2 : plus two three = plus three two.
  Proof. compute. reflexivity. Qed.
  Example plus_3 : plus (plus two two) three = plus one (plus three three).
  Proof. compute. reflexivity. Qed.

  Definition mult (n m : nat) : nat :=
    fun X f => m X (n X f).
  Example mult_1 : mult one one = one.
  Proof. compute. reflexivity. Qed.
  Example mult_2 : mult zero (plus three three) = zero.
  Proof. compute. reflexivity. Qed.
  Example mult_3 : mult two three = plus three three.
  Proof. compute. reflexivity. Qed.

End Church.
