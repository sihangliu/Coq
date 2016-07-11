Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check (nil nat).
Check cons.
Check (cons _ 2 (nil _)).

Check (cons nat 2 (cons nat 3 (nil _))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.


Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. auto. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. auto. Qed.

Module MumbleGrumble.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

  Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  (* yes *)
  Check (d _ (b a 5)).
  Check (d mumble (b a 5)).
  Check  d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).
  (* no *)
  (* Check e bool (b c 0). *)
  Check c.
End MumbleGrumble.


Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X : Type} : Type :=
| nil' : list'
| cons' : X -> list' -> list'.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.
Check @nil.
Check @nil nat.  

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
      l ++ [] = l.
Proof.
  intros X l. induction l.
  + auto.
  + simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  simpl. induction l.
  + auto.
  + simpl. rewrite IHl. auto.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1. induction l1.
  + auto.
  + simpl. intros l2. rewrite IHl1. auto.
Qed.

Theorem rev_app_distr: forall (X : Type) (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1. induction l1.
  + simpl. intros l2. rewrite  app_nil_r. reflexivity.
  + simpl. intros l2. rewrite IHl1. rewrite <- app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type), forall (l : list X),
      rev (rev l) = l.
Proof.
  intros X l. induction l.
  + auto.
  + simpl. assert (H : forall (x : X) (l : list X), rev (l ++ [x]) = x :: rev l).
    {
      intros x0 l0. induction l0.
      + auto.
      + simpl. rewrite IHl0. auto.
    }
    rewrite H. rewrite IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Check (pair 1 2).

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | h1 :: t1, h2 :: t2 => (h1, h2) :: combine t1 t2
  end.

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X * list Y) :=
  match l with
  | nil => (nil, nil)
  | (a, b) :: t =>
    let (remx, remy) := split t in
    (a :: remx, b :: remy)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  auto.
Qed.  

Inductive option (X : Type) : Type :=
| None : option X
| Some : X -> option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | h :: t => if Basics.beq_nat n O then Some h
             else nth_error t (pred n)
  end.


Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. auto. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. auto. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. auto. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. auto. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. auto. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).
Check @doit3times.  

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. auto. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. auto. Qed.


Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t =>
    if f h then h :: filter f t else filter f t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. simpl. auto. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  Basics.beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
    = [ [3]; [4]; [8] ].
Proof. simpl. auto. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. auto. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. auto. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. auto. Qed.

Example test_anan_fun' :
  doit3times (fun n => n * n) 2 = 256.
Proof. auto. Qed.

Example test_filter2' :
  filter (fun l => Basics.beq_nat (length l) 1) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. auto. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (Basics.evenb n) (Basics.blt_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. compute. auto. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. auto. Qed.

Definition partition {X : Type} (f : X -> bool) (l : list X) : (list X * list X) :=
  (filter (fun n => f n) l, filter (fun n => negb (f n)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. compute. auto. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. compute. auto. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (lx : list X) : list Y :=
  match lx with
  | nil => nil
  | h :: t =>
    (f h) :: map f t
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. auto. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. auto. Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l.
  + auto.
  + simpl. assert (H : forall (X Y : Type) (f : X -> Y) (x : X) (l : list X),
                      map f (l ++ [x]) = map f l ++ [f x]).
    {
      intros X0 Y0 f0 x0 l0. induction l0.
      + auto.
      + simpl. rewrite IHl0. reflexivity.
    }
    rewrite H. rewrite IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. auto. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (x : option X) : option Y :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.



Module NoImplicitTypes.
  Fixpoint filter (X : Type) (f : X -> bool) (l : list X) : list X :=
    match l with
    | nil => nil
    | h :: t => if f h then h :: filter X f t else filter X f t
    end.

  Fixpoint map (X Y : Type) (f : X -> Y) (l : list X) : list Y :=
    match l with
    | nil => nil
    | h :: t =>
      f h :: map X Y f t
    end.

  Example test_filter1: filter nat evenb [1;2;3;4] = [2;4].
  Proof. auto. Qed.

  Example test_filter2':
    filter (list _) (fun l => Basics.beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
  Proof. compute. reflexivity. Qed.
  Check @test_filter2'.

  Example test_map1: map nat nat (fun x => plus 3 x) [2;0;2] = [5;3;5].
  Proof. auto. Qed.

  Example test_map2: map nat bool oddb [2;1;2;5] = [false;true;false;true].
  Proof. auto. Qed.

  Example test_map3:
    map nat (list bool) (fun n => [evenb n;oddb n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
  Proof. auto. Qed.

End NoImplicitTypes.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b) (* fold f t (f h b) *)
  end.

Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. compute. auto. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. auto. Qed.


Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. auto. Qed.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. auto. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. auto. Qed.

Check plus.

Module Vector.
  Inductive Vect (X : Type) : nat -> Type :=
  | nil : Vect X O
  | cons : forall (n : nat),  X ->  Vect X n -> Vect X (S n).

  Check @nil.
  Check @cons.
  Arguments nil {X}.
  Arguments cons {X} {n} _ _.
  Check cons 1 (cons 2 nil).

  Fixpoint app {X : Type} {n m : nat} (lx : Vect X n) (ly : Vect X m) : Vect X (n + m) :=
    match lx with
    | nil => ly
    | cons h t => cons h (app t ly)
    end. 

  Fixpoint map {X Y : Type} {n : nat} (f : X -> Y) (lx : Vect X n) : Vect Y n :=
    match lx with
    | nil => nil
    | cons h t => cons (f h) (map f t)
    end.                   
    
    
  Definition zip {X Y : Type} {n : nat} (lx : Vect X n) (ly : Vect Y n) : Vect (X*Y) n.
  Proof.
    destruct lx.
    constructor.
    induction ly.
    constructor.
    apply cons.
    exact (x, x0).
    exact IHly.
  Defined.

  Definition filter {X : Type} {n : nat} (l : Vect X n) : {p : {m : nat & Vect X m} | projT1 p <= n}.
  Proof. induction n.
  Abort.
  
End Vector.


Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. auto. Qed.

Theorem fold_length_correct : forall (X : Type) (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
  + auto.
  + simpl. unfold fold_length. simpl.
    unfold fold_length in IHl. rewrite IHl. reflexivity.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x acc => f x :: acc) l nil.

Theorem map_fold :
  forall (X Y : Type)(f : X -> Y) (l : list X), map f l = fold_map f l.
Proof.
  intros X Y f l. induction l.
  + auto.
  + simpl. unfold fold_map.
    simpl. unfold fold_map in IHl. rewrite <- IHl.
    reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
           (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map22: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. auto. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. unfold prod_uncurry.
  unfold prod_curry. simpl. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. unfold prod_curry.
  unfold prod_uncurry. destruct p.
  simpl. reflexivity.
Qed.

Module Chruch.

  Definition nat := forall (X : Type), (X -> X) -> X -> X.
  Definition one :=
    fun (X : Type) (f : X -> X) (x : X) => f x. 

  Definition two :=
    fun (X : Type) (f : X -> X) (x : X) => f (f x).

  Definition zero :=
    fun (X : Type) (f : X -> X) (x : X) => x.

  Definition three : nat := @doit3times.

  Check zero.
  (* Come here and solve it again *)

End Chruch.
