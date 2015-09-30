Require Export Logic.

Definition even (n : nat) : Prop :=
  evenb n = true.

Theorem even20 : even 20.
Proof. reflexivity. Qed.
Print even20.

Inductive ev : nat -> Prop :=
| ev_O : ev 0
| ev_SS : forall n,  ev n -> ev (S (S n)).

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n. induction n.
  Case "n = O". simpl. apply ev_O.
  Case "n = S n". simpl. apply ev_SS. assumption.
Qed.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum n m : beautiful n -> beautiful m -> beautiful (n + m).

Theorem three_is_beautiful : beautiful 3.
Proof. apply b_3. Qed.

Theorem eight_is_beautiful : beautiful 8.
Proof.
  apply b_sum with (n := 3) (m := 5). apply b_3. apply b_5.
Qed.

Theorem beautiful_plus_eight n : beautiful n -> beautiful (8+n).
Proof.
  intros H. apply b_sum with (n := 3) (m := 5 + n).
  apply b_3. apply b_sum with (n := 5) (m := n). apply b_5.
  assumption.
Qed.

Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros n. intros H. simpl. apply b_sum with (n := n) (m := (n + 0)).
  assumption. SearchAbout (_ + 0 = _). rewrite NPeano.Nat.add_0_r.
  assumption.
Qed.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m * n).
Proof.
  intros n m H. induction m.
  Case "m = O". apply b_0.
  Case "m = S m". simpl. apply b_sum with (n := n ) (m := m * n). assumption.
  assumption.
Qed.
(* This is best example of not following the nose *)
Print b_timesm.

Inductive gorgeous : nat -> Prop :=
| g_0 : gorgeous 0
| g_3 : forall n : nat, gorgeous n -> gorgeous (3 + n)
| g_5 : forall n : nat, gorgeous n -> gorgeous (5 + n).

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H. apply g_5 with (n := 8 + n). apply g_5. apply g_3. assumption.
Qed.

Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
  intros n H. induction n.
  Case "n = O". apply b_0.
  Abort.

Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
  intros n H. induction H.
  Case "H = b_0". apply b_0.
  Case "H = b_3". apply b_sum with (n := 3). apply b_3. assumption.
  Case "H = b_5". apply b_sum with (n := 5). apply b_5. assumption.
Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hn Hm. induction Hn.
  Case "g_0". simpl. assumption.
  Case "g_3". apply g_3 with (n := n + m). assumption.
  Case "g_5". apply g_5 with (n := n + m). assumption.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H. induction H.
  Case "b_0". apply g_0.
  Case "b_3". apply g_3. apply g_0.
  Case "b_5". apply g_5. apply g_0.
  Case "b_sum". apply gorgeous_sum. assumption. assumption.
Qed.

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z. induction x. 
  Case "x = O".
    simpl. rewrite plus_0_r. reflexivity.
  Case "x = S x".
   assert ( H : z + S x = S x + z ).
       apply plus_comm. 
       rewrite H. simpl. rewrite plus_assoc. reflexivity.
Qed.
  
  
Theorem g_times2: forall n, gorgeous n -> gorgeous (2 * n).
Proof.
   intros n H. simpl. induction H.
   Case "g_0". simpl. apply g_0.
   Case "g_3". apply g_3 with (n := n + (3 + n + 0)).
   rewrite plus_0_r. rewrite helper_g_times2. apply g_3 with (n := n + n).
   rewrite plus_0_r in IHgorgeous. assumption.
   Case "g_5". apply g_5 with (n := n + (5 + n + 0)). rewrite helper_g_times2.
   rewrite plus_0_r. rewrite plus_0_r in IHgorgeous. apply g_5 with (n := n + n).
   assumption.
Qed.
Print g_times2.

Theorem g_times2': forall n, gorgeous n -> gorgeous (2 * n).
Proof.
  intros n H. apply beautiful__gorgeous with (n := 2 * n).
  apply b_timesm.  apply  gorgeous__beautiful. assumption.
Qed.
(* prevous proof is about moving gorgeous (2 * n ) => beautiful n 
and beautiful n to gorgeous n *)


Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n H. induction H. unfold even. simpl. reflexivity.
  unfold even. simpl. assumption.
Qed.

Theorem l : forall n, ev n.
Proof.
  induction n. apply ev_O.
  Abort.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m Hn Hm. induction Hn.
  Case "ev_O". simpl. assumption.
  Case "ev_n". simpl. apply ev_SS. assumption.
Qed.

Theorem ev_minus2: forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n H. induction H. simpl. apply ev_O.
  simpl. assumption.
Qed.

Theorem ev_minus2': forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n H. inversion H. simpl. apply ev_O.
  simpl. assumption.
Qed.

Theorem ev_minus2'': forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n H. destruct H eqn: Ht. simpl. apply ev_O.
  simpl. assumption.
Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H. inversion H. assumption.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. apply SSev__even in H. apply SSev__even in H. assumption.
Qed.

Theorem SSSSev__even' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H. inversion H1. assumption.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1.
  inversion H3.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m E1 E2. induction E2.
  Case "ev_O". assumption.
  Case "ev_SS". apply IHE2. simpl in E1. inversion E1. assumption.
Qed.

Theorem ev_ev_even : forall n m,
   ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1. induction E1. intros. simpl. assumption.
  intros H. simpl. apply ev_SS. apply IHE1. assumption.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H1 H2.

(*

2 subgoals, subgoal 1 (ID 720)
  
  n : nat
  m : nat
  p : nat
  H1 : ev (n + m)
  H2 : ev (n + p)
  ============================
   ev m

subgoal 2 (ID 721) is:
 ev p

I am not able to extact the any information from H1 and H2 so stuck 
 *)
Abort.

Inductive ev_list {X : Type} : list X -> Prop :=
| el_nil : ev_list []
| el_cc x y l : ev_list l -> ev_list ( x :: y :: l).

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof.
  intros X l H. induction H.
  Case "el_nil". apply ev_O.
  Case "el_cc". simpl. apply ev_SS. apply IHev_list.
Qed.

Lemma ev_length__ev_list:
  forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. induction H.
  Case "ev_O".
  {
    induction l.
    SCase "[]". intros. apply el_nil.
    SCase "Cons n l". intros H. inversion H.
  }
  Case "ev_SS".
  {
    intros l H2. destruct l.
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "{x :: y :: l]". apply el_cc. apply IHev. inversion H2. reflexivity.
  }
Qed.

Inductive pal {X : Type} : list X -> Prop :=
| empty : pal []
| oneelem : forall x,  pal [x]
| manyelem : forall x l, pal l -> pal ( x :: l ++ [x]).

Theorem snoc_list : forall (X : Type) (l : list X) (n : X),
                          snoc l n = l ++ [n].
Proof.
    induction l.
    Case "l = nil". reflexivity.
    Case "l = cons n l". simpl. intros n0. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall  (X : Type) (l1 l2 l3 : list X),
                        (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    induction l1 as [ | n l'].
    Case "l1 = nil". reflexivity.
    Case "l1 = cons n l'".
    simpl. intros l2 l3. rewrite IHl'. reflexivity.
Qed.

Theorem pal_app_rev : forall (X : Type) (l : list X), pal (l ++ rev l).
Proof.
  intros X l. induction l.
  Case "nil". simpl. apply empty.
  Case "Cons n l". simpl. rewrite snoc_list.
  rewrite <- app_assoc. apply manyelem. assumption.
Qed.

Lemma rev_list : forall ( X : Type ) ( a : X ) ( l : list X ),
  rev ( l ++ [a] ) = a :: rev l.
Proof.
  intros X a l. induction l as [ | v' l'].
  Case "l = nil".
     reflexivity.
  Case "l = Cons v' l'".
    simpl. rewrite -> snoc_list. rewrite -> snoc_list.
    rewrite IHl'. simpl. reflexivity.
Qed.

Theorem pal_rev : forall (X : Type) (l : list X),
                    pal l -> l = rev l.
Proof.
  intros X l H. induction H.
  Case "empty". simpl. reflexivity.
  Case "oneelem". simpl. reflexivity.
  Case "manyelem". simpl. rewrite snoc_list. rewrite rev_list. simpl.
  rewrite <- IHpal. reflexivity.
Qed.

Theorem rev_pal : forall (X : Type) (l : list X),
                    l = rev l -> pal l.
Proof.
  intros X l H. destruct l.
  Case "nil". apply empty. destruct l.
  Case "[x]". apply oneelem.
  Case "x :: y :: l". simpl in H. rewrite snoc_list in H. rewrite snoc_list in H.
  rewrite app_assoc in H.
Abort.

Inductive le : nat -> nat -> Prop :=
| le_n n : le n n
| le_S n m : le n m -> le n (S m).


Notation "m <= n" := (le m n).
Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply (le_S 3 4). apply (le_S 3 3). apply (le_n 3).
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n, square_of n (n * n).

Theorem square3 : square_of 3 9.
Proof.
  apply sq.
Qed.

Inductive next_nat : nat -> nat -> Prop :=
  nn : forall n, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
  assumption.
  apply le_S. apply IHle. assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n. apply le_n. apply le_S. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H. apply le_n. apply le_S. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.  generalize dependent n. induction m.
  Case "m = O". intros n H. inversion H. apply le_n. inversion H2.
  Case "m = S m". intros n H. inversion H.
  apply le_n. apply le_S. apply IHm. apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. generalize dependent a. induction b.
  Case "b = O". simpl. intros a. rewrite plus_0_r. apply le_n.
  Case "b = S b". intros a. SearchAbout ( _ + S _).
  rewrite NPeano.Nat.add_succ_r. apply le_S. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
                    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt. intros n1 n2 m H. split.
  Case "left". inversion H.
Abort.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros n m H. apply le_S. assumption.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m H. generalize dependent m. induction n.
  Case "n = O". intros m H. unfold ble_nat in H. induction m.
  apply le_n. apply le_S. assumption.
  Case "n = S n". intros m H. induction m. inversion H. simpl in H. apply IHn in H.
  apply n_le_m__Sn_le_Sm in H. assumption.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros n m H. generalize dependent n. induction m.
  Case "m = O". intros n H. inversion H. reflexivity.
  Case "m = S m".
  {
    induction n.
    simpl. intros H. reflexivity.
    simpl. intros H. apply IHm. apply Sn_le_Sm__n_le_m in H. assumption.
  }
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros n m o H1 H2. apply ble_nat_true in H1. apply ble_nat_true in H2.
  apply le_ble_nat. generalize dependent H2. generalize dependent H1.
  apply le_trans.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not. intros n m H1 H2. apply le_ble_nat in H2.
  rewrite H1 in H2. inversion H2.
Qed.

Inductive sortedlist : list nat -> Prop :=
| nilsorted : sortedlist []
| onesorted : forall x, sortedlist [x]
| morsorted : forall x y ys,
                le x y -> sortedlist (y :: ys) -> sortedlist (x :: y :: ys).

Theorem sorted : sortedlist [1; 2; 3].
Proof.
  apply morsorted. apply le_S. apply le_n.
  apply morsorted. apply le_S. apply le_n.
  apply onesorted.
Qed.

Theorem sorted_inv : forall (n : nat) (l : list nat),
                       sortedlist (n :: l) -> sortedlist l.
Proof.
  intros n l H. induction l.
  Case "l = []". apply nilsorted.
  Case "Cons n l". inversion H. assumption.
Qed.

Module R.

  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

  (* R 1 1 2 is provalbe. c2 -> c3 -> c1 *)
  Theorem provalber112 : R 1 1 2.
  Proof.
    apply c2. apply c3. apply c1.
  Qed.

  
  Theorem provalber226 : R 2 2 6.
  Proof.
    apply c3. apply c3. apply c5.
    apply c3. apply c3.
  Abort.
End R.

Inductive subseq {X : Type} : list X -> list X -> Prop :=
| emptysubseq : forall l, subseq [] l
| dropsubseq : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2)
| keepsubseq : forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2).

Example subseqexample : subseq [1; 2; 3] [5; 6; 1; 9; 9; 2; 7; 3; 8].
Proof.
  apply dropsubseq. apply dropsubseq. apply keepsubseq.
  apply dropsubseq. apply dropsubseq. apply keepsubseq.
  apply dropsubseq. apply keepsubseq. apply emptysubseq.
Qed.

Theorem subseqreflexive : forall (X : Type) (l : list X), subseq l l.
Proof.
  intros X l. induction l.
  Case "l = []". apply emptysubseq.
  Case "l = x :: l". apply keepsubseq. apply IHl.
Qed.

Lemma app_right : forall (X : Type) (l : list X), l ++ [] = l.
Proof.
  intros X l. induction l.
  Case "l = []". reflexivity.
  Case "l = Cons n l".
  {
    simpl. rewrite IHl. reflexivity.
  }
Qed.

Theorem subseq_app : forall (X : Type) (l1 l2 l3 : list X),
                       subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros X l1 l2 l3 H. induction H.
  Case "emptysubseq". apply emptysubseq.
  Case "dropsubseq". simpl. apply dropsubseq. assumption.
  Case "keepsubseq". simpl. apply keepsubseq. assumption.
Qed.

Theorem subseq_trans : forall (X : Type) (l1 l2 l3 : list X),
                         subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros X l1 l2 l3 H1 H2. induction H1.
  Case "emptysubseq". apply emptysubseq.
Abort.

Inductive R : nat -> list nat -> Prop :=
 | c1 : R 0 []
 | c2 : forall n l, R n l -> R (S n) (n :: l)
 | c3 : forall n l, R (S n) l -> R n l.

(* first  provable. second third is not *)

Theorem r210 : R 2 [1; 0].
Proof. apply c2. apply c2. apply c1. Qed.
Theorem r11210 : R 1 [1;2;1;0].
Proof. Abort.
Theorem r63210 : R 6 [3;2;1;0].
Proof. Abort.

Check (2 + 2 = 4).
Check (ble_nat 2 3 = false).
Check (beautiful 8).
Check (2 + 2 = 5).
Check (beautiful 4).
Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. compute. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. unfold plus_fact. reflexivity. Qed.

Check (even 3).
Check (even 4).
Check even.

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.
Check teen.

Definition true_for_zero (P : nat -> Prop) : Prop := P 0.

Definition true_for_all_number (P : nat -> Prop) : Prop :=
  forall n, P n.

Definition preserverd_by_S (P : nat -> Prop) : Prop :=
  forall n, P n -> P (S n).

Definition natural_number_induction_valid : Prop :=
  forall (P : nat -> Prop),
    true_for_zero P -> preserverd_by_S P -> true_for_all_number P.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if evenb n then Peven n else Podd n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even. destruct (evenb n) eqn:Hev.
  apply H2. unfold oddb. rewrite Hev. simpl. reflexivity.
  apply H1. unfold oddb. rewrite Hev. simpl. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  unfold combine_odd_even. unfold oddb.
  assert (forall n, negb (evenb n) = true -> evenb n = false).
  {
    intros n. destruct (evenb n) eqn:Hev.
    Case "true". intros H. simpl in H. inversion H.
    Case "false". simpl. intros H. reflexivity.
  }
  intros Podd Peven n H1 H2. apply H in H2. rewrite H2 in H1. assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  unfold combine_odd_even, oddb.
  assert (forall n, negb (evenb n) = false -> evenb n = true).
  {
    intros n. destruct (evenb n) eqn: Hev.
    Case "true". intros H. reflexivity.
    Case "false". simpl. intros H. inversion H.
  }
  intros Podd Peven n H1 H2. apply H in H2. rewrite H2 in H1. assumption.
Qed.

(* finished all the problems *)
