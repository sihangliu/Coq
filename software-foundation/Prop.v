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

