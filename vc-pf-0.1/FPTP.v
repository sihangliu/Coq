Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Import ListNotations.

(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(* FPTP counting for a finite inhabited type with decidable equality *)
Section FPTP.

Variable cand : Type.
Variable cand_all : list cand.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Hypothesis cand_inh : cand.

(* intermediate and final states of counting *)
Inductive Node  :=
  winner : cand -> Node                         (* electon winner *)
| state  : (list cand) * (cand -> nat) -> Node  (* election state *).

(* null tally *)
Definition nty : cand -> nat := fun x => 0. 

(* the new tally is the old tally with c's votes incremented by one *)
Definition inc (c:cand) (t: cand -> nat) (nt: cand -> nat) : Prop :=
  (nt c = t c + 1)%nat /\  forall d, d <> c -> nt d = t d.

Inductive Pf (b: list cand) : Node -> Type :=
  ax : forall u t,                              (** start counting **)
  u = b ->                                      (* if the uncounted votes comprise all ballots *)
  t = nty ->                                    (* and the tally is nill *)
  Pf b  (state (u, t))                          (* we may start counting with nil tally and all ballots *)
| c1 : forall u0 c u1 nu t nt,                  (** count one vote **)
  Pf b  (state  (u0 ++[c]++u1, t)) ->           (* if we have an uncounted vote for c *)
  inc c t nt ->                                 (* and the new tally increments c's votes by one *)
  nu = u0++u1 ->                                (* and the vote has been removed from the uncounted votes *)
  Pf b (state (nu, nt))                         (* we continue  with new tally and consume the vote for c *)
| dw : forall c  t,                             (** declare winner **)
  Pf b  (state ([], t)) ->                      (* if all votes have been counted *)
  (forall d : cand, (t d <= t c)) ->            (* and all cands have fewer votes than c *)
  Pf b  (winner c)                              (* then c may be declared the winner *).

(* increment tally for cand by one *)
Definition inct (c:cand) (t: cand -> nat) : cand -> nat :=
  fun d => if (cand_eq_dec c d) then (S (t d)) else (t d).

Lemma inct_ok: forall c:cand, forall t: cand -> nat, inc c t (inct c t).
Proof.
  intros. unfold inc. split.
  unfold inct. destruct (cand_eq_dec c c). omega. contradict n. trivial.
  intros d ass. unfold inct. destruct (cand_eq_dec c d).
  contradict ass. symmetry. trivial. trivial.
Qed.

(* auxilary constructors *)
Definition ax_aux: forall b : list cand,
  Pf b (state (b, nty)).
Proof.
  intros.
  apply (ax b b nty). trivial. trivial.
Defined.

Definition c1_aux: forall b c u t,
  Pf b (state (c::u, t)) -> Pf b (state (u, inct c t)).
Proof.
  intros.
  apply (c1 b [] c u u t (inct c t)).
  replace ([] ++ [c] ++ u) with (c::u).
  assumption. auto. apply (inct_ok c t). auto.
Defined.

Definition dw_aux: forall b t c,
  Pf b (state (([]: list cand), t)) ->
  (forall d : cand, (t d <= t c)) ->
  Pf b (winner c).
Proof.
  intros.
  apply (dw b c t). assumption. assumption.
Defined.

(* we can always reach a state where all votes are counted *)
Lemma cnt_all : forall b u t,
  Pf b (state (u, t)) -> existsT nt, Pf b (state ([]: list cand, nt)).
Proof.
  intro b.
  induction u as [| u0 us IHus].
  intros t p. exists t. assumption.
  intros t p. 
  specialize (IHus (inct u0 t) (c1_aux b u0 us t p)).
  assumption.
Defined.

(* nonempty lists have a minimal element wrt a nat-valued measure *)
Lemma list_max : forall A:Type, forall l: list A, forall f: A -> nat,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->f b <= f m))).
Proof.
  intros A l f.
  induction l as [| l0 ls IHls].
  (* l = [] *)
  left. trivial.
  (* l = l0::ls *)
  right. destruct IHls as [lsemp | lsnemp ].
  (* case ls = [] *)
  exists l0. split. apply (in_eq l0 ls).
  intros b H.
  assert (H0: l0 = b \/ In b ls) by apply (in_inv H).
  destruct H0 as [ eq | ctd].
  replace l0 with b. trivial.
  replace ls with ([]: list A) in ctd. contradict ctd.
  (* case ls <> [] *)
  destruct lsnemp as [maxls Hmax ]. destruct Hmax as [Hmaxin Hmaxgeq].
  assert (H: {f maxls <= (f l0)}  + {(f l0) <= (f maxls)}) by apply (le_ge_dec (f maxls) (f l0)).
  destruct H as [Hl0 | Hmaxls].
  (* l0 is maxium *)
  exists l0. split. apply (in_eq l0 ls). intros b Hin.
  assert (H: l0 = b \/ In b ls) by apply (in_inv Hin).
  destruct H as [Heq | Hls ]. replace l0 with b. trivial.

  transitivity (f maxls). apply (Hmaxgeq b Hls). assumption.
  (* maxls is maximum *)
  exists maxls. split.
  apply (in_cons l0 maxls ls Hmaxin).
  intros b Hin.
  assert (H: l0 = b \/ In b ls) by apply (in_inv Hin). destruct H as [Heq | Htl].
  replace b with l0. assumption. apply (Hmaxgeq b Htl).
Defined.

(* every list of candidates has a minimal element wrt a nat-valued measure as cans are inhabited *)
Lemma list_cand_max: forall f: cand -> nat, existsT m:cand, forall b: cand, f b <= f m.
Proof.
  intros f. specialize (list_max cand cand_all f).
  intro H. destruct H as [Hemp | Hnemp].
  contradict cand_inh. intro c. specialize (cand_finite c).
  replace cand_all with ([]: list cand) in cand_finite. auto.
  destruct Hnemp as [max H]. destruct H as [Hin Hmax].
  exists max. intro b. apply (Hmax b). apply (cand_finite b).
Defined.

Theorem exists_winner_pf : forall b, existsT w, Pf b (winner w).
Proof.
  intros b.
  assert (p0 : Pf b (state (b, nty))) by apply (ax_aux b).
  assert (H: existsT  t, Pf b (state ([], t))) by apply (cnt_all b b nty p0).
  destruct H as [t p].
  assert (H: existsT w:cand, forall b: cand, t b <= t w).
  apply (list_cand_max t).
  destruct H as [w H].
  exists w.
  apply (dw_aux b t w p H).
Defined.

(* admissibility of weakening (not needed for extraction) *)
Lemma weaken_right_aux : forall b  n, 
  Pf b n -> 
  forall u t, n = state (u, t) -> 
  forall w, Pf (b++w) (state (u++w, t)).
Proof.
  intros b n p.
  induction p.
  (* case ax *)
  intros.
  replace u0 with b. replace t0 with nty.
  apply (ax_aux (b++w)).
  transitivity  t. symmetry. assumption. injection H. intros. assumption.
  transitivity u. symmetry. assumption. injection H. intros. assumption.
  (* case c1 *)
  intros.
  specialize (IHp (u0 ++ [c] ++ u1) t eq_refl w).
  replace ((u0 ++ [c] ++ u1) ++ w) with (u0 ++ [c] ++ (u1 ++ w)) in IHp.
  replace t0 with nt. replace u with (u0 ++ u1).
  replace ((u0 ++ u1) ++ w) with (u0 ++ u1 ++ w).
  apply (c1 (b++w) u0 c (u1 ++ w) (u0 ++ (u1 ++ w)) t nt IHp i eq_refl).
  apply (app_assoc u0 u1 w).
  transitivity nu. auto. injection H. intros. assumption.
  injection H. intros. assumption. simpl.
  apply (app_assoc u0 (c::u1) w).
  (* case dw *)
  intros u0 t0 e0. discriminate e0.
Qed.

Lemma weaken_right: forall b u t, Pf b (state (u, t)) -> 
  forall w, Pf (b++w) (state (u++w, t)).
Proof.
  intros b u t p w.
  apply (weaken_right_aux b (state (u, t)) p u t eq_refl w).
Qed.

Lemma weaken_left_aux : forall b  n, 
  Pf b n -> 
  forall u t, n = state (u, t) -> 
  forall w, Pf (w++b) (state (w++u, t)).
Proof.
  intros b n p.
  induction p.
  (* case ax *)
  intros.
  replace u0 with b. replace t0 with nty.
  apply (ax_aux (w++b)).
  transitivity  t. symmetry. assumption. injection H. intros. assumption.
  transitivity u. symmetry. assumption. injection H. intros. assumption.
  (* case c1 *)
  intros.
  specialize (IHp (u0 ++ [c] ++ u1) t eq_refl w).
  replace (w ++ u0 ++ [c] ++ u1) with ((w ++ u0) ++ [c] ++ u1) in IHp.
  replace t0 with nt. replace u with (u0 ++ u1).
  replace (w ++ u0 ++ u1) with ((w ++ u0) ++ u1).
  apply (c1 (w++b) (w++u0) c u1 ((w ++ u0) ++ u1) t nt IHp i eq_refl).
  symmetry. apply (app_assoc w u0 u1).
  transitivity nu. auto. injection H. intros. assumption.
  injection H. intros. assumption. simpl.
  symmetry. apply (app_assoc w u0 (c::u1)).
  (* case dw *)
  intros u0 t0 e0. discriminate e0.
Qed.

Lemma weaken_left: forall b u t, Pf b (state (u, t)) -> 
  forall w, Pf (w++b) (state (w++u, t)).
Proof.
  intros b u t p w.
  apply (weaken_left_aux b (state (u, t)) p u t eq_refl w).
Qed.

End FPTP.

Section candidates.

(* our candidates given as inductive type and list. *)
Inductive cand := Alice | Bob | Claire | Darren.
Definition cand_all := [Alice; Bob; Claire; Darren].

(* everything below here is independent of the definition of cand *)
(* as long as cand is an inductive type with nullary constructors *)
(* only and all_cands mentions all of them.                       *)

Lemma cand_finite: forall c, In c cand_all.
Proof.
  unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
Qed.

Lemma  cand_eq_dec : forall c d : cand, {c = d} + {c <> d}.
Proof.
  intros a b;
  repeat induction a; 
    repeat (induction b) || (right; discriminate) ||(left; trivial).
Defined.

Lemma cand_inh : cand.
Proof.
  constructor.
Defined.

End candidates.

(* extraction: instantiation and extraction of counting *)
Definition cand_exists_winner_pf := 
  exists_winner_pf cand cand_all cand_finite cand_eq_dec cand_inh.


Extraction Implicit c1 [u0 c u1 t].
Extraction Implicit dw [t].
Extraction Language Haskell.
Extraction "FPTPCode.hs"  cand_exists_winner_pf.
(* run using FPTPWrapper.hs *)
