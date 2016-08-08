Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set :=
| Plus : binop
| Times : binop.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenot (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenot e1) (expDenot e2)
  end.

Eval simpl in expDenot (Const 42).
Eval simpl in expDenot (Binop Plus (Const 42) (Const 1)).

(* target language *)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
    | _ => None
    end
  end.

Fixpoint progDenot (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' =>
    match instrDenote i s with
    | None => None
    | Some s' => progDenot p' s'
    end
  end.

Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 =>
    compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).

Theorem compiler_correct : forall e, progDenot (compile e) nil = Some (expDenot e :: nil).
Proof.
  induction e.
  +  simpl. reflexivity.
  + simpl.
Abort.

Lemma compiler_correct' : forall e p s,
    progDenot (compile e ++ p) s = progDenot p (expDenot e :: s).
Proof.
  induction e.
  + intros. unfold compile. unfold expDenot.
    unfold progDenot at 1. simpl. fold progDenot.
    reflexivity.
  + intros. unfold compile. fold compile.
    unfold expDenot. fold expDenot.
    rewrite app_assoc_reverse. rewrite IHe2.
    rewrite app_assoc_reverse. rewrite IHe1.
    unfold progDenot at 1. simpl. fold progDenot.
    reflexivity.
Qed.

Print compiler_correct'.

Lemma compile_correct' :
  forall e s p, progDenot (compile e ++ p) s = progDenot p (expDenot e :: s).
Proof.
  induction e; crush.
Qed.

Theorem compiler_correct : forall e, progDenot (compile e) nil = Some (expDenot e :: nil).
Proof.
  intros. Check app_nil_end.
  rewrite (app_nil_end (compile e)).
  rewrite compiler_correct'. reflexivity.
Qed.

Inductive type : Set :=
| Nat : type
| Bool : type.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq t : tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop t t1 t2 : tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res) :
  typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => beq_nat
  | TEq Bool => eqb
  | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst s : nat -> tinstr s (Nat :: s)
| TiBConst b : bool -> tinstr b (Bool :: b)
| TiBinop arg1 arg2 res s :
    tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil s : tprog s s
| TCons s1 s2 s3 : tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.


Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n, s)
  | TiBConst _ b => fun s => (b, s)
  | TiBinop _ _ _ _ b =>
    fun s => let '(arg1, (arg2, s')) := s in
                   ((tbinopDenote b) arg1 arg2, s')
               end.


                          
