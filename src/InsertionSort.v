
Set Implicit Arguments.

Require Import Bool.
Require Import Lt.
Require Import Recdef.
Require Import List.
Require Import Ring.
Require Import Plus.
Require Import Mult.
Require Import Compare_dec.
Require Import MonoidMonadTrans.
Require Import Le.
Require Import Div2.
Require Import Arith.
Require Import Wf_nat.
Require Import Monads.
Require Import Arith.
Require Import Omega.
Require Import ArithLems.
Require Import ListUtils.

Definition numbers := 3 :: 2 :: 5 :: 9 :: 7 :: 6 :: 1 :: 0 :: 4 :: 8 :: nil.

Module plain.
Section plain.

  Variables (T: Set) (le: T -> T -> bool).

  Fixpoint insert (l: list T) (x: T): list T :=
    match l with
    | nil => x :: nil
    | h :: t => if le x h then x :: h :: t else h :: insert t x
    end.

  Definition isort: list T -> list T := fold_left insert nil.

End plain.
End plain.

Module pairs.
Section pairs.

  Variables (T: Set) (le: T -> T -> bool).

  Fixpoint insert (l: list T) (x: T) {struct l}: nat * list T :=
      match l with
      | nil => (0, x :: nil)
      | h :: t =>
          if le x h
            then (1, x :: h :: t)
            else let (n, t') := insert t x in (S n, h :: t')
      end.

  Fixpoint insert_many (l l': list T) {struct l'}: nat * list T :=
      match l' with
      | nil => (0, l)
      | h :: t =>
          let (n, u) := insert l h in
          let (m, v) := insert_many u t in
            (n + m, v)
      end.

  Definition isort: list T -> (nat * list T) := insert_many nil.

End pairs.
End pairs.

Eval compute in (pairs.isort leb numbers).

Module monadic.
Section monadic.

  Variables (M: Monad) (T: Set) (le: T -> T -> M bool).

  Fixpoint insert (l: list T) (x: T): M (list T) :=
    match l with
    | nil => ret (x :: nil)
    | h :: t =>
        r <- le x h ;
        if r
          then ret (x :: h :: t)
          else t' <- insert t x ; ret (h :: t')
  end.

  Lemma insert_unfold: forall l x, insert l x =
    match l with
    | nil => ret (x :: nil)
    | h :: t =>
        r <- le x h ;
        if r then ret (x :: h :: t) else t' <- insert t x ; ret (h :: t')
    end.
  Proof. destruct l; auto. Qed.

  Definition isort: list T -> M (list T) := foldlM insert nil.

  Hypothesis run: forall U, M U -> U.
  Implicit Arguments run [U].
  Hypothesis run_ret: forall (U: Set) (x: U), run (ret x) = x.
  Hypothesis run_bind: forall (A B: Set) (x: M A) (f: A -> M B),
    run (x >>= f) = run (f (run x)).

  Lemma insert_length (x: T) (l: list T):
    length (run (insert l x)) = S (length l).
  Proof with simpl; auto with arith.
    induction l...
      rewrite run_ret...
    rewrite run_bind.
    destruct (run (U:=bool) (le x a)).
      rewrite run_ret...
    unfold liftM.
    rewrite run_bind.
    rewrite run_ret...
  Qed.

End monadic.
End monadic.

Section quadratic.

  Import monadic.

  Definition plain_leb: nat -> nat -> IdMonad.M bool := leb.

  (*Eval compute in (isort _ plain_leb numbers).*)

  Variables (T: Set) (le: T -> T -> bool).

  Definition mle (x y: T): SimplyProfiled bool := (1, le x y).

  Lemma insert_cost (l: list T) (x: T): cost (insert _ mle l x) <= length l.
  Proof with auto with arith.
    induction l...
    intros.
    rewrite insert_unfold, bind_cost.
    destruct (result (mle x a)).
      rewrite return_cost.
      simpl...
    rewrite bind_cost, return_cost.
    deep_le_trans (IHl x)...
    simpl.
    omega.
  Qed.

  Lemma fold_insert_cost (x y: list T):
    cost (foldlM (insert _ mle) y x) <= length y * length x + div2 (sqrd (length x)).
  Proof with auto with arith; try omega.
    induction x; intros.
      simpl. omega.
    rename a into h, x into t.
    rewrite foldlM_cons.
    rewrite bind_cost.
    deep_le_trans (insert_cost y h)...
      apply plus_le_compat...
      apply insert_cost.
    deep_le_trans (IHx (result (insert _ mle y h)))...
    clear IHx.
    rewrite insert_length...
    simpl length.
    simpl mult.
    rewrite <- mult_n_Sm.
    apply le_trans with ((length y * length t + length y) + (length t + div2 (sqrd (length t))))...
    apply plus_le_compat_l.
    rewrite plus_comm.
    apply div2_sqrdSn.
  Qed.

  Theorem insertion_sort_quadratic (l: list T):
    cost (isort _ mle l) <= div2 (sqrd (length l)).
  Proof fun l => fold_insert_cost l nil.

End quadratic.
