Set Implicit Arguments.

Require Import List.
Require Import Monads.
Require Import MonoidMonadTrans.
Require Import Quicksort.
Require Import Plus.
Require Import MonoidTreeMonad.

Import mon_nondet.

Section contents.

  Variable E: SortOrder.E.

  Definition M: Monad := MonoidMonadTrans.M NatAddMonoid NeTreeMonad.ext.

  Definition cmp (x y: E): M comparison :=
    @ret NeTreeMonad.M _ (1%nat, SortOrder.Ecmp E x y).

  Definition pick := MonoidTreeMonad.pick NatAddMonoid.

  Lemma Mext: extMonad M.
  Proof MonoidMonadTrans.Mext NatAddMonoid NeTreeMonad.ext.

  Lemma partition d l: partition M cmp d l = ne_tree.Leaf (length l, simplerPartition E d l).
  Proof with auto.
    induction l...
    simpl.
    rewrite (@mon_assoc (NeTreeMonad.M)).
    rewrite IHl.
    simpl.
    rewrite plus_0_r...
  Qed.

  Definition qs := qs cmp pick.

End contents.
