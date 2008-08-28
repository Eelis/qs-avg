
Set Implicit Arguments.

Require Import Util.
Require Import Le.
Require Import EqNat.
Require Import Compare_dec.
Require Import Bool.
Require Import Lt.
Require Import ListUtils.
Require Import List.
Require Import Compare_dec.
Require Import Monads.
Require Import MonoidMonadTrans.
Require Import nats_below.
Require Import Quicksort.
Require Import MonoidExpec.
Require QsParts.
Require Import SortOrder.
Require Import Indices.
Require Import Arith.
Require Import NatBelow.
Require Import Bvector.

Import mon_nondet.

Section contents.

  Variable (e: E) (ol: list e).

  (* todo: use:

  Inductive UnordNatPair: Set := unord_nat_pair (x y: nat): x <= y -> UnordNatPair.

  Definition mk_unord_nat_pair (x y: nat): UnordNatPair :=
    match le_lt_dec x y with
    | left p => unord_nat_pair p
    | right p => unord_nat_pair (lt_le_weak _ _ p)
    end.

  *)

  Definition monoid := ListMonoid.M (nat * nat).

  Definition M: Monad := MonoidMonadTrans.M monoid NeTreeMonad.ext.

  Lemma Mext: extMonad M.
  Proof MonoidMonadTrans.Mext monoid NeTreeMonad.ext.

  Definition unordered_nat_pair (x y: nat): nat * nat :=
    if le_lt_dec x y then (x, y) else (y, x).

  Definition cmp (x y: Index e ol): M comparison
    := ret (unordered_nat_pair x y :: nil, Ecmp e (subscript x) (subscript y)).

  Definition homo: monoidHomo monoid NatAddMonoid (fun x => length x).
  Proof with auto. apply Build_monoidHomo... simpl. intros. rewrite app_length... Qed.

  Definition pick := MonoidTreeMonad.pick monoid.

  Require Import Rdefinitions.

  Lemma partition d (l: list (Index e ol)):
    partition M cmp d l =
    ne_tree.Leaf (map (fun i: Index e ol => unordered_nat_pair i d) l, simplerPartition (UE e ol) d l).
  Proof with auto. (* todo: rename *)
    induction l...
    simpl.
    rewrite (@mon_assoc (NeTreeMonad.M)).
    rewrite IHl.
    simpl.
    rewrite app_nil_r...
  Qed.

  Lemma simplePartition_component (ee: E) i cr l:
    proj1_sig (simplerPartition ee i l) cr =
      filter (fun f => unsum_bool (cmp_cmp (Ecmp ee f i) cr)) l.
  Proof with auto.
    induction l...
    simpl.
    rewrite IHl.
    destruct (Ecmp ee a i); destruct cr...
  Qed.

  Section Uqs_ind.

    Variable P: list (Index e ol) -> M (list (Index e ol)) -> Prop.
    Hypothesis Pnil: P nil (ret nil).

    Hypothesis Pcons: forall n (v: vector (Index e ol) (S n)),
      (forall x0 cr, P (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) cr)) (vec.remove v x0)) (qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) cr)) (vec.remove v x0)))) ->
      P v
      (ne_tree.Node
          (ne_list.map
            (fun x0: natBelow (S n) =>
              ne_tree.map
                (map_fst (C:=list (Index e ol)) (app (map (fun i0: Index e ol => unordered_nat_pair i0 (vec.nth v x0)) (vec.remove v x0))))
                (foo <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Lt)) (vec.remove v x0));
                bar <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Gt)) (vec.remove v x0));
                ret (foo ++ (vec.nth v x0 :: filter (fun f0: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f0 (vec.nth v x0)) Eq)) (vec.remove v x0)) ++ bar)))
            (nats_below_S n))).

    Theorem qs_ind: forall l, P l (qs cmp pick l).
    Proof with auto.
      apply QsParts.rect...
        apply Mext.
      intros.
      unfold QsParts.body.
      replace (QsParts.selectPivotPart M pick cmp v) with (ne_tree.Node (ne_list.map (fun x0: natBelow (S n) => ne_tree.map (map_fst (app (map (fun i0: Index e ol => unordered_nat_pair i0 ((vec.nth v x0))) (vec.remove v x0)))) (
      foo <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Lt)) (vec.remove v x0));
      bar <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Gt)) (vec.remove v x0));
      ret (m:=NeTreeMonad.M) (nil, foo ++ (vec.nth v x0 :: filter (fun f0: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f0 (vec.nth v x0)) Eq)) (vec.remove v x0)) ++ bar))) (nats_below_S n))).
        simpl @ret in Pcons.
        Focus 1.
        specialize (Pcons v).
        simpl vec.to_list in Pcons.
        apply Pcons. clear Pcons.
        intros.
        apply H.
        rewrite length_filter.
        apply le_lt_trans with (length (vec.to_list (vec.remove v x0))).
          apply count_le.
        rewrite vec.length...
      unfold QsParts.selectPivotPart.
      unfold QsParts.partitionPart.
      unfold QsParts.lowRecPart.
      simpl.
      f_equal.
      repeat rewrite ne_list.map_map.
      apply ne_list.map_ext. intro.
      unfold compose. simpl.
      rewrite NeTreeMonad.map_bind.
      rewrite (@mon_assoc (NeTreeMonad.M)).
      rewrite partition. simpl.
      rewrite (@mon_assoc (NeTreeMonad.M)). simpl.
      rewrite (@mon_assoc (NeTreeMonad.M)). simpl.
      rewrite (@simplePartition_component (UE e ol)).
      apply NeTreeMonad.ext. intro.
      rewrite (@mon_assoc (NeTreeMonad.M)). simpl.
      rewrite NeTreeMonad.map_bind.
            rewrite (@mon_assoc (NeTreeMonad.M)). simpl.
      rewrite (@mon_assoc (NeTreeMonad.M)). simpl.
      rewrite (@simplePartition_component (UE e ol)).
      apply NeTreeMonad.ext. intro.
      unfold compose, map_fst.
      simpl.
      rewrite (@simplePartition_component (UE e ol)).
      reflexivity.
    Qed.

  End Uqs_ind.

  Lemma UcmpDec (x y: nat * nat): { x = y } + { x <> y }.
  Proof with auto.
    intros.
    destruct x.
    destruct y.
    destruct (eq_nat_dec n n1).
      destruct (eq_nat_dec n0 n2).
        subst.
        left...
      right. intro. inversion H...
    right. intro. inversion H...
  Qed.

  Definition UcmpCmp (x y: nat * nat): bool := unsum_bool (UcmpDec x y).

  Definition ijcount (i j: nat): monoid -> nat := count (UcmpCmp (i, j)).

  Lemma ijcount_0 i j l: ~ In (i, j) l -> ijcount i j l = 0.
  Proof with auto.
    unfold ijcount.
    intros.
    apply count_0.
    intros.
    unfold UcmpCmp.
    case_eq (UcmpDec (i, j) x); intros...
    elimtype False.
    apply H.
    rewrite e0...
  Qed.

  Lemma hom_ijcount i j: monoidHomo monoid NatAddMonoid (ijcount i j).
  Proof with auto.
    unfold ijcount.
    intros.
    apply Build_monoidHomo; intros; simpl...
    apply count_app.
  Qed.

  Hint Resolve hom_ijcount.

  Lemma ijcount_eq_count i j: ijcount i j = eq_count UcmpDec (i, j).
  Proof. auto. Qed.

  Definition qs: list (Index e ol) -> M (list (Index e ol)) := qs cmp pick.

End contents.
