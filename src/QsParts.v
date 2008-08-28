Set Implicit Arguments.

Require Import Util.
Require Import Le.
Require Import Plus.
Require Import Lt.
Require Import Arith.
Require Import MonoidExpec.
Require Import List.
Require Import Monads.
Require Import ListUtils.
Require Import Coq.Program.Wf.
(*Require Import Wf_nat.*)
Require Import MonoidMonadTrans.
Require Import nats_below.
Require Import MonoidTreeMonad.
Require Quicksort.
Require FixMeasureSubLems.
Require Import NatBelow.
Require Import Bvector.

Import Quicksort.mon_nondet.

Section contents.

  Variable M: Monad.

  Lemma bind_eqq (e: extMonad M) (A B: Set) (m n: M A) (f g: A -> M B): m = n -> ext_eq f g -> (m >>= f) = (n >>= g).
  Proof.
    intros.
    subst.
    apply e.
    assumption.
  Qed.

  Variables (X: Set) (pick: forall T: Set, ne_list.L T -> M T) (cmp: X -> X -> M comparison).

  Definition lowRecPart n (t: vector X (S n)) (i: natBelow (S n)) (part: {p: Partitioning X |
          Permutation (p Eq ++ p Lt ++ p Gt) (vec.remove t i)}) :=
    low <- qs cmp pick (proj1_sig part Lt);
    upp <- qs cmp pick (proj1_sig part Gt);
    ret (low ++ vec.nth t i :: proj1_sig part Eq ++ upp).

  Definition partitionPart n (t: vector X (S n)) (i: natBelow (S n))
    := partition M cmp (vec.nth t i) (vec.remove t i) >>= lowRecPart t i.

  Definition selectPivotPart n (t: vector X (S n)) := pick (nats_below_S n) >>= partitionPart t.

  Definition body n (v: vector X n) :=
    match v with
    | Vnil => ret nil
    | l => selectPivotPart l
    end.

  Definition raw_body (l0: list X) (qs: {l': list X | length l' < length l0} -> M (list X)) :=
    match l0 as l1 return (l1 = l0 -> M (list X)) with
    | nil => fun _ => ret nil
    | h :: t => fun e =>
      i <- pick (nats_below_S (length t));
      part <- partition M cmp (vec.nth (h :: t) i) (vec.remove (h :: t) i);
      low <- qs (exist (fun l': list X => length l' < length l0) (proj1_sig part Lt) (qs_obligation_1 M qs e i part));
      upp <- qs (exist (fun l': list X => length l' < length l0) (proj1_sig part Gt) (qs_obligation_2 M qs e i part low));
      ret (low ++ vec.nth (h :: t) i :: proj1_sig part Eq ++ upp)
    end (refl_equal l0).

  Variable e: extMonad M.

  Definition raw_body_ext (l: list X) (qs qs': {l': list X | length l' < length l} -> M (list X)):
    (forall x y, proj1_sig x = proj1_sig y -> qs x = qs' y) -> raw_body l qs = raw_body l qs'.
  Proof with auto.
    unfold raw_body.
    intros.
    destruct l...
    apply e. intro.
    apply e. intro.
    apply bind_eqq...
    intro.
    apply bind_eqq...
    intro...
  Qed.

  Lemma measure_proof_irrelevant l a a':
    Wf.Fix_measure_F_sub (list X) (fun l => length l) (fun _: list X => M (list X)) raw_body l a =
    Wf.Fix_measure_F_sub (list X) (fun l => length l) (fun _: list X => M (list X)) raw_body l a'.
  Proof with auto.
    intros.
    apply (FixMeasureSubLems.eq_Fix_measure_F_sub (fun l => length l) (fun _: list X => M (list X))).
    intros.
    apply raw_body_ext.
    intros.
    destruct x.
    destruct y.
    simpl in H0.
    subst x1.
    apply H.
  Qed.

  Lemma bodies x0:
    raw_body x0 (fun y: {y: list X | length y < length x0} => qs (M:=M) cmp pick (proj1_sig y)) = body x0.
  Proof.
    intros.
    unfold raw_body, body, selectPivotPart, partitionPart, lowRecPart.
    destruct x0; reflexivity.
  Qed.

  Lemma toBody (l: list X): qs cmp pick l = body l.
  Proof with auto.
    intro.
    unfold qs.
    fold raw_body.
    unfold Wf.Fix_measure_sub.
    rewrite FixMeasureSubLems.F_unfold.
    rewrite <- bodies.
    unfold qs. fold raw_body.
    apply raw_body_ext.
    intros x y j.
    generalize (Acc_inv (lt_wf (length l)) (proj2_sig x)).
    rewrite j.
    intros.
    unfold Wf.Fix_measure_sub.
    apply measure_proof_irrelevant.
  Qed.
(*
  Lemma vec_vec_round_trip  (J: Set) (n: nat) (v: vector J n): vec.from_list (vec.to_list v) = v.
*)

  Lemma toBody_cons (n: nat) (v: vector X (S n)): body v = selectPivotPart v.
    intros.
    rewrite (vec.eq_cons v).
    simpl.
    reflexivity.
  Qed.

  Lemma rect (Q: list X -> M (list X) -> Type):
    (Q nil (ret nil)) ->
    (forall n (v: vector X (S n)), (forall y, length y < S n -> Q y (qs cmp pick y)) -> Q v (selectPivotPart v)) ->
      forall x, Q x (qs cmp pick x).
  Proof with auto.
    intros.
    unfold qs. fold raw_body.
    apply FixMeasureSubLems.recti2.
      intros.
      apply raw_body_ext.
      intros.
      destruct x1. destruct y.
      simpl in H0.
      subst...
    intros.
    rewrite (raw_body_ext x0 (fun y: {y: list X | length y < length x0} => Wf.Fix_measure_sub (list X) (fun l => length l) (fun _: list X => M (list X)) raw_body (proj1_sig y)) (fun y: {y: list X | length y < length x0} => qs cmp pick (proj1_sig y))).
      rewrite bodies.
      unfold body.
      destruct x0...
      simpl.
      rewrite <- (vec.list_round_trip (x0 :: x1)).
      apply X1.
      intros.
      unfold qs. fold raw_body...
    intros.
    unfold qs. fold raw_body.
    rewrite H...
  Qed.

End contents.
