Set Implicit Arguments.

Require Import
  List
  util monads list_utils qs_definitions.

Import qs_definitions.mon_det_partition.

Section contents.

  Variable M: Monad.

  Variables (X: Set) (pick: forall T: Set, ne_list.L T -> M T) (cmp: X -> X -> M comparison).

  Definition lowRecPart p (t: list X) (part: {p: Partitioning X |
          Permutation (p Eq ++ p Lt ++ p Gt) t}) :=
    low <- qs _ cmp (proj1_sig part Lt);
    upp <- qs _ cmp (proj1_sig part Gt);
    ret (low ++ p :: proj1_sig part Eq ++ upp).

  Definition partitionPart p (t: list X)
    := partition M cmp p t >>= @lowRecPart p t.

  Definition body (v: list X) :=
    match v with
    | nil => ret nil
    | p :: t => partitionPart p t
    end.

  Definition raw_body (l0 : list X) (qs0 : {l' : list X | length l' < length l0} -> M (list X)) :=
   match l0 as l1 return (l1 = l0 -> M (list X)) with
   | nil => fun _ : nil = l0 => ret nil
   | h :: t =>
       fun Heq_l : h :: t = l0 =>
       part <- partition M cmp h t;
       low <-
       qs0
         (exist (fun l' : list X => length l' < length l0)
            (proj1_sig part Lt) (qs_obligation_1 M qs0 Heq_l part));
       upp <-
       qs0
         (exist (fun l' : list X => length l' < length l0)
            (proj1_sig part Gt) (qs_obligation_2 M qs0 Heq_l part low));
       ret (low ++ h :: proj1_sig part Eq ++ upp)
   end (refl_equal l0).

  Variable e: extMonad M.

  Definition raw_body_ext (l: list X) (qs qs': {l': list X | length l' < length l} -> M (list X)):
    (forall x y, proj1_sig x = proj1_sig y -> qs x = qs' y) -> raw_body l qs = raw_body l qs'.
  Proof with auto.
    unfold raw_body.
    intros.
    destruct l...
    apply e. intro.
    apply bind_eqq...
    intro.
    apply bind_eqq...
    intro...
  Qed.

  Lemma bodies x0:
    raw_body x0 (fun y: {y: list X | length y < length x0} => qs _ cmp (proj1_sig y)) = body x0.
  Proof.
    intros.
    unfold raw_body, body, partitionPart, lowRecPart.
    destruct x0; reflexivity.
  Qed.

  Lemma toBody (l: list X): qs _ cmp l = body l.
  Proof with auto.
    intro.
    unfold qs.
    fold raw_body.
    rewrite fix_measure_utils.unfold.
      rewrite <- bodies.
      unfold qs. fold raw_body...
    intros.
    apply raw_body_ext.
    intros.
    destruct x. destruct y.
    simpl in H0.
    subst...
  Qed.

  Lemma rect (Q: list X -> M (list X) -> Type):
    (Q nil (ret nil)) ->
    (forall h t, (forall y, length y <= length t -> Q y (qs _ cmp y)) -> Q (h :: t) (partitionPart h t)) ->
      forall x, Q x (qs _ cmp x).
  Proof with auto.
    intros.
    unfold qs. fold raw_body.
    apply fix_measure_utils.rect.
      intros.
      apply raw_body_ext.
      intros.
      destruct x1. destruct y.
      simpl in H0.
      subst...
    intros.
    rewrite (raw_body_ext x0 (fun y: {y: list X | length y < length x0} => Wf.Fix_measure_sub (list X) (fun l => length l) (fun _: list X => M (list X)) raw_body (proj1_sig y)) (fun y: {y: list X | length y < length x0} => qs _ cmp (proj1_sig y))).
      rewrite bodies.
      unfold body.
      destruct x0...
      apply X1.
      intros.
      unfold qs. fold raw_body...
      apply H.
      unfold fix_measure_utils.MR.
      simpl.
      auto with arith.
    intros.
    unfold qs. fold raw_body.
    rewrite H0...
  Qed.

End contents.
