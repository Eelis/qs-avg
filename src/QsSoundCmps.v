Set Implicit Arguments.

Require Import Util.
Require Import Le.
Require Import Plus.
Require Import Lt.
Require Import List.
Require Import Monads.
Require FixMeasureSubLems.
Require Import MonoidMonadTrans.
Require Import nats_below.
Require Import Compare_dec.
Require Quicksort.
Require QsParts.
Require U.
Require Import Expec.
Require Import ArithLems.
Require Import ListUtils.
Require Import Indices.
Require Import SortOrder.
Require Import NatBelow.
Require Import SkipList.
Require Import Bvector.

Section contents.

  Variables (ee: E) (ol: list ee).

  Import Quicksort.mon_nondet.

  Lemma NeTree_In_Node_inv (A: Set) (r: A) (l: ne_list.L (ne_tree.T A)):
    ne_tree.In r (ne_tree.Node l) -> ne_tree.InL r l.
  Proof.
    intros.
    inversion H.
    assumption.
  Qed.

  Lemma pair_eq_inv (X Y: Set) (x x': X) (y y': Y): (x, y) = (x', y') -> x' = x /\ y' = y.
  Proof.
    intros.
    inversion H.
    split; reflexivity.
  Qed.

  Let qs := @U.qs ee ol.

  Theorem qs_sound_cmps_2: forall l,
    forall r, ne_tree.In r (qs l) ->
      forall i j, In (i, j) (fst r) -> IndexIn i l /\ IndexIn j l.
  Proof with auto with arith. (* simpler version of the one below. doesn't provide (i < j), and doesn't need NoDup l *)
    subst qs. unfold U.qs.
    intro.
    pattern l, (Quicksort.mon_nondet.qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      Focus 1.
      simpl.
      intros r H.
      inversion_clear H.
      simpl.
      intros.
      elimtype False...
    intros.
    cset (NeTree_In_Node_inv H0). clear H0.
    destruct (ne_tree.InL_map_inv _ _ H2). clear H2. destruct H0.
    destruct (ne_tree.In_map_inv _ _ H0). clear H0. destruct H3.
    subst r.
    unfold MonoidExpec.map_fst in H1.
    unfold fst in H1.
    destruct (in_app_or _ _ _ H1); clear H1.
      destruct (In_map_inv H0). clear H0. destruct H1.
      unfold U.unordered_nat_pair in H0.
      unfold IndexIn.
      destruct (le_lt_dec x1 (vec.nth v x)); destruct (pair_eq_inv H0); split; subst; apply in_map.
            apply vec.remove_In with x...
          apply vec.In_nth.
        apply vec.In_nth.
      apply vec.remove_In with x...
    destruct (NeTreeMonad.In_bind_inv _ _ H3). clear H3. destruct H1.
    unfold U.M in H3.
    rewrite MonoidMonadTrans.bind_toLower in H3.
    rewrite (@mon_assoc NeTreeMonad.M ) in H3.
    destruct (NeTreeMonad.In_bind_inv _ _ H3). clear H3. destruct H4.
    extro H0.
    rewrite (@mon_assoc NeTreeMonad.M) in H4.
    rewrite MonoidMonadTrans.ret_toLower in H4.
    rewrite (@mon_lunit NeTreeMonad.M) in H4.
    simpl @fst in H4.
    rewrite (@mon_lunit NeTreeMonad.M) in H4.
    simpl @fst in H4.
    unfold snd in H4.
    inversion_clear H4.
    simpl.
    rewrite app_nil_r.
    intros.
    assert (forall k cr, IndexIn k (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x)) -> IndexIn k v).
      intros.
      unfold IndexIn in *.
      apply (incl_In _ H4).
      apply incl_map.
      apply incl_trans with (vec.remove v x)...
      apply SkipList_incl.
      apply vec.SkipList_remove.
    destruct (in_app_or _ _ _ H0).
      destruct (H x Lt x1 H1 _ _ H5).
      split; apply H4 with Lt...
    destruct (H x Gt x2 H3 _ _ H5).
    split; apply H4 with Gt...
  Qed.


  Theorem qs_sound_cmps: forall l,
    forall r, ne_tree.In r (qs l) -> NoDup l ->
      forall i j, In (i, j) (fst r) -> i < j.
  Proof with auto with arith.
    subst qs. unfold U.qs.
    intro.
    pattern l, (Quicksort.mon_nondet.qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      simpl.
      intros r H.
      inversion_clear H.
      simpl.
      intros.
      elimtype False...
    intros.
    cset (NeTree_In_Node_inv H0). clear H0.
    destruct (ne_tree.InL_map_inv _ _ H3). clear H3. destruct H0.
    destruct (ne_tree.In_map_inv _ _ H0). clear H0. destruct H4.
    subst r.
    unfold MonoidExpec.map_fst in H2.
    unfold fst in H2.
    destruct (in_app_or _ _ _ H2); clear H2.
      destruct (In_map_inv H0). clear H0. destruct H2.
      unfold U.unordered_nat_pair in H0.
      destruct (le_lt_dec x1 (vec.nth v x)); destruct (pair_eq_inv H0)...
        subst.
        apply ne_le_impl_lt...
        intro.
        cset (vec.List_Permutation (vec.perm_sym (vec.remove_perm x v))).
        simpl in H6.
        cset (Permutation_NoDup H1 H6).
        assert (~ In (vec.nth v x) (vec.remove v x)).
          inversion_clear H7...
        apply H8.
        cset(natBelow_unique _ _ H5).
        subst x1...
      subst...
    destruct (NeTreeMonad.In_bind_inv _ _ H4). clear H4. destruct H2.
    unfold U.M in H4.
    rewrite MonoidMonadTrans.bind_toLower in H4.
    rewrite (@mon_assoc NeTreeMonad.M ) in H4.
    destruct (NeTreeMonad.In_bind_inv _ _ H4). clear H4. destruct H5.
    extro H0.
    rewrite (@mon_assoc NeTreeMonad.M) in H5.
    rewrite MonoidMonadTrans.ret_toLower in H5.
    rewrite (@mon_lunit NeTreeMonad.M) in H5.
    simpl @fst in H5.
    rewrite (@mon_lunit NeTreeMonad.M) in H5.
    simpl @fst in H5.
    unfold snd in H5.
    inversion_clear H5.
    simpl.
    rewrite app_nil_r.
    intros.
    assert (forall cr, NoDup (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x))).
      intros.
      apply NoDup_SkipList with v...
      apply SkipList_trans with (vec.remove v x).
        apply SkipList_filter.
      apply vec.SkipList_remove.
    assert (forall k cr, IndexIn k (filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp ee (subscript f) (subscript (vec.nth v x))) cr)) (vec.remove v x)) -> IndexIn k v).
      intros.
      unfold IndexIn in *.
      apply (incl_In _ H6).
      apply incl_map.
      apply incl_trans with (vec.remove v x)...
      apply SkipList_incl.
      apply vec.SkipList_remove.
    destruct (in_app_or _ _ _ H0).
      apply H with x Lt x1...
    apply H with x Gt x2...
  Qed.

  (* The last two lemmas used to be joined together, but that way the NoDup parameter was also needed just to get the first lemma's result. *)

Require Import MonoidExpec.
Require Import Rbase.

  Lemma sound_cmp_expec_0 i j (l: list (Index ee ol)):
    (~ In i l \/ ~ In j l) -> monoid_expec (U.ijcount i j) (qs l) = 0.
  Proof with auto.
(*    subst qs.*)
    intros.
    unfold monoid_expec.
    replace 0 with (INR 0)...
    apply (expec_constant).
    intros.
    unfold compose.
    apply U.ijcount_0.
    intro.
    destruct (qs_sound_cmps_2 l H0 i j )...
    destruct H.
      apply H.
      unfold IndexIn in H2.
      destruct (In_map_inv H2).
      destruct H4.
      cset (natBelow_unique _ _ H4).
      subst...
    apply H.
    unfold IndexIn in H3.
    destruct (In_map_inv H3).
    destruct H4.
    cset (natBelow_unique _ _ H4).
    subst...
  Qed.


End contents.



