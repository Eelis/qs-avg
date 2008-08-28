
Set Implicit Arguments.

Require Import Util.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Import Bool_nat.
Require Import ArithLems.
Require Import NatBelow.
Require Import List.
Require Import Monads.
Require Import Bool.
Require Import Compare_dec.
Require Import EqNat.
Require Import Relation_Definitions.
Require FixMeasureSubLems.
Require Import MonoidMonadTrans.
Require Import Expec.
Require Import MonoidExpec.
Require Import nats_below.
Require Import ListUtils.
Require Import sums_and_averages.
Require Quicksort.
Require QsParts.
Require U.
Require Import Indices.
Require Import QsSoundCmps.
Require Import QsCaseSplit.
Require Import QsCases.
Require Import Fourier.
Require Import Rbase.
Require Import SortOrder.

Import Quicksort.mon_nondet.

Lemma sigh n: 0 <= 2 * / INR (S n).
Proof with auto with real.
  intros.
  unfold Rdiv...
  apply Rle_mult_inv_pos...
Qed.

Hint Resolve sigh.

Require Import Minus.

Section contents.

  Variables (ee: E) (ol: list ee).

  Lemma arith_part n (b i j: nat):
    (b <= i)%nat -> (i < j)%nat -> (j < b + S n)%nat ->
    (2 * / INR (S (j - i)) * INR (i - b) + (1 + (0 + (1 + 2 * / INR (S (j - i)) * INR (b + n - j))))) / INR (S n) = 2 / INR (S (j - i)).
  Proof with auto with real.
    intros.
    repeat rewrite <- Rplus_assoc.
    rewrite Rplus_0_r.
    rewrite plus_comm.
    replace
    (2 * / INR (S (j - i)) * INR (i - b) + 1 + 1 + 2 * / INR (S (j - i)) * INR (n + b - j)) with
    (2 * / INR (S (j - i)) * (INR (i - b) + INR (n + b - j)) + 2).
      rewrite <- plus_INR.
      replace ((i - b + (n + b - j))%nat) with ((S n - S (j - i))%nat) by omega.
      rewrite minus_INR.
        field.
        split...
      omega.
    field...
  Qed.

  Lemma Index_In_dec (i: Index ee ol) l: { In i l } + { ~ In i l }.
  Proof.
    intros. apply In_dec.
    unfold Index. intros.
    apply natBelow_eq_dec.
  Qed.

  Theorem qs_comp_prob: forall i j: Index ee ol, lt i j -> forall l b, IndexSeq b l ->
    monoid_expec (U.ijcount i j) (U.qs (e:=ee) (ol:=ol) l) <= 2 / INR (S (j - i)).
  Proof with auto with real.
    do 4 intro.
    cset (sound_cmp_expec_0 i j l).
    unfold U.qs in *.
    extro H0.
    pattern l, (qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      Focus 1.
      intros.
      apply Rle_trans with 0.
        compute...
      apply sigh.
    intros.
    clear l.
    destruct (Index_In_dec i v).
      Focus 2. rewrite H1... apply sigh.
    destruct (Index_In_dec j v).
      Focus 2. rewrite H1... apply sigh.
    clear H1.
    rename H2 into H1.
    rename i0 into H2.
    rename i1 into H3.
    destruct (IndexSeq_inv H1 i H2).
    destruct (IndexSeq_inv H1 j H3).
    rewrite vec.length in *.
    cset (@monoid_expec_Node_map U.monoid (U.ijcount i j) (natBelow (S n))).
    simpl in H8. rewrite H8. clear H8.
    unfold monoid_expec_sum.
    rewrite nats_below_S_length.
    rewrite <- arith_part with n b i j...
    unfold Rdiv.
    apply Rmult_le_compat_r...
    cset (monoid_expec_map_fst_monoid_mult (U.hom_ijcount i j)).
    simpl monoid_mult in H8.
    unfold monoid_expec in H8.
    apply (@vec_cases2 ee ol b i j (list (Index ee ol)) (U.ijcount i j ∘ fst) n v); intros; try rewrite H8...
            apply case_A with b...
            intros. apply H0 with b0... apply sound_cmp_expec_0...
          apply case_BD with b...
            intros. apply H0 with b0... apply sound_cmp_expec_0...
          left...
          unfold Index in *.
          apply natBelow_unique...
        apply case_C...
      apply case_BD with b...
        intros. apply H0 with b0... apply sound_cmp_expec_0...
      right...
      unfold Index in *.
      apply natBelow_unique...
    apply case_E with b...
    intros. apply H0 with b0... apply sound_cmp_expec_0.
  Qed.

End contents.
