
Set Implicit Arguments.

Require Import Util.
Require Import List.
Require Import Plus.
Require Import Arith.
Require Import ArithLems.
Require Import nats_below.
Require Import ListUtils.

(* sum *)

Fixpoint sum (l: list nat): nat :=
  match l with
  | nil => 0
  | h :: t => h + sum t
  end.

Lemma sum_once h t: sum (h :: t) = h + sum t.
Proof. auto. Qed.

Lemma sum_app x y: sum (x ++ y) = sum x + sum y.
Proof with auto.
  induction x...
  simpl.
  intros.
  rewrite IHx.
  rewrite plus_assoc...
Qed.

Require Import Rbase.
Require Import Rdefinitions.
Require Import Fourier.

Open Scope R_scope.

(* Rsum *)

Definition Rsum: list R -> R := fold_right Rplus 0.

Lemma Rsum_sum_map (T: Set) (fi: T -> nat) (fr: T -> R) (l: list T):
  (forall x, In x l -> fr x = INR (fi x)) -> Rsum (map fr l) = INR (sum (map fi l)).
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite plus_INR.
  rewrite H...
  rewrite IHl...
Qed.

Lemma Rsum_Permutation (x y: list R): Permutation x y -> Rsum x = Rsum y.
Proof with auto.
  intros x y p.
  induction p...
      simpl.
      rewrite IHp...
    simpl.
    do 2 rewrite <- Rplus_assoc.
    rewrite (Rplus_comm y)...
  rewrite IHp1...
Qed.

Lemma Rsum_app (x y: list R): Rsum (x ++ y) = Rsum x + Rsum y.
Proof with auto with real.
  induction x...
  simpl.
  intros.
  rewrite IHx...
Qed.

Lemma Rsum_constant r l: (forall x, In x l -> x = r) -> Rsum l = INR (length l) * r.
Proof with auto.
  induction l; intros.
    simpl.
    field.
  simpl Rsum.
  simpl length.
  rewrite IHl.
    rewrite (H a).
      rewrite S_INR.
      field.
    left...
  intros.
  apply H.
  right...
Qed.

Lemma Rsum_le l r: (forall x, In x l -> x <= r) -> Rsum l <= INR (length l) * r.
Proof with auto with real.
  induction l...
  simpl length.
  intros.
  simpl Rsum.
  apply Rle_trans with (a + INR (length l) * r).
    apply Rplus_le_compat_l.
    apply IHl.
    intros.
    apply H.
    right...
  apply Rle_trans with (r + INR (length l) * r).
    apply Rplus_le_compat_r.
    firstorder.
  simpl length.
  rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l...
Qed.

Lemma le_Rsum l r: (forall x, In x l -> r <= x) -> INR (length l) * r <= Rsum l.
Proof with auto with real.
  induction l; intros.
    simpl.
    rewrite Rmult_0_l...
  simpl length.
  simpl Rsum.
  rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  rewrite Rplus_comm.
  apply Rplus_le_compat.
    apply H.
    left...
  apply IHl.
  intros.
  apply H.
  right...
Qed.

(* RsumOver *)

Definition RsumOver (X: Set) (l: list X) (f: X -> R): R := Rsum (map f l).

Lemma RsumOver_nats_le x y z: (y <= z)%nat -> forall f, (forall q, (x <= q)%nat -> 0 <= f q) ->
  RsumOver (nats x y) f <= RsumOver (nats x z) f.
Proof with auto.
  intros.
  destruct (le_exists_plus H).
  subst.
  unfold RsumOver.
  rewrite nats_plus.
  rewrite map_app.
  rewrite Rsum_app.
  assert (0 <= Rsum (map f (nats (y + x) x0))).
    replace 0 with (INR (length (map f (nats (y + x) x0))) * 0)...
      apply le_Rsum.
      intros.
      destruct (In_map_inv H1).
      destruct H2.
      subst...
      destruct (In_nats_inv _ _ _ H3).
      apply H0.
      omega.
    rewrite Rmult_0_r...
  fourier.
Qed.

Lemma RsumOver_cons (X: Set) (x: X) (l: list X) (f: X -> R): RsumOver (x :: l) f = f x + RsumOver l f.
Proof. auto. Qed.

Lemma RsumOver_concat_map (X Y: Set) (f: X -> R) (g: Y -> list X) (l: list Y):
  RsumOver (concat (map g l)) f = RsumOver l (fun x => RsumOver (g x) f).
Proof with auto.
  unfold RsumOver.
  induction l...
  simpl.
  rewrite map_app.
  rewrite Rsum_app.
  rewrite IHl...
Qed.

Lemma RsumOver_constant_le (X: Set) (l: list X) (f: X -> R) (c: R):
  (forall x, List.In x l -> f x <= c) -> RsumOver l f <= INR (length l) * c.
Proof with auto.
  unfold RsumOver.
  intros.
  rewrite <- (map_length f l).
  apply Rsum_le...
  intros.
  destruct (In_map_inv H0).
  destruct H1.
  subst...
Qed.

Lemma nats_Sb w b: nats (S b) w = map S (nats b w).
Proof with auto.
  induction w...
  simpl.
  intros.
  rewrite IHw...
Qed.

Lemma nats_plusb b b' w: nats (b + b') w = map (plus b) (nats b' w).
Proof with auto.
  induction b; simpl; intros.
    induction (nats b' w)...
    simpl.
    rewrite <- IHl...
  rewrite nats_Sb.
  rewrite IHb.
  rewrite map_map...
Qed.

Lemma RsumOver_nats_natsBelow b w f:
  RsumOver (nats b w) f =
  RsumOver (natsBelow w) (f ∘ plus b).
Proof with auto.
  intros.
  replace b with ((b + 0)%nat)...
  rewrite nats_plusb.
  unfold RsumOver.
  rewrite map_map...
  f_equal.
  unfold compose.
  apply map_ext...
Qed.

Lemma RsumOver_le (X: Set) (f g: X -> R) (l: list X):
  (forall x, In x l -> f x <= g x) -> RsumOver l f <= RsumOver l g.
Proof with auto with real.
  unfold RsumOver.
  intros.
  induction l...
  simpl.
  apply Rplus_le_compat.
    apply H.
    left...
  apply IHl.
  intros.
  apply H.
  right...
Qed.

Lemma RsumOver_mult_constant (X: Set) (f: X -> R) c (l: list X):
  c * RsumOver l f = RsumOver l (Rmult c ∘ f).
Proof with auto.
  unfold compose.
  unfold RsumOver.
  induction l.
    simpl.
    apply Rmult_0_r.
  simpl.
  rewrite <- IHl.
  apply Rmult_plus_distr_l.
Qed.

Lemma RsumOver_minus w f b d: (b + w <= d)%nat ->
  RsumOver (nats b w) (f ∘ minus d) = RsumOver (nats (S (d - (w + b))) w) f.
Proof with auto with arith.
  unfold compose.
  unfold RsumOver...
  intros.
  apply Rsum_Permutation.
  rewrite <- (map_map (minus d) f).
  apply Permutation_map.
  apply NoDup_incl_Permutation.
      rewrite map_length.
      repeat rewrite nats_length...
    apply NoDup_map.
      intros.
      apply minus_eq_inv_r with d...
        destruct (In_nats_inv _ _ _ H0)...
        apply le_trans with ((b + w)%nat)...
      destruct (In_nats_inv _ _ _ H1).
      apply le_trans with ((b + w)%nat)...
    apply NoDup_nats.
  intro.
  intro.
  destruct (In_map_inv H0).
  destruct H1.
  destruct (In_nats_inv _ _ _ H2).
  subst.
  apply In_nats; omega.
Qed.

(* Ravg *)

Definition Ravg (l: list R): R := Rsum l / INR (length l).

Lemma Ravg_nil: Ravg nil = 0.
Proof with auto.
  unfold Ravg.
  simpl.
  unfold Rdiv.
  rewrite Rmult_0_l...
Qed.

Lemma Ravg_one h: Ravg (h :: nil) = h.
Proof. intros. unfold Ravg. simpl. field. Qed.

Lemma Ravg_cons h t: Ravg (h :: t) = (h + Ravg t * INR (length t)) / INR (S (length t)).
Proof with auto with real.
  destruct t.
    simpl.
    unfold Ravg.
    simpl.
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Rmult_0_l...
  unfold Ravg.
  simpl Rsum.
  simpl length.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l...
Qed.

Lemma Ravg_Permutation x y: Permutation x y -> Ravg x = Ravg y.
Proof.
  intros.
  unfold Ravg.
  rewrite (Rsum_Permutation H).
  rewrite (Permutation_length H); auto.
Qed.

Lemma Ravg_0_le l: (forall x, In x l -> 0 <= x) -> 0 <= Ravg l.
Proof with auto with real.
  induction l.
    simpl.
    rewrite Ravg_nil...
  intros.
  rewrite Ravg_cons.
  unfold Rdiv.
  apply Rmult_le_pos...
  apply Rplus_le_le_0_compat.
    firstorder.
  apply Rmult_le_pos...
  firstorder.
Qed.

Lemma Ravg_0 (l: list R): (forall x, In x l -> x = 0) -> Ravg l = 0.
Proof with auto.
  induction l.
    rewrite Ravg_nil...
  intros.
  rewrite Ravg_cons.
  rewrite IHl.
    rewrite Rmult_0_l.
    rewrite (H a).
      rewrite Rplus_0_l.
      unfold Rdiv.
      rewrite Rmult_0_l...
    left...
  intros.
  apply H.
  right...
Qed.

(* Ravg_0 and Ravg_0_le cannot be generalized to arbitrary constant resp. lower bound, because Ravg nil = 0 *)

Lemma Ravg_app x y:
  Ravg (x ++ y) = / INR (length x + length y) * (Ravg x * INR (length x) + Ravg y * INR (length y)).
Proof with auto with real.
  induction x; intros.
    simpl.
    rewrite Ravg_nil.
    rewrite Rmult_0_l.
    rewrite Rplus_0_l.
    rewrite Rmult_comm.
    rewrite Rmult_assoc.
    destruct y.
      rewrite Ravg_nil.
      rewrite Rmult_0_l...
    rewrite Rinv_r...
    simpl length...
  simpl length.
  simpl app.
  do 2 rewrite Ravg_cons.
  rewrite IHx.
  rewrite app_length.
  unfold Rdiv.
  rewrite (Rmult_assoc (a + Ravg x * INR (length x)) ).
  rewrite (Rmult_comm (/ INR (S (length x)))).
  rewrite Rinv_r...
  rewrite Rmult_1_r.
  simpl plus.
  rewrite Rmult_comm.
  apply Rmult_eq_compat_l.
  rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  case_eq ((length x + length y)%nat); intros.
    destruct x.
      destruct y.
        simpl.
        repeat rewrite Rmult_0_r...
      elimtype False.
      simpl in H.
      discriminate.
    elimtype False.
    simpl in H.
    discriminate.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r...
Qed.

Lemma Ravg_0_inv (l: list R): Ravg l = 0 -> (forall x, In x l -> 0 <= x) -> forall x, In x l -> x = 0.
Proof with auto with real.
  induction l.
    intros.
    inversion H1.
  simpl.
  rewrite Ravg_cons.
  unfold Rdiv.
  intros.
  destruct (Rmult_0_inv H).
    Focus 2.
    elimtype False.
    apply (Rinv_neq_0_compat (INR (S (length l))))...
  assert (0 <= a).
    apply H0...
  assert (0 <= Ravg l).
    apply Ravg_0_le...
  assert (0 <= Ravg l * INR (length l)).
    apply Rmult_le_pos...
  destruct H1.
    subst.
    apply (Rplus_eq_0_l x (Ravg l * INR (length l)) H3 H5 H2).
  apply IHl...
  rewrite Rplus_comm in H2.
  cset (Rplus_eq_0_l (Ravg l * INR (length l)) a H5 H3 H2).
  destruct (Rmult_0_inv H6)...
  destruct l.
    inversion H1.
  simpl length in H7.
  elimtype False.
  apply (INR_S_ne_0 (length l))...
Qed.

Require ne_tree.

Definition TRavg: ne_tree.T R -> R := ne_tree.fold (@id R) Ravg.
