Set Implicit Arguments.

Require Import List.
Require Import Lt.
Require Import Le.
Require Import util.
Require Import list_utils.
Require Import Omega.
Require Import arith_lems.

Fixpoint nats (b: nat) (w: nat) {struct w}: list nat :=
  match w with
  | 0 => nil
  | S w' => b :: nats (S b) w'
  end.

Lemma nats_length (w b: nat): length (nats b w) = w.
Proof with auto.
  induction w...
  simpl.
  intros.
  rewrite IHw...
Qed.

Lemma In_nats (w x b: nat): b <= x -> x < b + w -> In x (nats b w).
Proof with auto.
  induction w; intros.
    elimtype False.
    rewrite plus_0_r in H0.
    apply (lt_not_le x b H0)...
  simpl.
  destruct (le_lt_eq_dec _ _ H); [right | left]...
  apply IHw...
  omega.
Qed.

Lemma In_nats_inv (w x b: nat): In x (nats b w) -> b <= x < b + w.
Proof with auto.
  induction w; simpl; intros.
    inversion H.
  inversion H.
    omega.
  destruct (IHw x (S b) H0).
  omega.
Qed.

Lemma NoDup_nats (w b: nat): NoDup (nats b w).
Proof with auto.
  induction w; simpl; intros.
    apply NoDup_nil.
  apply NoDup_cons...
  intro.
  destruct (In_nats_inv _ _ _ H).
  apply (le_Sn_n _ H0).
Qed.

Lemma nats_plus y x z: nats x (y + z) = nats x y ++ nats (y + x) z.
Proof with auto.
  induction y...
  intros.
  simpl.
  rewrite IHy.
  rewrite <- plus_n_Sm...
Qed.

Lemma nats_Sw b w: nats b (S w) = b :: nats (S b) w.
Proof. auto. Qed.

Lemma nats_split (w b i: nat): i <= w -> nats b w = nats b i ++ nats (b + i) (w - i).
Proof with auto.
  intros.
  destruct (le_exists_plus H).
  subst w.
  replace (i + x - i) with x by omega.
  rewrite nats_plus.
  rewrite plus_comm.
  reflexivity.
Qed.

Lemma nats_Sw' w b: nats b (S w) = nats b w ++ (w + b :: nil).
Proof with auto.
  induction w...
  intros.
  rewrite nats_Sw.
  rewrite IHw.
  simpl.
  rewrite plus_n_Sm...
Qed.

Lemma split_pow2_range n:
  nats 1 (pow 2 n) = 1 :: concat (map (fun x => nats (pow 2 x + 1) (pow 2 x)) (nats 0 n)).
Proof with auto.
  induction n...
  simpl pow.
  rewrite plus_0_r.
  rewrite nats_plus.
  rewrite IHn.
  rewrite nats_Sw'.
  rewrite map_app.
  simpl.
  rewrite concat_app.
  rewrite plus_0_r.
  simpl.
  rewrite app_nil_r...
Qed.
