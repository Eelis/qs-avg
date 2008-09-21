
Set Implicit Arguments.

Require Import List.
Require Import Lt.
Require Import Le.
Require Import Util.
Require Import ListUtils.
Require Import Omega.
Require ne_list.
Require Import ArithLems.
Require Import Bvector.
Require Import SkipList.
Require vec.
Require Import NatBelow.

Definition map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): C * B := (fst p, f (snd p)).

Lemma fst_map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): fst (map_snd f p) = fst p.
Proof. destruct p. auto. Qed.

Lemma nth_in (T: Set) (l: list T) (i: natBelow (length l)): In (vec.nth l i) l. (* todo: rename *)
Proof.
  unfold vec.nth.
  intros.
  cset (vec.In_nth i (vec.from_list l)).
  rewrite vec.list_round_trip in H.
  assumption.
Qed.
  
Hint Resolve nth_in.

(* nats_below *)

Definition nats_below_from (x y: nat): list (natBelow (x + y)) := vec.nats x y.

Definition nats_below: forall n, list (natBelow n) := nats_below_from 0.

Fixpoint vec_to_ne_list (A: Set) n: vector A (S n) -> ne_list.L A :=
  match n return vector A (S n) -> ne_list.L A with
  | 0 => fun v => ne_list.one (vec.head v)
  | _ => fun v => ne_list.cons (vec.head v) (vec_to_ne_list (vec.tail v))
  end.

Definition nats_below_S (n: nat): ne_list.L (natBelow (S n)) := vec_to_ne_list (vec.nats 0 (S n)).

Lemma vec_to_ne_list_to_plain (A: Set) n (v: vector A (S n)): ne_list.to_plain (vec_to_ne_list v) = vec.to_list v.
Proof with reflexivity.
  induction n; intros.
    rewrite (vec.eq_cons v).
    simpl.
    rewrite (vec.eq_nil (vec.tail v))...
  rewrite (vec.eq_cons v).
  simpl.
  rewrite IHn...
Qed.

Lemma nats_below_S_length n: length (nats_below_S n) = S n.
Proof with auto.
  intros.
  unfold nats_below_S.
  rewrite vec_to_ne_list_to_plain.
  apply vec.length.
Qed.

(* nats *)

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

(* natsBelow *)

Definition natsBelow: nat -> list nat := nats 0.

Lemma In_natsBelow m n: lt n m -> List.In n (natsBelow m).
Proof. unfold natsBelow. intros. apply In_nats; auto with arith. Qed.

Lemma In_natsBelow_inv m n: List.In n (natsBelow m) -> lt n m.
Proof. unfold natsBelow. intros. destruct (In_nats_inv _ _ _ H); auto. Qed.
