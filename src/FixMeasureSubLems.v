(* Intended for use without Import. *)

Set Implicit Arguments.

Require Import Util.
Require Import Le.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Import Measured.
Require (*Import *) Coq.Program.Wf.
(*Require Import Wf_nat.*)
(*Require Import FixSub.*)
Require Import List.

(*  Program Fixpoint qs (l: list nat) {measure length l}: list nat :=
    match l with
    | _ => nil
    end.
Print qs.*)

Section rect.

  Variable A: Set.
  Variable m: A -> nat.
  Variable P: A -> Type.
  Variable f: forall x: A, (forall y: { y: A | m y < m x }, P (proj1_sig y)) -> P x.

  Lemma F_unfold x r:
    Wf.Fix_measure_F_sub A m P f x r =
    f (fun y => Wf.Fix_measure_F_sub A m P f (proj1_sig y) (Acc_inv r (proj2_sig y))).
  Proof. intros. case r; auto. Qed.

  Lemma recti
    (Q: forall x, P x -> Type)
    (inv: forall x: A, (forall y: A, MR lt m y x -> forall a: Acc lt (m y), Q y (Wf.Fix_measure_F_sub A m P f y a)) -> forall a: Acc lt (m x), Q x (f (fun y: {y: A | m y < m x} => Wf.Fix_measure_F_sub A m P f (proj1_sig y) (Acc_inv a (proj2_sig y))))):
      forall x a, Q _ (Wf.Fix_measure_F_sub A m P f x a).
  Proof with auto.
    intros Q inv.
    set (R := fun (x: A) => forall a, Q _ (Wf.Fix_measure_F_sub A m P f x a)).
    cut (forall x, R x)...
    apply (well_founded_induction_type (measure_wf lt_wf m)).
    subst R.
    simpl.
    intros.
    rewrite F_unfold...
  Qed.

  Hypothesis byt: forall x0 (g h: forall x: {y: A | m y < m x0}, P (proj1_sig x)),
    (forall x p p', g (exist (fun y: A => m y < m x0) x p) = h (exist _ x p')) -> f g = f h.

  Lemma eq_Fix_measure_F_sub x a a':
    Wf.Fix_measure_F_sub A m P f x a =
    Wf.Fix_measure_F_sub A m P f x a'.
  Proof.
    intros x a.
    pattern x, (Wf.Fix_measure_F_sub A m P f x a).
    apply recti.
    intros.
    rewrite F_unfold.
    apply byt.
    intros.
    apply H.
    assumption.
  Qed.

  Lemma recti2
    (Q: forall x, P x -> Type)
    (inv: forall x: A, (forall y: A, MR lt m y x -> Q y (Wf.Fix_measure_sub A m P f y)) -> forall a: Acc lt (m x), Q x (f (fun y: {y: A | m y < m x} => Wf.Fix_measure_sub A m P f (proj1_sig y)))):
      forall x, Q _ (Wf.Fix_measure_sub A m P f x).
  Proof with auto.
    unfold Wf.Fix_measure_sub.
    intros.
    apply recti.
    intros.
    assert (forall y: A, MR lt m y x0 -> Q y (Wf.Fix_measure_F_sub A m P f y (lt_wf (m y))))...
    cset (inv x0 X0 a).
    rewrite <- (byt (fun y: {y: A | m y < m x0} => Wf.Fix_measure_F_sub A m P f (proj1_sig y) (lt_wf (m (proj1_sig y)))) (fun y: {y: A | m y < m x0} => Wf.Fix_measure_F_sub A m P f (proj1_sig y) (Acc_inv a (proj2_sig y))))...
    intros.
    apply eq_Fix_measure_F_sub.
  Qed.

End rect.
