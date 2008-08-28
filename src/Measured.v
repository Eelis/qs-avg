Set Implicit Arguments.

Section measure_wf.

  (* Measure relations are well-founded if the underlying relation is well-founded. *)

  Variables T M: Set.
  Variable R: M -> M -> Prop.
  Hypothesis wf: well_founded R.
  Variable m: T -> M.

  Definition MR (x y: T): Prop := R (m x) (m y).

  Lemma measure_wf: well_founded MR.
  Proof with auto.
    unfold well_founded.
    cut (forall a: M, (fun mm: M => forall a0: T, m a0 = mm -> Acc MR a0) a).
      intros.
      apply (H (m a))...
    apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc MR a)).
    intros.
    apply Acc_intro.
    intros.
    unfold MR in H1.
    rewrite H0 in H1.
    apply (H (m y))...
  Defined.

End measure_wf.

Section wf_ind_prop.

  (* Lemma for proving things about functions defined with well_founded_induction. *)

  Variable A: Set.
  Variable R: A -> A -> Prop.
  Hypothesis wf_R: well_founded R.
  Variable U: A -> Set.
  Hypothesis f: (forall x: A, (forall y: A, R y x -> U y) -> U x).

  Variable P: forall (t: A), U t -> Prop.

  Hypothesis f_invariant: forall (x: A) (priors: forall y, R y x -> U y),
    (forall y (e: R y x), P (priors y e)) -> P (f priors).

  Fixpoint mja (a: A) (H: Acc R a) {struct H}: P (Acc_iter U f H) :=
    match H return P (Acc_iter U f H) with
    | Acc_intro x => f_invariant (fun y (h: R y a) => Acc_iter U f (x y h)) (fun q e => mja (x q e))
    end. (* todo: rename *)

  Lemma wf_ind_ind a: P (well_founded_induction wf_R U f a).
  Proof with auto.
    unfold well_founded_induction.
    unfold well_founded_induction_type.
    intro.
    apply mja.
  Defined.

End wf_ind_prop.
