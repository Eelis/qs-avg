
Set Implicit Arguments.

Require Import List.
Require Import Bool.
Require Import Util.

Hint Resolve in_map.

Hint Constructors NoDup.

Definition count (X: Set) (p: X -> bool): list X -> nat :=
  fix F (l: list X): nat :=
    match l with
    | nil => 0
    | h :: t => if p h then S (F t) else F t
    end.

Lemma count_app (X: Set) (p: X -> bool) (l l': list X): count p (l ++ l') = count p l + count p l'.
Proof with auto.
  induction l...
  simpl.
  destruct (p a)...
  intros.
  rewrite IHl...
Qed.

Lemma count_0 (X: Set) (p: X -> bool) (l: list X): (forall x, In x l -> p x = false) -> count p l = 0.
Proof with auto. induction l... simpl. intros. rewrite H... Qed.

Lemma count_le (X: Set) (p: X -> bool) (l: list X): count p l <= length l.
Proof with auto with arith.
  induction l...
  simpl.
  destruct (p a)...
Qed.

Hint Resolve count_le.

Lemma count_filter_le (X: Set) (f p: X -> bool) (x: list X): count f (filter p x) <= count f x.
Proof with auto with arith.
  induction x...
  simpl.
  destruct (p a).
    simpl.
    destruct (f a)...
  destruct (f a)...
Qed.

Lemma count_lt (X: Set) (p: X -> bool) (v: X) (l: list X):
  In v l -> p v = false -> count p l < length l.
Proof with auto with arith.
  induction l; simpl; intros.
    elimtype False...
  inversion_clear H.
    subst.
    rewrite H0...
  destruct (p a)...
Qed.

Lemma count_perm (A: Set) (l l': list A): Permutation l l' -> forall p, count p l' = count p l.
Proof with auto.
  intros A l l' p.
  induction p; intros; simpl...
      rewrite IHp...
    destruct (p y); destruct (p x)...
  rewrite IHp2...
Qed.

Lemma NoDup_map_inv' (A B: Set) (f: A -> B) (l: list A): NoDup (map f l) -> NoDup l.
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H.
  apply NoDup_cons...
Qed.

Lemma length_filter (X: Set) (p: X -> bool) (l: list X): length (filter p l) = count p l.
Proof with auto. induction l... simpl. destruct (p a)... simpl... Qed.

Lemma length_filter_le (T: Set) (p: T -> bool) (l: list T): length (filter p l) <= length l.
Proof. intros. rewrite length_filter. apply count_le. Qed.

Lemma filter_all (X: Set) (p: X -> bool) (l: list X):
  (forall x, In x l -> p x = true) -> filter p l = l.
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite H...
  rewrite IHl...
Qed.

Lemma In_filter (T: Set) (p: T -> bool) (t: T): p t = true -> forall l, In t l -> In t (filter p l).
Proof. intros. destruct (filter_In p t l). apply H2; auto. Qed.

Lemma incl_filter (X: Set) (p: X -> bool) (l: list X): incl (filter p l) l.
Proof with auto.
  unfold incl.
  induction l; simpl...
  intros.
  destruct (p a); firstorder.
Qed.

Lemma incl_trans (A: Set) (x y: list A): incl x y -> forall z, incl y z -> incl x z.
Proof. do 8 intro. apply H0. apply H. assumption. Qed.

Hint Resolve incl_filter.

Lemma filter_preserves_incl (X: Set) (p: X -> bool) (a b: list X): incl a b -> incl (filter p a) (filter p b).
Proof with auto.
  unfold incl.
  intros.
  destruct (filter_In p a0 a).
  clear H2.
  destruct (H1 H0).
  clear H1.
  apply In_filter...
Qed.

Hint Resolve filter_preserves_incl.

Lemma In_inv_perm (X: Set) (x: X) (l: list X):
  In x l -> exists l', Permutation (x :: l') l.
Proof with auto.
  induction l; intros; inversion_clear H.
    subst.
    exists l...
    apply Permutation_refl.
  destruct (IHl H0).
  exists (a :: x0).
  destruct l.
    elimtype False...
  apply perm_trans with (a :: x :: x0).
    apply perm_swap.
  apply perm_skip...
Qed.

Lemma In_map_inv (T U: Set) (f: T -> U) (l: list T) (y: U): In y (map f l) -> exists x, f x = y /\ In x l.
Proof. induction l; firstorder. Qed.

Implicit Arguments In_map_inv [T U f l y].

Lemma Permutation_NoDup: forall (X: Set) (a: list X),
  NoDup a -> forall b, Permutation a b -> NoDup b.
Proof with auto.
  intros.
  induction H0...
    inversion_clear H.
    apply NoDup_cons...
    intro.
    apply H1.
    apply Permutation_in with l'...
    apply Permutation_sym...
  inversion_clear H.
  inversion_clear H1.
  apply NoDup_cons; firstorder.
Qed.

Lemma Permutation_incl (X: Set) (a b: list X): Permutation a b -> incl a b.
Proof with auto.
  intros.
  induction H.
        do 2 intro.
        inversion H.
      do 2 intro.
      inversion_clear H0; [left | right]...
    do 2 intro.
    inversion_clear H.
      right. left...
    destruct H0; [left | right]...
    right...
  apply incl_tran with l'...
Qed.

Hint Resolve Permutation_refl.

Lemma filter_perm (X: Set) (a b: list X): Permutation a b -> forall p, Permutation (filter p a) (filter p b).
Proof with auto.
  intros X a b P.
  induction P.
        intros.
        simpl...
      intros.
      simpl.
      destruct (p x)...
      apply perm_skip...
    intros.
    simpl.
    destruct (p y)...
    destruct (p x)...
    apply perm_swap...
  intros.
  apply perm_trans with (filter p l')...
Qed.

Lemma complementary_filter_perm (A: Set) (p: A -> bool) (l: list A):
  Permutation l (filter p l ++ filter (negb ∘ p) l).
Proof with auto.
  induction l...
  simpl.
  unfold compose.
  destruct (p a); simpl.
    apply perm_skip...
  apply Permutation_cons_app...
Qed.

Lemma filter_none (X: Set) (p: X -> bool) (l: list X): (forall x, In x l -> p x = false) <-> filter p l = nil.
Proof with auto.
  induction l.
    split...
    intros.
    inversion H0.
  destruct IHl.
  split.
    intros.
    simpl.
    rewrite H1.
      apply H.
      firstorder.
    left...
  intros.
  simpl in H1.
  destruct H2.
    subst.
    destruct (p x)...
    discriminate.
  apply H0...
  destruct (p a)...
  discriminate.
Qed.

Lemma incl_map (X Y: Set) (f: X -> Y) (a b: list X): incl a b -> incl (map f a) (map f b).
Proof with auto.
  do 8 intro.
  destruct (In_map_inv H0).
  destruct H1.
  subst.
  apply in_map...
Qed.

Lemma incl_in (T: Set) (a b: list T): incl a b -> forall x, In x a -> In x b.
Proof. auto. Qed.

Lemma incl_In X (x: X) (l: list X): In x l -> forall l', incl l l' -> In x l'.
Proof. intros. apply H0. assumption. Qed. (* todo: move *)

Lemma NoDup_filter (T: Set) (p: T -> bool) (l: list T):
  NoDup l -> NoDup (filter p l).
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H.
  destruct (p a)...
  apply NoDup_cons...
  intro.
  apply H0...
  apply (incl_filter p l)...
Qed.

Lemma length_excl_counts (X: Set) (p: X -> bool) (l: list X):
  length l = count p l + count (negb ∘ p) l.
Proof with auto.
  unfold compose.
  induction l...
  intros.
  simpl.
  rewrite IHl.
  destruct (p a); simpl...
Qed.

Lemma count_filtered (X: Set) (p q: X -> bool):
  (forall x, q x = true -> p x = false) ->
  forall l, count p (filter q l) = 0.
Proof with auto.
  induction l...
  simpl.
  cset (H a).
  destruct (q a)...
  simpl.
  rewrite H0...
Qed.

Lemma app_nil_r T (l: list T): l ++ nil = l.
Proof with auto. induction l... simpl. rewrite IHl... Qed.

Hint Resolve Permutation_map.

Lemma map_cons (T U: Set) (f: T -> U) (h: T) (l: list T): map f (h :: l) = f h :: map f l.
Proof. auto. Qed.

(* concat *)

Definition concat T: list (list T) -> list T := fold_right (@app _) nil.

Lemma concat_app T (x y: list (list T)): concat (x ++ y) = concat x ++ concat y.
Proof with auto.
  induction x...
  simpl.
  intros.
  rewrite IHx.
  rewrite app_ass...
Qed.

Lemma In_concat (X: Type) (l: list (list X)) (s: list X) (x: X): In x s -> In s l -> In x (concat l).
Proof with auto.
  induction l...
  intros.
  simpl.
  apply in_or_app.
  inversion_clear H0.
    subst...
  right...
  apply IHl with s...
Qed.

Lemma In_concat_inv (X: Type) (x: X) (l: list (list X)):
  In x (concat l) -> exists s, In x s /\ In s l.
Proof with auto.
  induction l.
    intros.
    elimtype False...
  simpl.
  intros.
  destruct (in_app_or _ _ _ H).
    exists a.
    split...
  destruct (IHl H0).
  destruct H1.
  exists x0...
Qed.

Definition eq_count (X: Set) (d: forall (x y: X), { x = y } + { x <> y }) (x: X): list X -> nat :=
 count (fun y => unsum_bool (d x y)).

Lemma eq_count_0 (X: Set) (d: forall (x y: X), { x = y } + { x <> y }) (x: X) l:
  ~ In x l -> eq_count d x l = 0%nat.
Proof with auto.
  induction l...
  simpl.
  intros.
  destruct (d x a).
    elimtype False.
    apply H.
    left...
  simpl.
  apply IHl.
  intro.
  apply H.
  right...
Qed.

Lemma eq_count_NoDup (X: Set) (d: forall (x y: X), { x = y } + { x <> y }) (x: X) l:
  NoDup l -> eq_count d x l <= 1.
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H...
  destruct (d x a); simpl...
  subst.
  rewrite eq_count_0...
Qed.

Lemma NoDup_incl_Permutation (A: Set) (a b: list A):
  length a = length b -> NoDup a -> incl a b -> Permutation a b.
Proof with auto. (* todo: prove in terms of the vec equivalent *)
  induction a; intros.
    destruct b.
      apply perm_nil.
    discriminate.
  assert (In a b).
    apply H1.
    left...
  destruct (In_inv_perm a b H2).
  apply perm_trans with (a :: x)...
  apply perm_skip.
  apply IHa.
      cset (Permutation_length H3).
      rewrite <- H in H4.
      inversion_clear H4...
    inversion_clear H0...
  cut (incl a0 (a :: x)).
    intros.
    intro.
    intros.
    cset (H4 a1 H5).
    inversion_clear H6...
    subst.
    inversion_clear H0.
    elimtype False...
  apply incl_tran with b...
    intro.
    intros.
    apply H1.
    right...
  apply Permutation_incl.
  apply Permutation_sym...
Qed.

Lemma NoDup_map' (A B: Set) (f: A -> B) (l: list A):
  (forall x y: A, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup l -> NoDup (map f l).
Proof with auto.
  induction l; simpl...
  intros.
  inversion_clear H0.
  apply NoDup_cons...
  intro.
  destruct (In_map_inv H0).
  destruct H3.
  apply (H x a)...
  intro.
  subst...
Qed. (* todo: replace NoDup_map *)

Lemma NoDup_map (A B: Set) (f: A -> B) l:
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof with simpl; auto.
  induction l...
  intros.
  simpl.
  inversion_clear H0.
  apply NoDup_cons...
  intro.
  apply H1.
  destruct (In_map_inv H0).
  destruct H3.
  rewrite (H a x)...
Qed.

Inductive InP (X: Type) (P: X -> Prop): list X -> Prop :=
  | InP_head x t: P x -> InP P (x :: t)
  | InP_tail x t: InP P t -> InP P (x :: t).

Inductive NoDupL (A: Type): list (list A) -> Prop :=
  | NoDupL_nil: NoDupL nil
  | NoDupL_cons (l: list A) (ll: list (list A)): NoDup l ->
      (forall x, In x l -> ~ InP (In x) ll) -> NoDupL ll -> NoDupL (l :: ll).

Hint Constructors NoDupL.

Lemma InP_In (X: Type) (l: list X) (ll: list (list X)): In l ll -> forall x, In x l -> InP (In x) ll.
Proof with auto.
  induction ll.
    intros.
    inversion H.
  intros.
  inversion_clear H; [left | right]...
  subst...
Qed.

Lemma InP_In_inv (X: Type) (x: X) (ll: list (list X)):
  InP (In x) ll -> exists l, In x l /\ In l ll.
Proof with auto.
  intros X x ll H.
  induction H.
    exists x0.
    split...
    left...
  destruct IHInP.
  destruct H0.
  exists x1.
  split...
  right...
Qed.

Implicit Arguments InP_In_inv [X x ll].

Lemma NoDup_concat (A: Type) (l: list (list A)): NoDupL l -> NoDup (concat l).
Proof with auto.
  induction l; simpl; intros.
    apply NoDup_nil.
  inversion_clear H.
  induction a...
  inversion_clear H0.
  simpl.
  apply NoDup_cons...
    intro.
    destruct (in_app_or _ _ _ H0)...
    apply (H1 a).
      left...
    destruct (In_concat_inv _ _ H4).
    destruct H5.
    apply InP_In with x...
  apply IHa...
  intros.
  apply H1.
  right...
Qed.

Lemma In_filter_inv (A: Type) (f: A -> bool) (x: A) (l: list A): In x (filter f l) -> In x l /\ f x = true.
Proof. intros. destruct (filter_In f x l). apply H0. assumption. Qed.

(* Partitioning *)

Section Partitioning.

  Variable T: Set.

  Definition Partitioning: Set := comparison -> list T.

  Lemma partition_oblig c l h
    (H: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l}):
    Permutation
      ((if cmp_cmp c Eq then h :: proj1_sig H Eq else proj1_sig H Eq) ++
      (if cmp_cmp c Lt then h :: proj1_sig H Lt else proj1_sig H Lt) ++
      (if cmp_cmp c Gt then h :: proj1_sig H Gt else proj1_sig H Gt))
      (h :: l).
  Proof with auto.
    intros.
    destruct H. simpl.
    apply Permutation_sym.
    cset (Permutation_sym p).
    destruct c; simpl.
        apply perm_skip...
      apply Permutation_cons_app...
    rewrite <- app_ass in *.
    apply Permutation_cons_app...
  Qed.

  Definition addToPartitioning (c: comparison) (l: list T) (h: T) (H: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l}): {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) (h :: l)} :=
    exist (fun p => Permutation (p Eq ++ p Lt ++ p Gt) (h :: l))
      (fun c' => if cmp_cmp c c' then h :: proj1_sig H c' else proj1_sig H c')
      (partition_oblig c h H).

  Definition emp: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) nil} :=
    exist (fun p => Permutation (p Eq ++ p Lt ++ p Gt) nil) (fun _ => nil) (perm_nil T).

End Partitioning.
