
Set Implicit Arguments.

Require Import List.
Require Import ListUtils.
Require Import Util.

Record Monad: Type :=
  { mon:> Set -> Set
  ; bind: forall a b, mon a -> (a -> mon b) -> mon b
  ; ret: forall (a: Set), a -> mon a
  (* Laws: *)
  ; mon_lunit: forall (a b: Set) (x: a) (f: a -> mon b), bind _ _ (ret _ x) f = f x
      (* (return x >>= f) = (f x) *)
  ; mon_runit: forall (a: Set) (f: mon a), bind a a f (ret a) = f
      (* (f >>= return) = f *)
  ; mon_assoc: forall a b c (n: mon a) (f: a -> mon b) (g: b -> mon c),
      bind _ _ (bind _ _ n f) g =
      bind _ _ n (fun x => bind _ _ (f x) g)
      (* ((n >>= f) >>= g) = n >>= (\x -> f x >>= g) *)
  }.

  (* Todo: I vaguely recall someone mentioning that there was a way to use notation and/or implicit arguments inside a record definition. That would make the above a lot cleaner. *)

Implicit Arguments bind [m a b].
Implicit Arguments ret [[m] [a]].

Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).

Record Functor: Type :=
  { func: Set -> Set
  ; func_map: forall (a b: Set) (f: a -> b), func a -> func b
  (* Laws: *)
  ; func_id: forall (X: Set), func_map _ _ (fun (x: X) => x) = (fun (x: func X) => x)
        (* (id .) = id *)
  ; func_assoc: forall (a b c: Set) (x: func a) (f: b -> c) (g: a -> b),
      func_map _ _ (f ∘ g) x = func_map _ _ f (func_map _ _ g x)
        (* (f . g) . x = f . (g . x) *)
  }.

Implicit Arguments func_map [f a b].

Definition extMonad (M: Monad): Prop := forall (A B: Set) (f g: A -> M B), ext_eq f g -> forall x, bind x f = bind x g.

Lemma bind_eqq (M: Monad) (e: extMonad M) (A B: Set) (m n: M A) (f g: A -> M B):
  m = n -> ext_eq f g -> (m >>= f) = (n >>= g).
Proof. intros. subst. apply e. assumption. Qed.

Definition extFlipped (M: Monad): extMonad M -> forall A (x: M A) (B: Set) (f g: A -> M B), ext_eq f g -> bind x f = bind x g.
Proof. auto. Defined.

Lemma mon_lunit_under_bind (M: Monad) (A B C: Set) (a: M A) (b: A -> B) (f: A -> B -> M C):
  extMonad M -> (x <- a ; (ret (b x) >>= f x)) = (x <- a ; f x (b x)).
Proof with auto.
  intros.
  apply H.
  intro.
  apply mon_lunit.
Qed.

Section MonadFunctor. (* Every Monad is a Functor. *)

  Variable M: Monad.

  Definition bind_map (a b: Set) (f: a -> b) (x: M a): M b :=
    xv <- x ;
    ret (f xv).

  Hypothesis f_ext_eq: forall A B (f g: A -> B), (forall x, f x = g x) -> f = g.

  Lemma eta A B (f: A -> B): (fun x => f x) = f.
    intros.
    apply f_ext_eq.
    auto.
  Qed.

  Definition MonadFunctor: Functor.
  Proof with auto.
    apply (Build_Functor M bind_map).
      intros.
      apply f_ext_eq.
      intro.
      unfold bind_map.
      rewrite (eta (@ret M X)).
      apply mon_runit.
    intros.
    unfold bind_map.
    unfold compose.
    rewrite mon_assoc.
    replace (fun xv: a => ret (m:=M) (f (g xv))) with (fun x0: a =>
         bind (m:=M) (b:=c) (ret (m:=M) (g x0))
           (fun xv: b => ret (m:=M) (f xv)))...
    apply f_ext_eq.
    intros.
    rewrite mon_lunit...
  Defined.

  Definition a_monad_isa_functor T (x: M T): func MonadFunctor T := x.
    (* can't make this a coercion:
          User error: a_monad_isa_functor does not respect the inheritance uniform condition *)

End MonadFunctor.

Module IdMonad.

  Definition C (s: Set): Set := s. (* type ctor *)

  Definition bind A B (x: C A) (y: A -> C B): C B := y x.
  Definition ret (A: Set) (x: A): C A := x.

  Definition M: Monad.
  Proof. apply (Build_Monad C bind ret); auto. Defined.

  Coercion id_isa_monad A (a: C A): M A := a.
(*  Coercion id_isa_functor A (a: C A): func (MonadFunctor M) A := a.*)

  Lemma ext: extMonad M.
  Proof. compute. auto. Qed.

End IdMonad.

Unset Elimination Schemes.

Inductive Tree (A: Set): Set :=
  | Leaf: A -> Tree A
  | Node: list (Tree A) -> Tree A.

Set Elimination Schemes.

Definition Tree_ind
  : forall (A: Set) (P : Tree A -> Prop),
    (forall n : A, P (Leaf n)) ->
    (forall l : list (Tree A), (forall t, In t l -> P t) -> P (Node l)) ->
  forall t, P t.
Proof with auto.
  intros A P Hbase Hrcd.
  refine (fix IH (t:Tree A) {struct t} : P t := _).
  case t; intros.
    apply Hbase.
  apply Hrcd.
  induction l.
    simpl.
    intros.
    contradiction.
  simpl.
  intros.
  destruct H.
    subst t0.
    apply IH.
  apply IHl.
  assumption.
Qed.

Require ne_list.
Require ne_tree.

Module NeTreeMonad.

  Definition C := ne_tree.T.

  (*Definition ret: forall {A: Set}, A -> C A := ne_tree.Leaf.*)
  Definition ret {A: Set}: A -> C A := @ne_tree.Leaf A.

  Fixpoint bind (A B: Set) (m: C A) (k: A -> C B): C B :=
    match m with
    | ne_tree.Leaf a => k a
    | ne_tree.Node ts => ne_tree.Node (ne_list.map (fun x => bind x k) ts)
    end.

  Let runit (a b: Set) (x: a) (f: a -> C b): bind (ret x) f = f x.
  Proof. auto. Qed.

  Fixpoint lunit A (f: C A) {struct f}: bind f ret = f :=
    match f return bind f ret = f with
    | ne_tree.Leaf x => (refl_equal _)
    | ne_tree.Node l =>
      eq_ind_r (fun l0 => ne_tree.Node l0 = ne_tree.Node l) (refl_equal _)
        ((fix F (l: ne_list.L (C A)) :=
          match l return ne_list.map (fun u => bind u ret) l = l with
          | ne_list.one x => eq_ind_r (fun c => ne_list.one c = ne_list.one x) (refl_equal _) (lunit x)
          | ne_list.cons x y => eq_ind_r (fun c => ne_list.cons c (ne_list.map (fun x => bind x ret) y) = ne_list.cons x y) (eq_ind_r (fun l => ne_list.cons x l = ne_list.cons x y) (refl_equal _) (F y)) (lunit x)
          end) l)
    end.

  Let assoc (a b c: Set) (n: C a) (f: a -> C b) (g: b -> C c):
    bind (bind n f) g = bind n (fun x: a => bind (f x) g).
  Proof with auto.
    intros.
    generalize n. clear n.
    apply (ne_tree.alt_rect2 (fun n => bind (bind n f) g = bind n (fun x: a => bind (f x) g)) (fun l => ne_list.map (fun x => bind (bind x f) g) l = ne_list.map (fun x => bind x (fun x0 => bind (f x0) g)) l)); intros; simpl...
        rewrite ne_list.map_map.
        unfold compose.
        rewrite H...
      rewrite H...
    rewrite H.
    rewrite H0...
  Qed.

  Definition M: Monad := Build_Monad C bind (@ret) runit lunit assoc.

  Lemma ext: extMonad M.
  Proof with auto.
    unfold extMonad.
    induction x using ne_tree.alt_ind; simpl...
    replace (ne_list.map (fun x: C A => bind x f) l) with (ne_list.map (fun x: C A => bind x g) l)...
    generalize H0. clear H0.
    induction l; simpl; intros; rewrite H0...
    rewrite IHl...
  Qed.

  Lemma bind_Leaf (A B: Set) (x: A) (f: A -> M B): bind (ne_tree.Leaf x) f = f x.
  Proof. auto. Qed.

  Lemma bind_Node (A B: Set) (x: ne_list.L (ne_tree.T A)) (f: A -> M B):
    bind (ne_tree.Node x) f = ne_tree.Node (ne_list.map (fun x0: C A => bind x0 f) x).
  Proof. auto. Qed.

  Lemma bind_Node_one (X Y: Set) (t: M X) (g: X -> M Y):
    bind (ne_tree.Node (ne_list.one t)) g = ne_tree.Node (ne_list.one (t >>= g)).
  Proof. auto. Qed.

  Lemma bind_Node_cons (X Y: Set) (t: M X) (l: ne_list.L (M X)) (g: X -> M Y):
    bind (ne_tree.Node (ne_list.cons t l)) g = ne_tree.Node (ne_list.cons (bind t g) (ne_list.map (fun x => bind x g) l)).
  Proof. auto. Qed.

  Lemma bind_map (X Y: Set) (f: X -> Y) (x: M X): bind x (ret ∘ f) = ne_tree.map f x.
  Proof with try reflexivity.
    induction x...
      simpl.
      rewrite IHx...
    simpl.
    rewrite IHx.
    f_equal.
    simpl in IHx0.
    inversion_clear IHx0...
  Qed.

  Definition deterministic (X: Set) (x: M X) (v: X): Prop := x = ne_tree.Leaf v.

  Lemma deterministic_ret (A: Set) (a: A): deterministic (ret a) a.
  Proof. unfold deterministic. auto. Qed.

  Lemma ex_deterministic_ret (X: Set) (x: X): exists u, deterministic (ret x) u.
  Proof. intros. exists x. apply deterministic_ret. Qed.

  Lemma deterministic_bind:
    forall (A: Set) (a: M A) (z: A), deterministic a z ->
    forall (B: Set) (b: A -> M B) (v: B), deterministic (b z) v ->
      exists w, deterministic (a >>= b) w.
  Proof with auto. unfold deterministic. intros. subst. simpl. exists v... Qed.

  Lemma deterministic_bind_weak:
    forall (A: Set) (a: M A) (z: A), deterministic a z ->
    forall (B: Set) (b: A -> M B), (forall q, exists v, deterministic (b q) v) ->
    exists w, deterministic (a >>= b) w.
  Proof with auto. intros. destruct (H0 z). apply (deterministic_bind H _ H1). Qed.

  Lemma ex_deterministic_bind:
    forall (A: Set) (a: M A) (z: A), deterministic a z ->
    forall (B: Set) (b: A -> M B), (exists v, deterministic (b z) v) ->
      exists w, deterministic (a >>= b) w.
  Proof. intros. destruct H0. apply (deterministic_bind H _ H0). Qed.

  Lemma ex_deterministic_bind_weak:
    forall (A: Set) (a: M A) (z: A), deterministic a z ->
    forall (B: Set) (b: A -> M B), (forall q, exists v, deterministic (b q) v) ->
      exists w, deterministic (a >>= b) w.
  Proof. intros. apply (deterministic_bind_weak H). assumption. Qed.

  Definition pick T: ne_list.L T -> M T := @ne_tree.Node T ∘ ne_list.map (@ne_tree.Leaf T).

  Lemma In_bind_inv (X Y: Set) (f: X -> M Y) (x: M X) r:
    ne_tree.In r (bind x f) -> exists z, ne_tree.In z x /\ ne_tree.In r (f z).
  Proof with eauto.
    induction x...
      simpl.
      intros.
      inversion_clear H.
      inversion_clear H0.
      destruct (IHx r H).
      destruct H0...
    intros.
    inversion_clear H.
    inversion_clear H0.
      destruct (IHx r H).
      destruct H0...
    destruct (IHx0 r (ne_tree.InNode H)).
    destruct H0.
    inversion_clear H0...
  Qed.

  Lemma bind_eq (X X' Y XM: Set)
    (f: X -> M Y) (f': X' -> M Y)
    (xm: X -> XM) (xm': X' -> XM):
    (forall p q, xm p = xm' q -> f p = f' q) ->
    forall (x: M X) (x': M X'),
    ne_tree.map xm x = ne_tree.map xm' x' ->
      bind x f = bind x' f'.
  Proof with auto.
    induction x; simpl; destruct x'; simpl; intros; try discriminate.
        apply H.
        inversion_clear H0...
      destruct l; simpl; intros.
        simpl.
        intros.
        rewrite (IHx t)...
        inversion_clear H0...
      discriminate.
    destruct l0.
      discriminate.
    simpl in H0.
    simpl.
    inversion H0.
    clear H0.
    f_equal.
    replace (NeTreeMonad.bind x f) with (NeTreeMonad.bind t f').
      Focus 2.
      symmetry.
      apply IHx...
    replace (ne_list.map (fun x0: NeTreeMonad.C X => NeTreeMonad.bind x0 f) l) with (ne_list.map (fun x0: NeTreeMonad.C X' => NeTreeMonad.bind x0 f') l0)...
    assert (ne_tree.map xm (ne_tree.Node l) = ne_tree.map xm' (ne_tree.Node l0)).
      simpl.
      rewrite H3...
    cset (IHx0 (ne_tree.Node l0) H0).
    inversion_clear H1...
  Qed.

  Lemma map_bind (X Y Z: Set) (f: Y -> Z) (g: X -> M Y) (x: M X):
    ne_tree.map f (bind x g) =
    bind x (fun xx => ne_tree.map f (g xx)).
  Proof with auto.
    induction x...
      simpl.
      rewrite IHx...
    simpl.
    rewrite IHx.
    f_equal.
    simpl in IHx0.
    inversion IHx0...
  Qed.

  Coercion ne_tree_isa_monad (A: Set) (a: ne_tree.T A): M A := a.

End NeTreeMonad.

Section MonadToys.

  Definition liftM (A B: Set) (f: A -> B) (M: Monad) (x: M A): M B :=
    xv <- x ; ret (f xv).

  Definition liftM2 (A B C: Set) (f: A -> B -> C) (M: Monad) (x: M A) (y: M B): M C :=
    xv <- x ; yv <- y ; ret (f xv yv).

  Fixpoint foldlM {A B: Set} {M: Monad} (f: A -> B -> M A) (x: A) (l: list B) {struct l}: M A :=
    match l with
    | nil => ret x
    | h :: t => fax <- f x h ; foldlM f fax t
    end. (* Haskell's foldM *)

  Fixpoint foldrM {A B: Set} {M: Monad} (f: B -> A -> M A) (x: A) (l: list B) {struct l}: M A :=
    match l with
    | nil => ret x
    | h :: t => t' <- foldrM f x t; f h t'
    end. (* missing in Haskell.. *)

  Lemma foldlM_cons (A B: Set) (M: Monad) (f: A -> B -> M A) (x: A) (h: B) (t: list B):
    foldlM f x (h :: t) = fax <- f x h ; foldlM f fax t.
  Proof. auto. Qed.

  Fixpoint filterM {A: Set} {M: Monad} (p: A -> M bool) (l: list A): M (list A) :=
    match l with
    | nil => ret nil
    | h :: t =>
      b <- p h ;
      t' <- filterM p t ;
      ret (if b then h :: t' else t')
    end. (* as in Haskell *)

  Lemma filterM_id (A: Set) (p: A -> IdMonad.M bool) (l: list A): filter p l = filterM p l.
  Proof with auto.
    induction l...
    simpl.
    rewrite IHl...
  Qed.

End MonadToys.

Implicit Arguments liftM [A B M].

Record MonadTrans: Type :=
  { transMonad: forall (m: Monad), extMonad m -> Monad
  ; lift: forall (m: Monad) (e: extMonad m) (A: Set), m A -> transMonad m e A
  }.
