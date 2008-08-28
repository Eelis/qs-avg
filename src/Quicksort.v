
Set Implicit Arguments.

Require Import Util.
Require Import List.
Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Monads.
Require Import Measured.
Require Import Coq.Program.Wf.
Require Import nats_below.
Require Import ListUtils.
Require Import Bool.
Require Import Recdef.
Require Import MonoidMonadTrans.
Require Import Compare_dec.
Require Coq.Program.Wf.
(*Require Import ListUtils.*)
Require Import Wf_nat.
Require Import ArithLems.
Require Omega.

(*Extraction Language Haskell.*)

(*Require Import Compare_dec.*)

(*Definition ltb (x y: nat): bool := negb (leb y x).
Definition geb (x y: nat): bool := leb y x.*)

Definition numbers: list nat := 3 :: 1 :: 0 :: 4 :: 5 :: 2 :: nil.

Hint Resolve length_filter_le.

Module nonmonadic_using_Program.

  Program Fixpoint qs (l: list nat) {measure length l}: list nat :=
    match l with
    | nil => nil
    | pivot :: t => qs (filter (geb pivot) t) ++ (pivot :: nil) ++ qs (filter (ltb pivot) t)
    end.

  Next Obligation. simpl; auto with arith. Qed.
  Next Obligation. simpl; auto with arith. Qed.

  (*Eval vm_compute in qs numbers.*)

End nonmonadic_using_Program.

(*
Module nonmonadic_using_wf_ind.

  Definition qs (l: list nat): list nat.
  Proof with unfold MR; simpl; auto with arith.
    apply (well_founded_induction (measure_wf lt_wf (@length nat))).
    intro x.
    refine (
      match x as x return _ with
      | nil => fun _ => nil
      | pivot :: t => fun q => q (filter (geb pivot) t) _ ++ pivot :: nil ++ q (filter (ltb pivot) t) _
      end)...
  Defined.

  Eval compute in qs numbers.

End nonmonadic_using_wf_ind.
*)

Module mon_det. (* monadic, deterministic. This is the version used for the worst-case proof. *)
Section mon_det. (* For variable discharging. *)

  Variables (M: Monad) (T: Set).

  Definition filter (c: T -> M bool) (l: list T): M { l': list T | length l' <= length l }.
    (* Something with result type  M (list T)  is not good enough, because then   refine (u <- filter ... ; _)   just gives   u: list T, which is useless. *)
  Proof with auto with arith.
    induction l.
      refine (ret (exist _ nil _))...
    refine (
      t <- IHl ;
      let (x, l0) := t in
      b <- c a ;
      ret (if b then exist _ (a :: x) _ else exist _ x _)
    ); simpl...
  Defined.

  Fixpoint simple_filter (c: T -> M bool) (l: list T): M (list T) :=
    match l with
    | nil => ret nil
    | h :: t =>
      t' <- simple_filter c t ;
      b <- c h ;
      ret (if b then h :: t' else t')
    end.

  Variable le: T -> T -> M bool.

  Definition gt (x y: T): M bool := liftM negb (le x y).

  Definition simple_qs: list T -> M (list T).
  Proof with unfold MR; simpl; auto with arith.
    refine (well_founded_induction (measure_wf lt_wf (@length T)) (fun _ => M (list T)) (fun x =>
      match x as x return _ with
      | nil => fun _ => ret nil
      | pivot :: t => fun q =>
          lower <- simple_filter (gt pivot) t ;
          lower_sorted <- q lower _ ;
          upper <- simple_filter (le pivot) t ;
          upper_sorted <- q upper _ ;
          ret (lower_sorted ++ pivot :: nil ++ upper_sorted)
      end
    ))...
  Proof.
    (* no good, firewall *)
  Abort.

  Program Fixpoint qs (l: list T) {measure length l}: M (list T) :=
    match l with
    | nil => ret nil
    | pivot :: t =>
        lower <- filter (gt pivot) t >>= qs ;
        upper <- filter (le pivot) t >>= qs;
        ret (lower ++ pivot :: upper)
    end.

  Next Obligation. simpl. auto with arith. Qed.
  Next Obligation. simpl. auto with arith. Qed.
    (* "Solve All Obligations using ..." does not seem to work. *)

(*
  Definition qs: list T -> M (list T).
  Proof with unfold MR; simpl; auto with arith.
    refine (well_founded_induction (measure_wf lt_wf (@length T)) (fun _: list T => M (list T)) (fun x =>
      match x as x return _ with
      | nil => fun _ => ret nil
      | pivot :: t => fun q =>
          lower <- filter (gt pivot) t ;
          lower_sorted <- q (proj1_sig lower) _ ;
          upper <- filter (le pivot) t ;
          upper_sorted <- q (proj1_sig upper) _ ;
          ret (lower_sorted ++ pivot :: nil ++ upper_sorted)
      end
    ))...
  Proof. destruct lower... destruct upper... Defined.
*)

End mon_det.
End mon_det.

Implicit Arguments mon_det.qs [M T].

Definition profiled_leb (x y: nat): SimplyProfiled bool := (1, leb x y).
Eval vm_compute in mon_det.qs profiled_leb numbers.

Eval vm_compute in mon_det.qs (M:=IdMonad.M) leb numbers.

(*Implicit Arguments mon_det.qs [M T].*)
(*
Definition plain_leb: nat -> nat -> IdMonad.M bool := leb. (* lift *)
Eval compute in (mon_det.qs plain_leb numbers).

Definition counted_leb (x y: nat): CM bool := (1, leb x y). (* lift *)
Eval compute in (mon_det.qs counted_leb numbers).

Eval vm_compute in (mon_det.pqs counted_leb numbers).
*)
(*Definition ex_qs: list nat -> list nat := monadic.qs plain_leb.*)
(*Extraction "extracted" ex_qs.*)

Module mon_nondet. (* version used for average case proof *)
Section mon_nondet.

  Variables (T: Set) (M: Monad) (cmp: T -> T -> M comparison).

  Fixpoint partition (pivot: T) (l: list T) :
      M { p: Partitioning T | Permutation (p Eq ++ p Lt ++ p Gt) l } :=
        (* can't include a nice ordered-ness spec here, because we only have monadic cmp *)
    match l return M { p: Partitioning T | Permutation (p Eq ++ p Lt ++ p Gt) l } with
    | nil => ret (@emp T)
    | h :: t =>
        b <- cmp h pivot;
        tt <- partition pivot t ;
        ret (addToPartitioning b h tt)
    end.
(*
Inductive IMonad: Set -> Type :=
  | ret' (A: Set): A -> IMonad A
  | cmp': T -> T -> IMonad comparison
  | bind' (A B: Set): IMonad A -> (A -> IMonad B) -> IMonad B.

  Fixpoint interpret (A: Set) (m: IMonad A): M A :=
    match m in IMonad aap return M aap with
    | ret' Y x => ret x
    | cmp' x y => cmp x y
    | bind' _ _ x f => bind (interpret x)  (@interpret _ ∘ f)
    end.

  Fixpoint mpartition (pivot: T) (l: list T) {struct l}: IMonad { p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l } :=
    match l return IMonad { p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l } with
    | nil => ret' emp
    | h :: t =>
        bind' (cmp' h pivot) (fun b =>
        bind' (mpartition pivot t) (fun tt =>
        ret' (addToPartitioning b h tt)))
    end.

  Hypothesis Mext: extMonad M.

  Lemma partition_honest: forall p l, interpret (mpartition p l) = partition p l.
  Proof with auto.
    induction l...
    simpl.
    unfold compose.
    apply Mext.
    intro.
    simpl.
    rewrite IHl.
    apply Mext.
    intro.
    unfold compose.
    simpl...
  Qed.
*)
  Variable pick: forall (A: Set), ne_list.L A -> M A.

  Program Fixpoint qs (l: list T) {measure length l}: M (list T) :=
    match l with
    | nil => ret nil
    | h :: t =>
        i <- pick (nats_below_S (length t));
        part <- partition (vec.nth (h :: t) i) (vec.remove (h :: t) i);
        low <- qs (part Lt);
        upp <- qs (part Gt);
        ret (low ++ vec.nth (h :: t) i :: part Eq ++ upp)
    end.

  Next Obligation.
    simpl.
    replace (length t) with (length (vec.remove (h :: t) i)).
      rewrite <- (Permutation_length H).
      repeat rewrite app_length.
      omega.
    rewrite vec.length.
    reflexivity.
  Qed.

  Next Obligation.
    simpl.
    replace (length t) with (length (vec.remove (h :: t) i)).
      rewrite <- (Permutation_length H).
      repeat rewrite app_length.
      omega.
    rewrite vec.length.
    reflexivity.
  Qed.

End mon_nondet.
End mon_nondet.

Require Import SortOrder.

Fixpoint simplerPartition (e: E) (d: e) (l: list e) {struct l}: { p: Partitioning e | Permutation (p Eq ++ p Lt ++ p Gt) l } :=
  match l return { p: Partitioning e | Permutation (p Eq ++ p Lt ++ p Gt) l } with
  | nil => emp e
  | h :: t => addToPartitioning (Ecmp e h d) _ (simplerPartition e d t)
  end. (* todo: rename *)

Implicit Arguments mon_nondet.qs [M T].

(*Eval vm_compute in (@mon_nondet.qs IdMonad.M _ nat_cmp ne_list.head numbers).*)

Module nonmonadic_using_Function.

  Function qs (l: list nat) {measure length l}: list nat :=
    match l with
    | nil => nil
    | pivot :: t => qs (filter (geb pivot) t) ++ (pivot :: nil) ++ qs (filter (ltb pivot) t)
    end.
  Proof with simpl; auto with arith. intros... intros... Defined.

  (*Eval compute in qs numbers.*)

End nonmonadic_using_Function.
