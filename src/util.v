Set Implicit Arguments.

Require Import Relations.
Require Export Basics.
Require Import Setoid.

Definition proj1_conj (A B: Prop) (c: A /\ B): A :=
  match c with conj x _ => x end.

Definition proj2_conj (A B: Prop) (c: A /\ B): B :=
  match c with conj _ x => x end.

Lemma eq_trans (X: Set) (a b c: X): a = b -> b = c -> a = c.
Proof. intros. subst. reflexivity. Qed.

Definition cmp_cmp (x y: comparison): { x = y } + { x <> y } :=
  (* instead of being lazy with tactics, let's try to make as short a term as possible *)
  match x, y return { x = y } + { x <> y } with
  | Lt, Lt | Gt, Gt | Eq, Eq => left _ (refl_equal _)
  | a, b => right _ (
      match a, b
      return (fun _ => match a, b with Lt, Lt | Gt, Gt | Eq, Eq => True | _, _ => ~(a = b) end) _ with
        (* removing the silly abstraction breaks the definitions.. curious *)
      | Lt, Lt | Gt, Gt | Eq, Eq => I
      | Lt, _ => fun q =>
        match q in _ = t return match t with Lt => True | _ => False end with refl_equal => I end
      | Gt, _ => fun q =>
        match q in _ = t return match t with Gt => True | _ => False end with refl_equal => I end
      | Eq, _ => fun q =>
        match q in _ = t return match t with Eq => True | _ => False end with refl_equal => I end
      end
    )
  end. (* todo: derive this using the new equality Schemes *)

Fixpoint nat_cmp (x y: nat) {struct x}: comparison :=
  match x, y with
  | 0, 0 => Eq
  | 0, S _ => Lt
  | S _, 0 => Gt
  | S x', S y' => nat_cmp x' y'
  end.

Ltac cset e := let v := fresh in set (v := e); clearbody v.
Ltac cset' e := let v := fresh in set (v := e) in *; clearbody v.

Ltac extro x := generalize x; clear x.

Definition unsum_bool (A B: Prop) (sb: sumbool A B): bool := if sb then true else false.

Definition decision (P: Prop): Set := { P } + { ~ P }.
Definition predDecider (T: Set) (P: T -> Prop): Type := forall t, decision (P t).

Lemma negb_inv (b b': bool): negb b = negb b' -> b = b'.
Proof. destruct b; destruct b'; auto. Qed.

Lemma negb_negb (b: bool): negb (negb b) = b.
Proof. destruct b; auto. Qed.

Definition id {X} (x: X): X := x.

(* extensional equality on simple functions *)

Definition ext_eq (A B: Type) (f g: A -> B): Prop := forall x, f x = g x.

Lemma ext_eq_trans: forall A B, transitive _ (@ext_eq A B).
Proof. intros. unfold transitive. intros. intro. rewrite H. rewrite H0. reflexivity. Qed.

Lemma ext_eq_refl: forall A B, reflexive _ (@ext_eq A B).
Proof. intros. unfold reflexive. intros. intro. reflexivity. Qed.

Lemma ext_eq_sym: forall A B, symmetric _ (@ext_eq A B).
Proof. intros. unfold symmetric. intros. intro. rewrite H. reflexivity. Qed.

Add Parametric Relation X Y: (X -> Y) (@ext_eq X Y)
  reflexivity proved by (@ext_eq_refl X Y)
  symmetry proved by (@ext_eq_sym X Y)
  transitivity proved by (@ext_eq_trans X Y)
    as ext_eq_rel.

Lemma ext_eq_rw (A B: Type) (f g: A -> B): ext_eq f g -> forall x, f x = g x.
Proof. intros. apply H. Qed.

(* function composition *)

Hint Unfold compose.

Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

Lemma comp_apply (A B C: Set) (f: B -> C) (g: A -> B) (x: A): (f ∘ g) x = f (g x).
Proof. reflexivity. Qed.

Lemma comp_ass (A B C D: Set) (f: A -> B) (g: B -> C) (h: C -> D): h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. reflexivity. Qed.

Definition compose_lunit A B (f: A -> B): ext_eq (@id B ∘ f) f.
Proof. intros. intro. reflexivity. Qed.

Definition compose_runit A B (f: A -> B): ext_eq (f ∘ @id A) f.
Proof. intros. intro. reflexivity. Qed.

Add Parametric Morphism (X Y Z: Set): (@compose X Y Z) with signature (@ext_eq Y Z) ==> (@ext_eq X Y) ==> (@ext_eq X Z) as compose_ext_eq_morph.
Proof.
  intros.
  intro.
  unfold compose.
  unfold ext_eq in *.
  rewrite H0.
  rewrite H.
  reflexivity.
Qed.

Definition map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): C * B := (fst p, f (snd p)).

Lemma fst_map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): fst (map_snd f p) = fst p.
Proof. destruct p. auto. Qed.
