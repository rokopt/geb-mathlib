/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Geb.Prototypes.QuotientPRA.Basic

meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Endpoints of presheaf W-type constructors are constructor applications

Restricting a tree of a presheaf W-type along a morphism {lit}`g` rebuilds its root:
the restricted tree's root shape is {lit}`shapeRestr g` of the original root shape,
and its children are children of the original ({name}`PresheafPFunctor.wRestrTree`).
So the root shape of a restriction depends only on the root shape of the tree
({lit}`head_map`). If a family of trees all have one root shape, their restrictions
along {lit}`g` all have one root shape too ({lit}`head_map_of_head_eq`).

In a quotient presheaf polynomial functor ({lit}`GebProto.QuotientPRA.W`) the
endpoints of a witness are its restrictions along the two parallel morphisms, and the
index of a dependent term is its restriction along a morphism of the base. A
constructor of fixed shape therefore has endpoints, and gives terms indices, whose
root shapes are fixed. Reflexivity, symmetry, transitivity and transport require
endpoints or indices that are arguments of the constructor, whose root shapes vary,
so as soon as two arguments have different root shapes none of them is a constructor
of fixed shape: {lit}`no_uniform_refl`, {lit}`no_uniform_symm`,
{lit}`no_uniform_trans` and {lit}`no_uniform_transport`.

## Main definitions

* {lit}`head` — the root shape of a tree of a presheaf W-type.

## Main statements

* {lit}`head_map` — the root shape of a restriction is the restriction of the root
  shape.
* {lit}`head_map_of_head_eq` — restriction sends trees of one root shape to trees of
  one root shape.
* {lit}`no_uniform_refl`, {lit}`no_uniform_symm`, {lit}`no_uniform_trans`,
  {lit}`no_uniform_transport` — reflexivity, symmetry, transitivity and transport
  are not constructors of fixed shape once two arguments differ in root shape.

## Implementation notes

The statements quantify over an arbitrary function into the W-type rather than over
shapes of the functor, so they exclude any constructor whose applications all have
one root shape, however its arguments are arranged. Constructors indexed by the root
shape of an argument escape the argument: reflexivity at a term whose root shape is
{lit}`c` can be a witness constructor whose two endpoints are both {lit}`c` applied to
the constructor's arguments.

## References

* {cite}`Weber2007`

## Tags

W-type, presheaf, parametric right adjoint, restriction, quotient,
quotient inductive-inductive type
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

universe uC uA uB vC uI vI u

section Head

variable {C : Type uC} [Category.{vC} C] (F : PresheafPFunctor.{uC, uC, uA, uB, vC, vC} C C)

/-- The root shape of a tree of the presheaf W-type. -/
def head {c : C} (w : F.W.obj ⟨c⟩) : F.A := PFunctor.W.head w.down.1.1

/-- The root shape of a restriction along {lit}`g` is {lit}`shapeRestr g` of the root
shape. -/
theorem head_map {c c' : C} (g : c' ⟶ c) (w : F.W.obj ⟨c⟩) :
    head F (F.W.map g.op w) = (F.shapeRestr g ⟨head F w, w.down.2.1⟩).1 := by
  obtain ⟨⟨⟨tree, hv⟩, hi, hn⟩⟩ := w
  cases tree with
  | mk a f => rfl

/-- Restriction along {lit}`g` sends a family of trees all of root shape {lit}`ρ` to a
family of trees all of root shape {lit}`shapeRestr g ρ`. -/
theorem head_map_of_head_eq {A : Sort u} {c c' : C} (g : c' ⟶ c) (s : A → F.W.obj ⟨c⟩)
    (ρ : F.Shape c) (hs : ∀ a, head F (s a) = ρ.1) (a : A) :
    head F (F.W.map g.op (s a)) = (F.shapeRestr g ρ).1 :=
  (head_map F g (s a)).trans
    (congrArg (fun r ↦ (F.shapeRestr g r).1) (Subtype.ext (hs a)))

end Head

variable {I : Type uI} [Category.{vI} I]
  (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} (I × WalkingParallelPair)
    (I × WalkingParallelPair))

/-- Reflexivity is not a witness constructor of fixed shape: a function sending each
term to a witness with that term as source, all of one root shape, makes all terms
have one root shape. -/
theorem no_uniform_refl {i : I} (t₁ t₂ : F.W.obj ⟨termObj i⟩) (h : head F t₁ ≠ head F t₂) :
    ¬ ∃ (ρ : F.Shape (eqObj i)) (refl : F.W.obj ⟨termObj i⟩ → F.W.obj ⟨eqObj i⟩),
      (∀ t, head F (refl t) = ρ.1) ∧ ∀ t, src F.W i (refl t) = t := by
  rintro ⟨ρ, refl, hρ, hsrc⟩
  have key := head_map_of_head_eq F (srcHom i) refl ρ hρ
  exact h (((congrArg (head F) (hsrc t₁)).symm.trans (key t₁)).trans
    ((key t₂).symm.trans (congrArg (head F) (hsrc t₂))))

/-- Symmetry is not a witness constructor of fixed shape: a function sending each
witness to one whose source is the original's target, all of one root shape, makes
the targets of all witnesses have one root shape. -/
theorem no_uniform_symm {i : I} (e₁ e₂ : F.W.obj ⟨eqObj i⟩)
    (h : head F (tgt F.W i e₁) ≠ head F (tgt F.W i e₂)) :
    ¬ ∃ (ρ : F.Shape (eqObj i)) (symm : F.W.obj ⟨eqObj i⟩ → F.W.obj ⟨eqObj i⟩),
      (∀ e, head F (symm e) = ρ.1) ∧ ∀ e, src F.W i (symm e) = tgt F.W i e := by
  rintro ⟨ρ, symm, hρ, hsrc⟩
  have key := head_map_of_head_eq F (srcHom i) symm ρ hρ
  exact h (((congrArg (head F) (hsrc e₁)).symm.trans (key e₁)).trans
    ((key e₂).symm.trans (congrArg (head F) (hsrc e₂))))

/-- Transitivity is not a witness constructor of fixed shape: a function sending each
composable pair of witnesses to one whose source is the first witness's source, all
of one root shape, makes the sources of all first witnesses of composable pairs have
one root shape. -/
theorem no_uniform_trans {i : I}
    (p₁ p₂ : {p : F.W.obj ⟨eqObj i⟩ × F.W.obj ⟨eqObj i⟩ // tgt F.W i p.1 = src F.W i p.2})
    (h : head F (src F.W i p₁.1.1) ≠ head F (src F.W i p₂.1.1)) :
    ¬ ∃ (ρ : F.Shape (eqObj i))
      (trans : {p : F.W.obj ⟨eqObj i⟩ × F.W.obj ⟨eqObj i⟩ // tgt F.W i p.1 = src F.W i p.2} →
        F.W.obj ⟨eqObj i⟩),
      (∀ p, head F (trans p) = ρ.1) ∧ ∀ p, src F.W i (trans p) = src F.W i p.1.1 := by
  rintro ⟨ρ, trans, hρ, hsrc⟩
  have key := head_map_of_head_eq F (srcHom i) trans ρ hρ
  exact h (((congrArg (head F) (hsrc p₁)).symm.trans (key p₁)).trans
    ((key p₂).symm.trans (congrArg (head F) (hsrc p₂))))

/-- Transport along a morphism {lit}`f : i' ⟶ i` is not a term constructor of fixed
shape: a function sending a witness {lit}`e` over {lit}`i'` and a term over {lit}`i`
whose index along {lit}`f` is the source of {lit}`e` to a term whose index along
{lit}`f` is the target of {lit}`e`, all of one root shape, makes the targets of all
such witnesses have one root shape. -/
theorem no_uniform_transport {i' i : I} (f : i' ⟶ i)
    (p₁ p₂ : {p : F.W.obj ⟨eqObj i'⟩ × F.W.obj ⟨termObj i⟩ // restr F.W f p.2 = src F.W i' p.1})
    (h : head F (tgt F.W i' p₁.1.1) ≠ head F (tgt F.W i' p₂.1.1)) :
    ¬ ∃ (ρ : F.Shape (termObj i))
      (transport :
        {p : F.W.obj ⟨eqObj i'⟩ × F.W.obj ⟨termObj i⟩ // restr F.W f p.2 = src F.W i' p.1} →
          F.W.obj ⟨termObj i⟩),
      (∀ p, head F (transport p) = ρ.1) ∧
        ∀ p, restr F.W f (transport p) = tgt F.W i' p.1.1 := by
  rintro ⟨ρ, transport, hρ, hidx⟩
  have key := head_map_of_head_eq F (termHom f) transport ρ hρ
  exact h (((congrArg (head F) (hidx p₁)).symm.trans (key p₁)).trans
    ((key p₂).symm.trans (congrArg (head F) (hidx p₂))))

end GebProto.QuotientPRA
