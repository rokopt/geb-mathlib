/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# The W-type fold: computation rule and uniqueness

`WType.elim` is the non-dependent fold of a W-type: the morphism into a
given algebra of the polynomial endofunctor `X ↦ Σ a, β a → X`. mathlib
states the fold but neither its computation rule as a named `@[simp]`
lemma nor its uniqueness. Together the two make `WType β` the initial
algebra of that endofunctor, stated concretely.

## Main statements

* `WType.elim_mk` — the computation rule: the fold of a constructor
  application is the algebra applied to the folded children.
* `WType.elim_unique` — uniqueness: a function satisfying the
  computation rule is the fold.

## Implementation notes

`elim_mk` holds by `rfl`; mathlib's equation compiler generates the
equation, and the named `@[simp]` form is what makes the hypothesis
shape of `elim_unique` usable by `simp` at call sites. `elim_unique`
drives its recursion through an explicit `WType.rec` application into a
`Prop`-valued motive.

## References

* [GambinoHyland2004]

## Tags

W-type, fold, initial algebra, polynomial functor
-/

public section

universe uA uB uC

namespace WType

/-- The fold's computation rule: folding a constructor application
applies the algebra to the children's folds. -/
@[simp] theorem elim_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (a : α) (f : β a → WType β) :
    elim γ fγ (mk a f) = fγ ⟨a, fun b ↦ elim γ fγ (f b)⟩ :=
  rfl

/-- The fold is the unique function satisfying its computation rule.
With `elim` itself, this is the initiality of `WType β` among algebras
of the polynomial endofunctor `X ↦ Σ a, β a → X`. -/
theorem elim_unique {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (g : WType β → γ)
    (hg : ∀ (a : α) (f : β a → WType β),
      g (mk a f) = fγ ⟨a, fun b ↦ g (f b)⟩) :
    g = elim γ fγ :=
  funext fun x ↦
    rec (motive := fun x ↦ g x = elim γ fγ x)
      (fun a f ih ↦ (hg a f).trans (congrArg (fun h ↦ fγ ⟨a, h⟩) (funext ih))) x

end WType
