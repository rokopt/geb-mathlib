/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# The W-type fold and paramorphism: computation rules and uniqueness

`WType.elim` is the non-dependent fold of a W-type: the morphism into a
given algebra of the polynomial endofunctor `X ↦ Σ a, β a → X`. mathlib
states the fold but neither its computation rule as a named `@[simp]`
lemma nor its uniqueness. Together the two make `WType β` the initial
algebra of that endofunctor, stated concretely. `WType.para` generalises
the fold to a paramorphism, whose step additionally sees each node's
children as subtrees, not only as their folded values.

## Main definitions

* `WType.para` — the paramorphism: a fold whose step function receives
  each child as a subtree paired with its folded value.

## Main statements

* `WType.elim_mk` — the computation rule: the fold of a constructor
  application is the algebra applied to the folded children.
* `WType.elim_unique` — uniqueness: a function satisfying the
  computation rule is the fold.
* `WType.para_mk` — the paramorphism's computation rule.

## Implementation notes

`elim_mk` holds by `rfl`; mathlib's equation compiler generates the
equation, and the named `@[simp]` form is what makes the hypothesis
shape of `elim_unique` usable by `simp` at call sites. `elim_unique`
drives its recursion through an explicit `WType.rec` application into a
`Prop`-valued motive. `para` is `elim` at the product carrier
`WType β × γ`, whose first component reconstructs the subtree; its
computation rule `para_mk` does not hold by `rfl` and is proved through
that reconstruction.

## References

* [GambinoHyland2004]
* [Meertens1992]

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

/-- The algebra of the paramorphism fold: rebuild the node from the
children's reconstructed subtrees, and apply the step to the node. -/
@[expose] def paraStep {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) :
    (Σ a : α, β a → WType β × γ) → WType β × γ :=
  fun x ↦ (mk x.1 fun b ↦ (x.2 b).1, fγ x)

/-- The fold's first component reconstructs its input. -/
private theorem paraStep_fst {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (w : WType β) :
    (elim (WType β × γ) (paraStep γ fγ) w).1 = w :=
  rec (motive := fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).1 = w)
    (fun a _f ih ↦ congrArg (mk a) (funext ih)) w

/-- The paramorphism of a W-type: a fold whose step sees each node's
children as subtrees together with their folded values. Obtained from
`elim` at the product carrier `WType β × γ`, whose first component
reconstructs the subtree, so no new recursion is introduced.
[Meertens1992] -/
@[expose] def para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ :=
  fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).2

/-- The paramorphism's computation rule: it applies the step to the node's
children paired with their own paramorphisms. Unlike `elim_mk` this does
not hold by `rfl`; it is `paraStep_fst` under a `congrArg`. -/
@[simp] theorem para_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (a : α) (f : β a → WType β) :
    para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩ :=
  congrArg (fun h ↦ fγ ⟨a, h⟩)
    (funext fun b ↦ Prod.ext (paraStep_fst γ fγ (f b)) rfl)

end WType
