/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Substitution in configurations

Substitution composes by the free monad's associativity law. Wire elimination replaces an
occurrence everywhere in the remaining configuration. For a closed replacement, its only
effect on the occurrence list is to remove the eliminated name; all other wires retain
their number of ends.

## Main statements

* {lit}`Term.subst_subst` — substitutions compose.
* {lit}`Term.subst_of_names_eq_nil` — substitution leaves closed terms unchanged.
* {lit}`Config.names_subst` — the names of a substituted configuration.
* {lit}`Config.names_subst_closed` — eliminating a name with a closed replacement removes it.

## Tags

interaction calculus, substitution, wire, closed term
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν μ ξ : Type} {arity : α → ℕ}

namespace Term

/-- Substitutions compose by binding their replacements. -/
theorem subst_subst (ρ : μ → Term arity ξ) (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).subst ρ = t.subst (fun x ↦ (σ x).subst ρ) :=
  PFunctor.FreeM.bind_assoc t σ ρ

/-- Replacing names by themselves is the identity substitution. -/
@[simp] theorem subst_var_self (t : Term arity ν) : t.subst var = t :=
  PFunctor.FreeM.bind_pure t

/-- A substitution has no effect on a term with no names. -/
theorem subst_of_names_eq_nil (σ : ν → Term arity ν) (t : Term arity ν)
    (h : t.names = []) : t.subst σ = t := by
  apply PFunctor.FreeM.rec (motive := fun t ↦ names t = [] → subst σ t = t)
    (fun x hx ↦ by simp [names] at hx) (fun a ts ih ht ↦ ?_) t h
  change agent a (fun i ↦ subst σ (ts i)) = agent a ts
  congr 1
  funext i
  apply ih i
  exact (List.flatten_eq_nil_iff.mp ht) _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end Term

namespace Config

/-- Substitution replaces every occurrence in the configuration by its replacement's names. -/
theorem names_subst (σ : ℕ → Term arity ℕ) (c : Config arity) :
    (c.subst σ).names = c.names.flatMap (fun x ↦ (σ x).names) := by
  simp [names, subst, Term.names_subst, List.flatMap_map, List.flatMap_append,
    List.flatMap_assoc]

/-- Replacing a wire by a closed term removes that wire's names and introduces none. -/
theorem names_subst_closed (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (ht : t.names = []) :
    (c.subst fun y ↦ if y = x then t else Term.var y).names =
      c.names.filter (· != x) := by
  rw [names_subst]
  apply List.rec (motive := fun ns ↦
    ns.flatMap (fun y ↦ (if y = x then t else Term.var y).names) = ns.filter (· != x))
    rfl (fun a as ih ↦ ?_) c.names
  by_cases h : a = x <;> simp [h, ht, ih]

/-- Eliminating a name with a closed replacement preserves all other occurrence counts. -/
theorem count_names_subst_closed (c : Config arity) (x y : ℕ) (t : Term arity ℕ)
    (ht : t.names = []) (hxy : y ≠ x) :
    (c.subst fun z ↦ if z = x then t else Term.var z).names.count y = c.names.count y := by
  rw [names_subst_closed c x t ht]
  apply List.count_filter
  simpa using hxy

end Config

end Geb.InteractionNet

end
