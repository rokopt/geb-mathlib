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

/-- A substitution depends only on the names occurring in its argument. -/
theorem subst_congr (ρ σ : ν → Term arity μ) (t : Term arity ν)
    (h : ∀ x ∈ t.names, ρ x = σ x) : t.subst ρ = t.subst σ := by
  apply PFunctor.FreeM.rec (motive := fun t ↦
    (∀ x ∈ names t, ρ x = σ x) → subst ρ t = subst σ t)
    (fun x h ↦ h x (List.mem_singleton_self _)) (fun a ts ih ht ↦ ?_) t h
  change agent a (fun i ↦ subst ρ (ts i)) = agent a (fun i ↦ subst σ (ts i))
  congr 1
  funext i
  apply ih i
  intro x hx
  apply ht x
  exact List.mem_flatten.mpr ⟨names (ts i), List.mem_ofFn.mpr ⟨i, rfl⟩, hx⟩

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

/-- Substitutions compose pointwise on every interface and equation term. -/
theorem subst_subst (ρ σ : ℕ → Term arity ℕ) (c : Config arity) :
    (c.subst σ).subst ρ = c.subst (fun x ↦ (σ x).subst ρ) := by
  cases c
  simp only [subst, List.map_map, Function.comp_def, Term.subst_subst]

/-- The identity substitution leaves a configuration unchanged. -/
@[simp] theorem subst_var_self (c : Config arity) : c.subst Term.var = c := by
  cases c
  simp [subst, show Term.subst (arity := arity) (ν := ℕ) Term.var = id from
    funext Term.subst_var_self]

/-- Configuration substitution depends only on its occurring wire names. -/
theorem subst_congr (ρ σ : ℕ → Term arity ℕ) (c : Config arity)
    (h : ∀ x ∈ c.names, ρ x = σ x) : c.subst ρ = c.subst σ := by
  have hi : ∀ t ∈ c.interface, t.subst ρ = t.subst σ := by
    intro t ht
    apply Term.subst_congr
    intro x hx
    exact h x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, ht, hx⟩))
  have he : ∀ e ∈ c.equations,
      (e.1.subst ρ, e.2.subst ρ) = (e.1.subst σ, e.2.subst σ) := by
    intro e he
    apply Prod.ext <;> apply Term.subst_congr <;> intro x hx
    · exact h x (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨e, he, List.mem_append_left _ hx⟩))
    · exact h x (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨e, he, List.mem_append_right _ hx⟩))
  cases c
  simp only [subst]
  congr 1
  · exact List.map_congr_left hi
  · exact List.map_congr_left he

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
