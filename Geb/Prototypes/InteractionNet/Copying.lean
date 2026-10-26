/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.InteractionNet.Output
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Copying constructor leaves

A fan on a nullary constructor allocates no internal wires. Its single interaction produces
one closed delivery for each requested copy. Delivering those results terminates whenever
the output names are distinct and each has one end in the continuation. This is the base
case of the contextual constructor-copying proof; copying arbitrary trees additionally
requires composing the recursively allocated child copies.

## Main statements

* {lit}`copy_leaf_step` — a leaf fan exposes its output deliveries in one interaction.
* {lit}`reaches_copy_leaf` — any number of leaf copies are delivered to a continuation.

## Tags

interaction net, copying, constructor, leaf, continuation, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

private theorem ofFn_eq_nil {γ : Type} {n : ℕ} (h : n = 0) (f : Fin n → γ) :
    List.ofFn f = [] := by
  apply List.eq_nil_of_length_eq_zero
  simpa only [List.length_ofFn] using h

/-- A nullary constructor has no free wire names. -/
theorem leaf_names (a : δ) (ha : dataArity a = 0)
    (ts : Fin (dataArity a) → Term (netArity (φ := φ) dataArity) ℕ) :
    (Term.agent (arity := netArity (φ := φ) dataArity) (data dataArity a) ts).names = [] := by
  rw [Term.names_agent, ofFn_eq_nil ha, List.flatten_nil]

/-- Copying a leaf produces precisely its closed deliveries and allocates no names. -/
theorem copy_leaf_step (p : Program (φ := φ) dataArity) (a : δ) (ha : dataArity a = 0)
    (ts : Fin (dataArity a) → Term (netArity dataArity) ℕ) (outs : List ℕ)
    (c : Config (netArity dataArity)) :
    (system dataArity p).step
      { c with equations := (Term.agent (fan dataArity outs.length)
        (fun i ↦ Term.var (outs.get i)), Term.agent (data dataArity a) ts) :: c.equations } =
      some (deliveries (outs.map fun x ↦ (x, Term.agent (data dataArity a) ts)) c) := by
  apply System.step_cons
  change some { c with
    equations := (fanRule dataArity outs.length (.inl a)).instantiate c.nextName
      (fun i ↦ Term.var (outs.get i)) ts ++ c.equations
    nextName := c.nextName + (fanRule dataArity outs.length (.inl a)).fresh } = _
  have hz : ∀ {γ : Type} (f : Fin (dataArity a) → γ), List.ofFn f = [] :=
    fun f ↦ ofFn_eq_nil ha f
  simp only [fanRule, Rule.instantiate, hz, List.nil_append, List.map_ofFn,
    Function.comp_def, Term.subst_var, Sum.elim_inl, Term.subst_agent, Sum.elim_inr,
    deliveries, List.map_map]
  have ht : ∀ (f : Fin (dataArity a) → Term (netArity dataArity) ℕ), f = ts := by
    intro f
    funext i
    have hi := i.isLt
    exfalso
    omega
  simp only [ht, constructorArity, ha, Nat.zero_mul, Nat.add_zero]
  congr 2
  have hm := List.map_ofFn (f := outs.get)
    (g := fun x ↦ (Term.var (arity := netArity (φ := φ) dataArity) x,
      Term.agent (arity := netArity (φ := φ) dataArity) (data dataArity a) ts))
  simpa only [List.ofFn_get, Function.comp_def] using
    congrArg (fun es ↦ es ++ c.equations) hm.symm

/-- A fan delivers any number of copies of a nullary constructor to distinct output wires. -/
theorem reaches_copy_leaf (p : Program (φ := φ) dataArity) (a : δ)
    (ha : dataArity a = 0)
    (ts : Fin (dataArity a) → Term (netArity dataArity) ℕ) (outs : List ℕ)
    (c : Config (netArity dataArity)) (hn : outs.Nodup)
    (hc : ∀ x ∈ outs, c.names.count x = 1) :
    (system dataArity p).Reaches
      { c with equations := (Term.agent (fan dataArity outs.length)
        (fun i ↦ Term.var (outs.get i)), Term.agent (data dataArity a) ts) :: c.equations }
      (resolve (outs.map fun x ↦ (x, Term.agent (data dataArity a) ts)) c) := by
  apply System.reaches_trans _
    (System.reaches_of_step _ (copy_leaf_step dataArity p a ha ts outs c))
  apply reaches_resolve
  · intro b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    exact leaf_names dataArity a ha ts
  · simpa only [List.map_map, Function.comp_def, List.map_id'] using hn
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact hc x hx

end Geb.InteractionNet.FirstOrder

end
