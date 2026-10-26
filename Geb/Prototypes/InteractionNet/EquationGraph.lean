/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The forest and root wires of an equation list

An equation list supplies two indexed families of terms, one for each side. A root wire
joins the corresponding left and right terms. Enumerating the left terms before the right
terms preserves the multiplicity of every variable name, which is all the named-wire
assembly needs. Leaves and cells retain their structural occurrence identities.

## Main definitions

* {lit}`EquationGraph.fragments` — both term families as open graphs.
* {lit}`EquationGraph.rootWiring` — the wires joining corresponding equation roots.

## Main statements

* {lit}`EquationGraph.leaf_count` — the forest preserves every name's multiplicity.

## Tags

interaction net, equation, graph, wire, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.EquationGraph

open scoped FinEnum

variable {α ν : Type} {arity : α → ℕ}

/-- One root occurrence for each side of each equation. -/
abbrev Root (es : List (Equation arity ν)) := Fin es.length ⊕ Fin es.length

/-- The term at an equation's selected side. -/
def term (es : List (Equation arity ν)) : Root es → Term arity ν :=
  Sum.elim (fun i ↦ (es.get i).1) (fun i ↦ (es.get i).2)

/-- Translate each equation side independently, exposing its variable occurrences. -/
def fragments (es : List (Equation arity ν)) (i : Root es) : TermFragment arity ν :=
  (term es i).fragment

/-- Enumerate all left roots followed by all right roots. -/
def order (es : List (Equation arity ν)) : List (Root es) :=
  (List.finRange es.length).map Sum.inl ++ (List.finRange es.length).map Sum.inr

/-- Each root occurs once in the equation-side enumeration. -/
theorem order_unique (es : List (Equation arity ν)) : (order es).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,
    (List.nodup_finRange _).map Sum.inr_injective, ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  cases hxy

/-- The equation-side enumeration contains every root. -/
theorem order_cover (es : List (Equation arity ν)) (i : Root es) : i ∈ order es := by
  cases i with
  | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  | inr i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- Every equation connects its left and right roots. -/
def rootWiring (es : List (Equation arity ν)) : Wiring (Root es) where
  partner := Sum.swap
  involutive p := by cases p <;> rfl
  fixedPointFree p h := by cases p <;> cases h

/-- A forest leaf remembers its root occurrence and position within that term. -/
abbrev Leaf (es : List (Equation arity ν)) := Σ i, (fragments es i).Leaf

/-- The name written at a leaf occurrence. -/
def leafName (es : List (Equation arity ν)) (p : Leaf es) : ν :=
  (fragments es p.1).name p.2

/-- The equation forest's leaves in the selected root order. -/
def leafOrder (es : List (Equation arity ν)) : List (Leaf es) :=
  TermFragment.forestOrder (order es) (fragments es)

private theorem split_count [BEq ν] (es : List (Equation arity ν)) (x : ν) :
    ((es.flatMap fun e ↦ e.1.names) ++ (es.flatMap fun e ↦ e.2.names)).count x =
      (es.flatMap fun e ↦ e.1.names ++ e.2.names).count x := by
  apply List.rec (motive := fun es ↦
    ((es.flatMap fun e ↦ e.1.names) ++ (es.flatMap fun e ↦ e.2.names)).count x =
      (es.flatMap fun e ↦ e.1.names ++ e.2.names).count x) rfl (fun e es ih ↦ ?_) es
  simp only [List.flatMap_cons, List.count_append] at ih ⊢
  omega

/-- Splitting equation sides into two root families preserves every name's multiplicity. -/
theorem leaf_count [BEq ν] (es : List (Equation arity ν)) (x : ν) :
    ((leafOrder es).map (leafName es)).count x =
      (es.flatMap fun e ↦ e.1.names ++ e.2.names).count x := by
  change ((TermFragment.forestOrder (order es) (fragments es)).map
    (fun p ↦ (fragments es p.1).name p.2)).count x = _
  rw [TermFragment.forestOrder_names]
  simp only [fragments, Term.fragment_names, order, List.flatMap_append, List.flatMap_map,
    term, Sum.elim_inl, Sum.elim_inr]
  have hl : (List.finRange es.length).map es.get = es := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  change (((List.finRange es.length).flatMap fun i ↦ (es.get i).1.names) ++
    ((List.finRange es.length).flatMap fun i ↦ (es.get i).2.names)).count x = _
  have hlf (g : Equation arity ν → List ν) :
      (List.finRange es.length).flatMap (fun i ↦ g (es.get i)) = es.flatMap g := by
    simpa only [List.flatMap_map] using congrArg (fun l ↦ l.flatMap g) hl
  rw [hlf (fun e ↦ e.1.names), hlf (fun e ↦ e.2.names)]
  exact split_count es x

end Geb.InteractionNet.EquationGraph

end
