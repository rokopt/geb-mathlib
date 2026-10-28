/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigEliminationSimulation
public import Geb.Prototypes.InteractionNet.ConfigGraphBoundary
public import Geb.Prototypes.InteractionNet.ConfigInteractionSimulation
public import Geb.Prototypes.InteractionNet.GraphClosure
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Textual reductions refine graph execution

Wire elimination preserves the compiled graph. Agent interaction makes one graph step to
the compiled textual result. Equation reversal and permutation preserve these statements,
so the textual scheduler's selected equation determines a finite graph execution at the
same ordered interface.

## Main statements

* {lit}`Config.eliminate_graph_eq` — executable wire elimination preserves the represented graph.
* {lit}`System.contract_graph_reaches` — either contraction orientation refines graph execution.
* {lit}`System.step_graph_reaches` — the textual scheduler refines graph execution.

## Tags

interaction net, calculus, compiler, graph, simulation, refinement, execution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ} {boundary : ℕ}

/-- Executable wire elimination preserves the compiled graph and its numeric interface positions. -/
theorem Config.eliminate_graph_eq (c d : Config arity) (x : ℕ) (t : Term arity ℕ)
    (hc : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (hd : d.Closed) (he : c.eliminate x t = some d)
    (bc : c.interface.length = boundary) (bd : d.interface.length = boundary) :
    ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).graphAt hc bc =
      d.graphAt hd bd := by
  unfold Config.eliminate at he
  split at he
  · rename_i hw
    cases Option.some.inj he
    cases bc
    rw [Config.graphAt_refl]
    obtain ⟨i⟩ := c.elimination_graph_iso x t hw.2 hc hd
    exact Quotient.sound ⟨i⟩
  · cases he

/-- Every permitted textual equation contraction refines a finite graph execution. -/
theorem System.contract_graph_reaches (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (e : Equation arity ℕ) (c d : Config arity)
    (hc : ({ c with equations := e :: c.equations } : Config arity).Closed) (hd : d.Closed)
    (h : s.contract e c = some d) (bc : c.interface.length = boundary)
    (bd : d.interface.length = boundary) :
    Relation.ReflTransGen (Graph.Step (s.toPortSystem linear oriented))
      (({ c with equations := e :: c.equations } : Config arity).graphAt hc bc)
      (d.graphAt hd bd) := by
  obtain ⟨t, u⟩ := e
  cases t with
  | pure x =>
    cases u with
    | pure y =>
      change (c.eliminate x (Term.var y)).orElse (fun _ ↦ c.eliminate y (Term.var x)) =
        some d at h
      cases he : c.eliminate x (Term.var y) with
      | none =>
        simp only [he, Option.orElse_none] at h
        erw [c.graphAt_swap _ hc bc,
          c.eliminate_graph_eq d y (Term.var x) (c.closed_swap _ hc) hd h bc bd]
      | some v =>
        simp only [he, Option.orElse_some, Option.some.injEq] at h
        subst v
        erw [c.eliminate_graph_eq d x (Term.var y) hc hd he bc bd]
    | liftBind b ys =>
      erw [c.eliminate_graph_eq d x (.agent b ys) hc hd h bc bd]
  | liftBind a xs =>
    cases u with
    | pure y =>
      erw [c.graphAt_swap _ hc bc,
        c.eliminate_graph_eq d y (.agent a xs) (c.closed_swap _ hc) hd h bc bd]
    | liftBind b ys =>
      change (match s.rule a b with
        | some r => some (r.fire xs ys c)
        | none => (s.rule b a).map (fun r ↦ r.fire ys xs c)) = some d at h
      cases hr : s.rule a b with
      | some r =>
        simp only [hr, Option.some.injEq] at h
        subst d
        cases bc
        erw [Config.graphAt_nextName
          { c with equations := r.instantiate c.nextName xs ys ++ c.equations }
            (c.nextName + r.fresh) hd bd]
        erw [Config.graphAt_refl, Config.graphAt_refl]
        exact .single (s.interaction_graph_step linear oriented c r hr xs ys hc hd)
      | none =>
        simp only [hr, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        erw [c.graphAt_swap _ hc bc]
        cases bc
        erw [Config.graphAt_nextName
          { c with equations := r.instantiate c.nextName ys xs ++ c.equations }
            (c.nextName + r.fresh) hd bd]
        erw [Config.graphAt_refl, Config.graphAt_refl]
        exact .single (s.interaction_graph_step linear oriented c r hr ys xs
          (c.closed_swap _ hc) hd)

/-- The textual scheduler's selected equation refines a finite graph execution. -/
theorem System.step_graph_reaches (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c d : Config arity) (hc : c.Closed) (hd : d.Closed)
    (h : s.step c = some d) (bc : c.interface.length = boundary)
    (bd : d.interface.length = boundary) :
    Relation.ReflTransGen (Graph.Step (s.toPortSystem linear oriented))
      (c.graphAt hc bc) (d.graphAt hd bd) := by
  obtain ⟨⟨e, i⟩, hm, hr⟩ := List.exists_of_findSome?_eq_some h
  have hi : c.equations[i]? = some e := List.mk_mem_zipIdx_iff_getElem?.mp hm
  have he : c.equations.take i ++ e :: c.equations.drop (i + 1) = c.equations := by
    have ht := List.take_append_drop i c.equations
    rw [List.drop_eq_getElem?_toList_append, hi] at ht
    exact ht
  have hp := List.perm_middle.symm.trans (List.Perm.of_eq he)
  rw [c.graphAt_perm _ hp hc bc]
  exact s.contract_graph_reaches linear oriented e
    { c with equations := c.equations.take i ++ c.equations.drop (i + 1) } d
    (c.closed_perm _ hp hc) hd hr bc bd

end Geb.InteractionNet

end
