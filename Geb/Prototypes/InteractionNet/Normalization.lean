/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Expression
public import Geb.Prototypes.InteractionNet.Observation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# From contextual evaluation to completed execution

A closed expression's initial configuration is an evaluator attached to an empty
environment and one observable result wire. Contextual normalization specializes to this
continuation and consumes every equation. Tree read-back then connects the closed result
to the executable kernel runner.

## Main statements

* {lit}`FirstOrder.evaluates_initial` — contextual evaluation reaches a completed initial net.
* {lit}`Kernel.run_of_evaluates` — contextual evaluation at a tree yields a successful bounded run.

## Tags

interaction net, normalization, execution, read-back, contextual evaluation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

namespace FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- A closed contextual evaluation yields a finite execution with no remaining equations. -/
theorem evaluates_initial (p : Program (φ := φ) dataArity)
    (e : Expr (φ := φ) dataArity 0) (v : Value dataArity)
    (h : Evaluates dataArity p e Fin.elim0 v) :
    ∃ N, (system dataArity p).Reaches (initial dataArity e)
      ⟨[Value.embed dataArity v], [], N⟩ := by
  let c : Config (netArity (φ := φ) dataArity) := ⟨[Term.var 0], [], 1⟩
  have hc : c.names = [0] := rfl
  have hb : ∀ x ∈ c.names, x < c.nextName := by
    intro x hx
    rw [hc] at hx
    obtain rfl := List.mem_singleton.mp hx
    exact Nat.zero_lt_one
  obtain ⟨N, _, hs⟩ := h 0 c hb
    (by simp [evalTask])
    (by intro b hb; obtain rfl := List.mem_singleton.mp hb; rw [hc]; rfl)
  have he : (fun i : Fin 0 ↦ Value.embed (φ := φ) dataArity (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact i.elim0
  refine ⟨N, ?_⟩
  simpa only [tasks, evalTask, resolve, List.foldl_cons, List.foldl_nil,
    Config.subst, c, List.map_cons, List.map_nil, Term.subst_var, ↓reduceIte,
    List.singleton_append, he, initial] using hs

end FirstOrder

namespace Kernel

open FirstOrder

/-- A compiled function application with the expected contextual tree value succeeds at
some finite bound in the executable runner. -/
theorem run_of_evaluates (P : List Geb.Kernel.Tree) (t x y : Geb.Kernel.Tree) (e : E 0)
    (he : compile t [] = some e)
    (hv : Evaluates dataArity (program P) (apply e (literal x)) Fin.elim0 (treeValue y)) :
    ∃ steps, run P steps t x = some y := by
  obtain ⟨N, steps, hs⟩ := evaluates_initial dataArity (program P) _ _ hv
  refine ⟨steps, ?_⟩
  simp only [run, initial, he, Option.map_some]
  let observe (d : Config (netArity (φ := Op) dataArity)) :=
    if !d.equations.isEmpty then none else match d.interface with
      | [v] => readback v
      | _ => none
  change observe ((FirstOrder.system dataArity (program P)).run steps
    (FirstOrder.initial dataArity (apply e (literal x)))) = some y
  exact (congrArg observe hs).trans (readback_treeTerm y)

end Kernel

end Geb.InteractionNet

end
