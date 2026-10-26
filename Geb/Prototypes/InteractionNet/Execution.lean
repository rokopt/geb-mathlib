/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Kernel
import Geb.Prototypes.InteractionNet.ProgramCorrect
import Geb.Prototypes.InteractionNet.Preservation
import Geb.Prototypes.InteractionNet.Observation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Execution and observation of kernel nets

The kernel runner returns a tree only after its equations have all been consumed. Such a
result is the read-back of an actually reached normal configuration. Increasing the step
bound preserves a successful result. These are operational properties of the runner; the
connection to the kernel's denotation additionally requires normalization and adequacy of
the compilation.

## Main statements

* {lit}`FirstOrder.initial_wellFormed` — a compiled expression starts with a valid output wire.
* {lit}`FirstOrder.run_initial_wellFormed` — every finite run preserves valid wires.
* {lit}`Kernel.run_spec` — a successful result has a reachable normal configuration.
* {lit}`Kernel.run_names_eq_nil` — successful completion leaves no unresolved wire names.
* {lit}`Kernel.run_add_of_eq_some` — a successful result persists at larger step bounds.

## Tags

interaction net, kernel, execution, read-back, normal form, fuel
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

namespace FirstOrder

/-- Every closed expression starts with one wire, both of whose ends are present. -/
theorem initial_wellFormed {δ φ : Type} (dataArity : δ → ℕ)
    (e : Expr (φ := φ) dataArity 0) : (initial dataArity e).WellFormed := by
  simp only [Config.WellFormed, Config.names, initial, List.flatMap_cons,
    List.flatMap_nil, Term.names_var, Term.names_agent, List.ofFn_zero, List.ofFn_succ,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append]
  constructor
  · intro x
    by_cases hx : x = 0 <;> simp [-List.count_eq_one_of_mem, hx, Ne.symm]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst x
    exact Nat.zero_lt_one

/-- Every finite run of a translated closed expression preserves the wire invariant. -/
theorem run_initial_wellFormed {δ φ : Type} (dataArity : δ → ℕ)
    (p : Program (φ := φ) dataArity) (e : Expr dataArity 0) (n : ℕ) :
    ((system dataArity p).run n (initial dataArity e)).WellFormed :=
  System.run_wellFormed _ (system_rule_linear dataArity p) _
    (initial_wellFormed dataArity e) n

end FirstOrder

namespace Kernel

open Geb.Kernel

/-- Every compiled kernel initial state has valid wires. -/
theorem initial_wellFormed (t x : Tree)
    (c : Config (FirstOrder.netArity (φ := Op) dataArity))
    (h : initial t x = some c) : c.WellFormed := by
  obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact FirstOrder.initial_wellFormed dataArity (apply f (literal x))

/-- Finite kernel executions preserve valid wires, independently of the source's typing. -/
theorem run_wellFormed (P : List Tree) (t x : Tree)
    (c : Config (FirstOrder.netArity (φ := Op) dataArity)) (h : initial t x = some c)
    (n : ℕ) : ((system P).run n c).WellFormed :=
  System.run_wellFormed _ (FirstOrder.system_rule_linear dataArity (program P)) _
    (initial_wellFormed t x c h) n

/-- A successful run supplies its actual initial state, final tree term, and normal result. -/
theorem run_spec (P : List Tree) (n : ℕ) (t x y : Tree) (h : run P n t x = some y) :
    ∃ c v, initial t x = some c ∧
      (system P).Reaches c ((system P).run n c) ∧
      ((system P).run n c).equations = [] ∧
      (system P).Normal ((system P).run n c) ∧
      ((system P).run n c).interface = [v] ∧ readback v = some y := by
  unfold run at h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  · rename_i he
    have heq : ((system P).run n c).equations = [] := by simpa using he
    split at h
    · rename_i v hv
      exact ⟨c, v, hc, ⟨n, rfl⟩, heq,
        (system P).normal_of_equations_eq_nil _ heq, hv, h⟩
    · contradiction

/-- Once a run returns a result, any further number of steps returns the same result. -/
theorem run_add_of_eq_some (P : List Tree) (n m : ℕ) (t x y : Tree)
    (h : run P n t x = some y) : run P (n + m) t x = some y := by
  obtain ⟨c, v, hc, _, he, hn, hv, hy⟩ := run_spec P n t x y h
  have hr : (system P).run (n + m) c = (system P).run n c := by
    rw [System.run_add, System.run_of_normal _ hn]
  simpa [run, hc, hr, he, hv] using hy

/-- A successful run consumes all internal wires as well as all pending equations. -/
theorem run_names_eq_nil (P : List Tree) (n : ℕ) (t x y : Tree)
    (h : run P n t x = some y)
    (c : Config (FirstOrder.netArity (φ := Op) dataArity)) (hc : initial t x = some c) :
    ((system P).run n c).names = [] := by
  obtain ⟨d, v, hd, _, he, _, hv, hy⟩ := run_spec P n t x y h
  have hcd : c = d := Option.some.inj (hc.symm.trans hd)
  subst d
  simp only [Config.names, he, hv, List.flatMap_cons, List.flatMap_nil,
    names_eq_nil_of_readback v y hy, List.append_nil]

end Kernel

end Geb.InteractionNet

end
