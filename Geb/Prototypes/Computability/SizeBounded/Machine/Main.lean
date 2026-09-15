/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Wrapper
import Geb.Prototypes.Computability.SizeBounded.Machine.Transport
meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# Polynomial time and linear space

The meaning of an expression of the algebra of one argument is
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpace` with a polynomial time
bound and a linear space bound. The machine is {lit}`machine`, whose symbols
and states are relabeled by {lit}`relabel` over {lit}`Fin 2` and an initial
segment of the naturals, as the definition requires; the run is the one
{lit}`machine_emits` names, whose step count {lit}`time` bounds and whose
heads stay within {lit}`bound` of the origin.

The time bound is {lit}`time` read through
{name}`Geb.SizeBounded.IsPolyBounded`; the space bound is the cell count an
emission visits, {lit}`tapes` tapes of {lit}`bound` cells and two more each, which is linear
in the input length because {lit}`bound` is the length or a constant of the
expression.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its statement
mentions {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, which depends on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main statements

* {lit}`isPolyBounded_time` — the machine's step count is bounded by a
  polynomial in the input length.
* {lit}`computableInTimeAndSpace_sem` — every unary expression's meaning is
  computable in polynomial time and linear space.

# References

* {cite}`Mazzanti2016`

# Tags

Turing machine, polynomial time, linear space, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open Geb.SizeBounded (SOf nsiConst IsPolyBounded isPolyBounded_add isPolyBounded_mul
  isPolyBounded_const isPolyBounded_id isPolyBounded_max isPolyBounded_shift nsi_sem)

public section

/-- The machine's step count is polynomially bounded in the input length. -/
theorem isPolyBounded_time (e : SOf 1) : IsPolyBounded (time e) :=
  isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 3) isPolyBounded_id)
        (isPolyBounded_const 5))
      (isPolyBounded_shift _ (isPolyBounded_stepBound e.1.1)))
    (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2)
      (isPolyBounded_max isPolyBounded_id (isPolyBounded_const _))) (isPolyBounded_const 3))

/-- The meaning of a unary expression is computable by a multi-tape machine in
polynomial time and linear space: the machine reading of
{cite}`Mazzanti2016` Theorem 5.7, by the compiled program of the expression
rather than the paper's Theorem 5.3 encoding into a single recursion. -/
theorem computableInTimeAndSpace_sem (e : SOf 1) :
    ∃ c d : ℕ, ComputableInTimeAndSpace (fun w ↦ e.sem ![w])
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (n + 1)) := by
  obtain ⟨c₁, d, hd⟩ := isPolyBounded_time e
  refine ⟨max c₁ (tapes e * (nsiConst e.1.1 + 2)), d, tapes e, 2, FinEnum.card (State e), bitEmb,
    relabel (machine e) FinEnum.equiv, fun w ↦ ?_⟩
  obtain ⟨cfg', t', ht', h⟩ := machine_emits e w
  refine ⟨t', ?_, (relabel (machine e) FinEnum.equiv).spaceUsed
    ((relabel (machine e) FinEnum.equiv).initCfg (w.map bitEmb)) t', ?_, ?_, ?_, rfl⟩
  · have hlen : (e.sem ![w]).length ≤ bound e w.length :=
      nsi_sem e ![w] w.length fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact Nat.le_refl _
    refine le_trans (le_trans ht' ?_)
      (le_trans (hd w.length) (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))
    unfold time
    omega
  · have hlin : bound e w.length + 2 ≤ (nsiConst e.1.1 + 2) * (w.length + 1) := by
      have hw : w.length ≤ (nsiConst e.1.1 + 2) * w.length := Nat.le_mul_of_pos_left _ (by omega)
      unfold bound
      rw [Nat.mul_succ]
      generalize (nsiConst e.1.1 + 2) * w.length = m at hw ⊢
      omega
    rw [initCfg_relabel, spaceUsed_relabel]
    refine le_trans h.spaceUsed_le (le_trans (Nat.mul_le_mul_left _ hlin) ?_)
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
  · rw [initCfg_relabel, configs_relabel, h.configs_eq]
    exact congrArg (Option.map _) h.halted
  · rw [initCfg_relabel, outputString_relabel, h.output]

end

end Geb.SizeBounded.Machine
