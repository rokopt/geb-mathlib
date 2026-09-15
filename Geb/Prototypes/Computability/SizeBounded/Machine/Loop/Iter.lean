/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Basic
import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Phases
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true in
/-!
# One iteration of the recursion loop

One iteration of {name}`Geb.SizeBounded.Machine.caseLoop` composes its three
control phases with one run of a body. From the seek state, parked, with the
register {lit}`R` holding a word of head bit {lit}`c` and tail {lit}`r`, the
seek, back and return phases peel {lit}`c` off and enter the body for
{lit}`c` in its initial state, parked, holding the valuation with {lit}`R`
set to {lit}`r`. The body runs under its contract and halts, and its halting
step lifts to the seek state, where the next iteration begins.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statement mentions {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`caseLoop_iter` — the reach of one iteration, naming the
  configuration it ends in and the step count.

# Tags

Turing machine, loop, recursion, register
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The loop's one iteration: from the seek state, parked, holding a
valuation whose {lit}`R` is {lit}`c :: r`, the control peels {lit}`c`, runs the
body for {lit}`c` from its initial state on the valuation with {lit}`R` set
to {lit}`r`, and returns to the seek state, parked, holding the body's
transformed valuation. -/
theorem caseLoop_iter {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (FF FT : (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ)
    (hF : Transforms bodyF FF T B) (hT : Transforms bodyT FT T B)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (σ : Fin k → List Bool) (c : Bool) (r : List Bool) (hR : σ R = c :: r)
    (hpark : Parked cfg) (hσ : Holds cfg σ) (hB : Bounded σ B)
    (hb : Bounded ((if c then FT else FF) (Function.update σ R r)) B) :
    ∃ t ≤ T + 2 * r.length + 6,
      Reaches (caseLoop R bodyF bodyT) cfg
        { after cfg ((if c then FT else FF) (Function.update σ R r)) with
          state := some (.inl 0) } t B := by
  have hσR : cfg.workTapes R = tapeOf (c :: r) := by rw [hσ R, hR]
  have hlen : r.length + 1 ≤ B := by
    have h := hB R
    rw [hR, List.length_cons] at h
    exact h
  have hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ (B : ℤ) := by
    intro j
    rw [hpark j]
    constructor <;> omega
  have hpos₁ := update_workTapePos_bounds R hpos (r.length : ℤ) (by omega) (by omega)
  have hpos₂ := update_workTapePos_bounds R hpos₁ ((r.length : ℤ) - 1) (by omega) (by omega)
  have hseek := caseLoop_seek R bodyF bodyT cfg hq c r hσR (hpark R) B hlen hpos
  have hback := caseLoop_back R bodyF bodyT
    { cfg with
      state := some (.inl 1)
      workTapePos := Function.update cfg.workTapePos R (r.length : ℤ) }
    rfl c r hσR (Function.update_self ..) B hpos₁
  have hchain := (hseek.trans hback).trans
    (caseLoop_ret R bodyF bodyT _ c rfl r (Function.update_self ..)
      (Function.update_self ..) B hpos₂)
  have hupd : Bounded (Function.update σ R r) B := by
    intro i
    by_cases hi : i = R
    · subst hi
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hi]
      exact hB i
  have htapes : ∀ i, Function.update cfg.workTapes R (tapeOf r) i =
      tapeOf (Function.update σ R r i) := by
    intro i
    by_cases hi : i = R
    · subst hi
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact hσ i
  have hzero : ∀ j, Function.update (Function.update
        (Function.update cfg.workTapePos R (r.length : ℤ)) R ((r.length : ℤ) - 1)) R 0 j =
      cfg.workTapePos j := by
    intro j
    by_cases hj : j = R
    · subst hj
      rw [Function.update_self]
      exact (hpark _).symm
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
  cases c with
  | false =>
    obtain ⟨t, ht, hrun⟩ := hF
      ({ state := some bodyF.q₀
         inputPos := cfg.inputPos
         workTapes := fun i ↦ tapeOf (Function.update σ R r i)
         workTapePos := cfg.workTapePos
         output := cfg.output } : Cfg k Bool SF input)
      (Function.update σ R r) rfl hpark (fun _ ↦ rfl) hupd hb
    refine ⟨r.length + 2 + 1 + (r.length + 1) + t, by omega, hchain.trans ?_⟩
    have hl := hrun.toReaches.liftBodyF R bodyT
    rw [liftBodyF_halt _ (after_state _ _)] at hl
    rw [funext htapes, funext hzero]
    exact hl
  | true =>
    obtain ⟨t, ht, hrun⟩ := hT
      ({ state := some bodyT.q₀
         inputPos := cfg.inputPos
         workTapes := fun i ↦ tapeOf (Function.update σ R r i)
         workTapePos := cfg.workTapePos
         output := cfg.output } : Cfg k Bool ST input)
      (Function.update σ R r) rfl hpark (fun _ ↦ rfl) hupd hb
    refine ⟨r.length + 2 + 1 + (r.length + 1) + t, by omega, hchain.trans ?_⟩
    have hl := hrun.toReaches.liftBodyT R bodyF
    rw [liftBodyT_halt _ (after_state _ _)] at hl
    rw [funext htapes, funext hzero]
    exact hl

end

end Geb.SizeBounded.Machine
