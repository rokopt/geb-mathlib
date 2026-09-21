/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Subtraction
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Contract

set_option doc.verso true in
/-!
# Machine transitions for digitwise subtraction

The subtraction carry has three possible values, represented by a blank, zero,
or one cell. A single transition reads two digits and the carry, then replaces
the carry and result cells without moving any head.

## Main definitions

* {lit}`subBitStep` performs one digit of signed-carry subtraction.

## Main statements

* {lit}`subBitStep_transformsIn` verifies the transition and preservation of all other tapes.

## Implementation notes

This is the arithmetic transition, not yet a complete subtraction machine.
It must be combined with virtual digit readers and a scan locating the output sentinel.
The machine contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, subtraction, finite carry, logarithmic space
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace.Machine

public section

/-- Replacing the only possible occupied cell replaces its optional singleton word. -/
theorem tapeOf_update_zero {w : List Bool} (hw : w.length ≤ 1) (b : Option Bool) :
    Function.update (tapeOf w) 0 b = tapeOf b.toList := by
  funext z
  by_cases hz : z = 0
  · subst z
    cases b <;> simp [tapeOf]
  · rw [Function.update_of_ne hz]
    by_cases hneg : z < 0
    · rw [tapeOf_neg _ _ hneg, tapeOf_neg _ _ hneg]
    · rw [tapeOf_of_le _ _ (by omega), tapeOf_of_le _ _ ?_]
      have := Option.length_toList_le (o := b)
      omega

/-- One arithmetic transition. The ports are minuend digit, subtrahend digit, carry, result. -/
@[expose] def subBitStep {k : ℕ} (r : Fin 4 → Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    let v := subBit ((work (r 0)).getD false) ((work (r 1)).getD false) (work (r 2))
    { inputTape := 0
      workTapes := fun i ↦
        if i = r 2 then (some v.1, 0)
        else if i = r 3 then (some (some v.2), 0) else (none, 0)
      output := none
      state := none }

/-- Update the optional carry and result words with one finite arithmetic transition. -/
@[expose] def subBitVal {k : ℕ} (r : Fin 4 → Fin k) (σ : Fin k → List Bool) :=
  let v := subBit ((tapeOf (σ (r 0)) 0).getD false)
    ((tapeOf (σ (r 1)) 0).getD false) (tapeOf (σ (r 2)) 0)
  Function.update (Function.update σ (r 2) v.1.toList) (r 3) [v.2]

/-- The arithmetic transition writes at most one cell on each output port
and preserves all heads. -/
theorem subBitStep_transformsIn {k : ℕ} (r : Fin 4 → Fin k) (hr : Function.Injective r)
    (B : ℕ → ℕ) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (subBitStep r)
      (fun _ σ ↦ (σ (r 2)).length ≤ 1 ∧ (σ (r 3)).length ≤ 1)
      (fun _ σ ↦ subBitVal r σ) (fun _ ↦ 1) B := by
  intro input cfg σ hq hpark _ hσ hp hB
  have hw (i : Fin k) : cfg.workTapeSymbols i = tapeOf (σ i) 0 := by
    change cfg.workTapes i (cfg.workTapePos i) = _
    rw [hpark i, hσ i]
  have hs : (subBitStep r).step cfg = after cfg (subBitVal r σ) := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext i
      by_cases hi2 : i = r 2
      · subst i
        simp only [subBitStep, ite_true, after, subBitVal,
          Function.update_of_ne (hr.ne (by decide : (2 : Fin 4) ≠ 3)), Function.update_self]
        rw [hpark, hσ, hw, hw, hw, tapeOf_update_zero hp.1]
      · by_cases hi3 : i = r 3
        · subst i
          simp only [subBitStep, hi2, ite_false, ite_true, after, subBitVal,
            Function.update_self]
          rw [hpark, hσ, hw, hw, hw, tapeOf_update_zero hp.2]
          rfl
        · simp [subBitStep, hi2, hi3, after, subBitVal, hσ i]
    · funext i
      simp only [subBitStep, after]
      split_ifs <;> simp
    · simp [subBitStep, after]
  refine ⟨(hB.update (Option.length_toList_le.trans (hB1 _))).update (hB1 _),
    1, le_rfl, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩⟩
  · intro s hs'
    have : s = 0 := by omega
    simpa only [this, runFrom_zero, hq] using Option.some_ne_none ()
  · simpa only [runFrom_succ_eq_step', runFrom_zero] using hs
  · intro s hs' i
    have hpos : -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
      rw [hpark i]
      constructor <;> omega
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · exact hpos
    · simpa only [runFrom_succ_eq_step', runFrom_zero, hs, after] using hpos
  · simp only [outputString_succ, runFrom_zero, outputSymbol, hq]
    rfl

end

end Geb.Oitavem.Machine
