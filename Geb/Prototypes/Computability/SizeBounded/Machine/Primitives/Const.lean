/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Write

set_option doc.verso true

/-!
# Writing a constant

One primitive of the calculus writes a fixed word into a register, whatever
the register held. {lit}`const w j` empties the register, sweeps {lit}`w`
onto it and parks the head. It is a sequence of phase machines, and it
transforms the register valuation by a {name}`Function.update`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`const` — write a fixed word into a register.

# Main statements

* {lit}`const_transforms` — the contract of the primitive, naming its
  transformer and its step bound.

# Tags

Turing machine, register, constant, program
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Write the constant {lit}`w` into register {lit}`j`: clear, write, park. -/
@[expose] def const {k : ℕ} (w : List Bool) (j : Fin k) :=
  seq (clear j) (seq (constWalk w j) (returnTape j))

/-- {name}`const` transforms the valuation by setting {lit}`j` to {lit}`w`, in
{lit}`4 * B + 9` steps. The bound {lit}`w.length ≤ B` is the contract's
assumption on the transformed valuation. -/
theorem const_transforms {k : ℕ} (w : List Bool) (j : Fin k) (B : ℕ) :
    Transforms (const w j) (fun σ ↦ Function.update σ j w) (4 * B + 9) B := by
  intro _ cfg σ hq hpark hσ hB hFB
  have hBj : (σ j).length ≤ B := hB j
  have hwB : w.length ≤ B := by
    have h : (Function.update σ j w j).length ≤ B := hFB j
    rwa [Function.update_self] at h
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have hbnd : ∀ l, -1 ≤ Function.update cfg.workTapePos j (w.length : ℤ) l ∧
      Function.update cfg.workTapePos j (w.length : ℤ) l ≤ B :=
    fun l ↦ update_workTapePos_bounds j hpos _ (by omega) (by omega) l
  have r₁ := clear_runsTo j { cfg with state := some (clear j).q₀ } rfl (σ j) (hσ j) (hpark j)
    B hBj hpos
  rw [hself] at r₁
  have r₂ := constWalk_runsTo w j
    { cfg with
      state := some (constWalk w j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) }
    rfl
    (by change Function.update cfg.workTapes j (tapeOf []) j = tapeOf []
        rw [Function.update_self])
    (hpark j) B hwB hpos
  rw [Function.update_idem] at r₂
  have r₃ := returnTape_runsTo j
    { cfg with
      state := some (returnTape j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf w)
      workTapePos := Function.update cfg.workTapePos j (w.length : ℤ) }
    rfl w
    (by change Function.update cfg.workTapes j (tapeOf w) j = tapeOf w
        rw [Function.update_self])
    ((w.length : ℤ))
    (by change Function.update cfg.workTapePos j (w.length : ℤ) j = (w.length : ℤ)
        rw [Function.update_self])
    (by omega) (by omega) B hbnd
  rw [Function.update_idem, hself,
    show ((w.length : ℤ) + 2).toNat = w.length + 2 from by omega] at r₃
  have h₂₃ := r₂.seq r₃
  rw [← liftL_start (constWalk w j) (returnTape j)
    { cfg with
      state := some (seq (constWalk w j) (returnTape j)).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃
  have hall := r₁.seq h₂₃
  rw [← liftL_start (clear j) (seq (constWalk w j) (returnTape j)) cfg hq] at hall
  rw [show after cfg (Function.update σ j w) =
      liftR (liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w) }) from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ j w l) =
        Function.update cfg.workTapes j (tapeOf w) l
      by_cases hl : l = j
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl

end

end Geb.SizeBounded.Machine
