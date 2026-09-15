/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Walk
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The reversing copy

One primitive of the calculus copies the reverse of the word held by one
register onto another. {lit}`copyRev i j` empties the destination, walks the
source's head to the blank after its word and one cell back onto the word's
last cell, sweeps the word leftwards onto the destination, and parks the
destination's head; the source's head is parked by the sweep itself. It is a
sequence of phase machines, and it transforms the register valuation by a
{name}`Function.update` at {name}`List.reverse`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`copyRev` — copy the reverse of one register onto another.

# Main statements

* {lit}`copyRev_transforms` — the contract of the primitive, naming its
  transformer and its step bound.

# Tags

Turing machine, register, copying, reversal, program
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Copy the reverse of register {lit}`i` into register {lit}`j`: clear
{lit}`j`, walk {lit}`i` to its end and one back, copy leftwards, park
{lit}`j`. -/
@[expose] def copyRev {k : ℕ} (i j : Fin k) :=
  seq (clear j) (seq (walkEnd i) (seq (moveLeft i) (seq (revWalk i j) (returnTape j))))

/-- {name}`copyRev` transforms the valuation by setting {lit}`j` to the
reverse of {lit}`i`, in {lit}`5 * B + 12` steps. -/
theorem copyRev_transforms {k : ℕ} (i j : Fin k) (hij : i ≠ j) (B : ℕ) :
    Transforms (copyRev i j) (fun σ ↦ Function.update σ j (σ i).reverse) (5 * B + 12) B := by
  intro _ cfg σ hq hpark hσ hB _
  have hBi : (σ i).length ≤ B := hB i
  have hBj : (σ j).length ≤ B := hB j
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have hselfi : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from (hpark i).symm, Function.update_eq_self]
  have hmv : Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) i
        (Function.update cfg.workTapePos i ((σ i).length : ℤ) i - 1) =
      Function.update cfg.workTapePos i (((σ i).length : ℤ) - 1) := by
    rw [Function.update_self, Function.update_idem]
  have r₁ := clear_runsTo j { cfg with state := some (clear j).q₀ } rfl (σ j) (hσ j) (hpark j)
    B hBj hpos
  rw [hself] at r₁
  have r₂ := walkEnd_runsTo i
    { cfg with
      state := some (walkEnd i).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) }
    rfl (σ i)
    (by change Function.update cfg.workTapes j (tapeOf []) i = tapeOf (σ i)
        rw [Function.update_of_ne hij]
        exact hσ i)
    (hpark i) B hBi hpos
  have r₃ := moveLeft_runsTo i
    { cfg with
      state := some (moveLeft i).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf [])
      workTapePos := Function.update cfg.workTapePos i ((σ i).length : ℤ) }
    rfl B
    (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
    (by change (0 : ℤ) ≤ Function.update cfg.workTapePos i ((σ i).length : ℤ) i
        rw [Function.update_self]
        omega)
  rw [hmv] at r₃
  have r₄ := revWalk_runsTo i j hij
    { cfg with
      state := some (revWalk i j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf [])
      workTapePos := Function.update cfg.workTapePos i (((σ i).length : ℤ) - 1) }
    rfl (σ i)
    (by change Function.update cfg.workTapes j (tapeOf []) i = tapeOf (σ i)
        rw [Function.update_of_ne hij]
        exact hσ i)
    (by change Function.update cfg.workTapes j (tapeOf []) j = tapeOf []
        rw [Function.update_self])
    (by change Function.update cfg.workTapePos i (((σ i).length : ℤ) - 1) i =
          ((σ i).length : ℤ) - 1
        rw [Function.update_self])
    (by change Function.update cfg.workTapePos i (((σ i).length : ℤ) - 1) j = 0
        rw [Function.update_of_ne (Ne.symm hij)]
        exact hpark j)
    B hBi (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, Function.update_idem, hselfi] at r₄
  have r₅ := returnTape_runsTo j
    { cfg with
      state := some (returnTape j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (σ i).reverse)
      workTapePos := Function.update cfg.workTapePos j ((σ i).length : ℤ) }
    rfl (σ i).reverse
    (by change Function.update cfg.workTapes j (tapeOf (σ i).reverse) j = tapeOf (σ i).reverse
        rw [Function.update_self])
    ((σ i).length : ℤ)
    (by change Function.update cfg.workTapePos j ((σ i).length : ℤ) j = ((σ i).length : ℤ)
        rw [Function.update_self])
    (by omega) (by rw [List.length_reverse]) B
    (fun l ↦ update_workTapePos_bounds j hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself,
    show (((σ i).length : ℤ) + 2).toNat = (σ i).length + 2 from by omega] at r₅
  have h₄₅ := r₄.seq r₅
  rw [← liftL_start (revWalk i j) (returnTape j)
    { cfg with
      state := some (seq (revWalk i j) (returnTape j)).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf [])
      workTapePos := Function.update cfg.workTapePos i (((σ i).length : ℤ) - 1) } rfl] at h₄₅
  have h₃₄₅ := r₃.seq h₄₅
  rw [← liftL_start (moveLeft i) (seq (revWalk i j) (returnTape j))
    { cfg with
      state := some (seq (moveLeft i) (seq (revWalk i j) (returnTape j))).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf [])
      workTapePos := Function.update cfg.workTapePos i ((σ i).length : ℤ) } rfl] at h₃₄₅
  have h₂₃₄₅ := r₂.seq h₃₄₅
  rw [← liftL_start (walkEnd i) (seq (moveLeft i) (seq (revWalk i j) (returnTape j)))
    { cfg with
      state := some (seq (walkEnd i) (seq (moveLeft i) (seq (revWalk i j) (returnTape j)))).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃₄₅
  have hall := r₁.seq h₂₃₄₅
  rw [← liftL_start (clear j)
    (seq (walkEnd i) (seq (moveLeft i) (seq (revWalk i j) (returnTape j)))) cfg hq] at hall
  rw [show after cfg (Function.update σ j (σ i).reverse) =
      liftR (liftR (liftR (liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf (σ i).reverse) }))) from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ j (σ i).reverse l) =
        Function.update cfg.workTapes j (tapeOf (σ i).reverse) l
      by_cases hl : l = j
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl

end

end Geb.SizeBounded.Machine
