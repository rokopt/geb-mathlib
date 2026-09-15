/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Walk

set_option doc.verso true in
/-!
# Copying

One primitive of the calculus moves a word between registers. {lit}`copy i j`
empties the destination, sweeps the source's word onto it and parks both
heads. It is a sequence of phase machines, and it transforms the register
valuation by a {name}`Function.update`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`copy` — copy one register onto another.

# Main statements

* {lit}`copy_transforms` — the contract of the primitive, naming its
  transformer and its step bound.

# Tags

Turing machine, register, copying, program
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Copy register {lit}`i` into register {lit}`j`: clear {lit}`j`, copy, park
both. -/
@[expose] def copy {k : ℕ} (i j : Fin k) :=
  seq (clear j) (seq (copyWalk i j) (seq (returnTape i) (returnTape j)))

/-- {name}`copy` transforms the valuation by copying {lit}`i` to {lit}`j`, in
{lit}`5 * B + 12` steps. -/
theorem copy_transforms {k : ℕ} (i j : Fin k) (hij : i ≠ j) (B : ℕ) :
    Transforms (copy i j) (fun σ ↦ Function.update σ j (σ i)) (5 * B + 12) B := by
  intro _ cfg σ hq hpark hσ hB _
  have hBi : (σ i).length ≤ B := hB i
  have hBj : (σ j).length ≤ B := hB j
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have hret : Function.update (Function.update (Function.update cfg.workTapePos i
        ((σ i).length : ℤ)) j ((σ i).length : ℤ)) i 0 =
      Function.update cfg.workTapePos j ((σ i).length : ℤ) := by
    funext l
    by_cases hli : l = i
    · rw [hli, Function.update_self, Function.update_of_ne hij, hpark i]
    · rw [Function.update_of_ne hli]
      by_cases hlj : l = j
      · rw [hlj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hlj, Function.update_of_ne hlj, Function.update_of_ne hli]
  have hbnd : ∀ l, -1 ≤ Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) j
        ((σ i).length : ℤ) l ∧
      Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) j
        ((σ i).length : ℤ) l ≤ B :=
    fun l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) m) _
      (by omega) (by omega) l
  have r₁ := clear_runsTo j { cfg with state := some (clear j).q₀ } rfl (σ j) (hσ j) (hpark j)
    B hBj hpos
  rw [hself] at r₁
  have r₂ := copyWalk_runsTo i j hij
    { cfg with
      state := some (copyWalk i j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) }
    rfl (σ i)
    (by change Function.update cfg.workTapes j (tapeOf []) i = tapeOf (σ i)
        rw [Function.update_of_ne hij]
        exact hσ i)
    (by change Function.update cfg.workTapes j (tapeOf []) j = tapeOf []
        rw [Function.update_self])
    (hpark i) (hpark j) B hBi hpos
  rw [Function.update_idem] at r₂
  have r₃ := returnTape_runsTo i
    { cfg with
      state := some (returnTape i).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (σ i))
      workTapePos := Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) j
        ((σ i).length : ℤ) }
    rfl (σ i)
    (by change Function.update cfg.workTapes j (tapeOf (σ i)) i = tapeOf (σ i)
        rw [Function.update_of_ne hij]
        exact hσ i)
    ((σ i).length : ℤ)
    (by change Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) j
          ((σ i).length : ℤ) i = ((σ i).length : ℤ)
        rw [Function.update_of_ne hij, Function.update_self])
    (by omega) (by omega) B hbnd
  rw [hret, show (((σ i).length : ℤ) + 2).toNat = (σ i).length + 2 from by omega] at r₃
  have r₄ := returnTape_runsTo j
    { cfg with
      state := some (returnTape j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (σ i))
      workTapePos := Function.update cfg.workTapePos j ((σ i).length : ℤ) }
    rfl (σ i)
    (by change Function.update cfg.workTapes j (tapeOf (σ i)) j = tapeOf (σ i)
        rw [Function.update_self])
    ((σ i).length : ℤ)
    (by change Function.update cfg.workTapePos j ((σ i).length : ℤ) j = ((σ i).length : ℤ)
        rw [Function.update_self])
    (by omega) (by omega) B
    (fun l ↦ update_workTapePos_bounds j hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself,
    show (((σ i).length : ℤ) + 2).toNat = (σ i).length + 2 from by omega] at r₄
  have h₃₄ := r₃.seq r₄
  rw [← liftL_start (returnTape i) (returnTape j)
    { cfg with
      state := some (seq (returnTape i) (returnTape j)).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (σ i))
      workTapePos := Function.update (Function.update cfg.workTapePos i ((σ i).length : ℤ)) j
        ((σ i).length : ℤ) } rfl] at h₃₄
  have h₂₃₄ := r₂.seq h₃₄
  rw [← liftL_start (copyWalk i j) (seq (returnTape i) (returnTape j))
    { cfg with
      state := some (seq (copyWalk i j) (seq (returnTape i) (returnTape j))).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃₄
  have hall := r₁.seq h₂₃₄
  rw [← liftL_start (clear j) (seq (copyWalk i j) (seq (returnTape i) (returnTape j)))
    cfg hq] at hall
  rw [show after cfg (Function.update σ j (σ i)) =
      liftR (liftR (liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf (σ i)) })) from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ j (σ i) l) =
        Function.update cfg.workTapes j (tapeOf (σ i)) l
      by_cases hl : l = j
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl
    · rfl

end

end Geb.SizeBounded.Machine
