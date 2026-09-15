/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Sbs

set_option doc.verso true

/-!
# The size-bounded successor

One primitive of the calculus prepends a bit to the word held by one
register when the result is no longer than the word held by a second.
{lit}`sbs b x y j` empties the destination, sweeps the source's word onto it
with the bit prepended exactly when the second register is long enough, and
parks all three heads. It is a sequence of phase machines, and it transforms
the register valuation by a {name}`Function.update` at
{name}`Geb.SizeBounded.sbsSem`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`sbs` — the size-bounded successor of one register into another.

# Main statements

* {lit}`sbs_transforms` — the contract of the primitive, naming its
  transformer and its step bound.

# Tags

Turing machine, register, successor, program
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The size-bounded successor into register {lit}`j`: clear, walk, park all
three. -/
@[expose] def sbs {k : ℕ} (b : Bool) (x y j : Fin k) :=
  seq (clear j) (seq (sbsWalk b x y j) (seq (returnTape x) (seq (returnTape y) (returnTape j))))

/-- {name}`sbs` transforms the valuation by setting {lit}`j` to the
size-bounded successor of {lit}`x` bounded by {lit}`y`, in
{lit}`7 * B + 16` steps. -/
theorem sbs_transforms {k : ℕ} (b : Bool) (x y j : Fin k) (hxy : x ≠ y) (hxj : x ≠ j)
    (hyj : y ≠ j) (B : ℕ) :
    Transforms (sbs b x y j) (fun σ ↦ Function.update σ j (sbsSem b (σ x) (σ y)))
      (7 * B + 16) B := by
  intro _ cfg σ hq hpark hσ hB hFB
  have hBx : (σ x).length ≤ B := hB x
  have hBy : (σ y).length ≤ B := hB y
  have hBj : (σ j).length ≤ B := hB j
  have hwB : (sbsSem b (σ x) (σ y)).length ≤ B := by
    have h : (Function.update σ j (sbsSem b (σ x) (σ y)) j).length ≤ B := hFB j
    rwa [Function.update_self] at h
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have hret₃ : Function.update (Function.update (Function.update (Function.update
        cfg.workTapePos x ((σ x).length : ℤ)) y ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
        ((sbsSem b (σ x) (σ y)).length : ℤ)) x 0 =
      Function.update (Function.update cfg.workTapePos y
        ((min (σ x).length (σ y).length : ℕ) : ℤ)) j ((sbsSem b (σ x) (σ y)).length : ℤ) := by
    funext l
    by_cases hlx : l = x
    · rw [hlx, Function.update_self, Function.update_of_ne hxj, Function.update_of_ne hxy,
        hpark x]
    · rw [Function.update_of_ne hlx]
      by_cases hlj : l = j
      · rw [hlj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hlj, Function.update_of_ne hlj]
        by_cases hly : l = y
        · rw [hly, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hly, Function.update_of_ne hly, Function.update_of_ne hlx]
  have hret₄ : Function.update (Function.update (Function.update cfg.workTapePos y
        ((min (σ x).length (σ y).length : ℕ) : ℤ)) j ((sbsSem b (σ x) (σ y)).length : ℤ)) y 0 =
      Function.update cfg.workTapePos j ((sbsSem b (σ x) (σ y)).length : ℤ) := by
    funext l
    by_cases hly : l = y
    · rw [hly, Function.update_self, Function.update_of_ne hyj, hpark y]
    · rw [Function.update_of_ne hly]
      by_cases hlj : l = j
      · rw [hlj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hlj, Function.update_of_ne hlj, Function.update_of_ne hly]
  have r₁ := clear_runsTo j { cfg with state := some (clear j).q₀ } rfl (σ j) (hσ j) (hpark j)
    B hBj hpos
  rw [hself] at r₁
  have r₂ := sbsWalk_runsTo b x y j hxy hxj hyj
    { cfg with
      state := some (sbsWalk b x y j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) }
    rfl (σ x) (σ y)
    (by change Function.update cfg.workTapes j (tapeOf []) x = tapeOf (σ x)
        rw [Function.update_of_ne hxj]
        exact hσ x)
    (by change Function.update cfg.workTapes j (tapeOf []) y = tapeOf (σ y)
        rw [Function.update_of_ne hyj]
        exact hσ y)
    (by change Function.update cfg.workTapes j (tapeOf []) j = tapeOf []
        rw [Function.update_self])
    (hpark x) (hpark y) (hpark j) B hBx hBy hpos
  rw [Function.update_idem] at r₂
  have r₃ := returnTape_runsTo x
    { cfg with
      state := some (returnTape x).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y)))
      workTapePos := Function.update (Function.update (Function.update cfg.workTapePos x
        ((σ x).length : ℤ)) y ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
        ((sbsSem b (σ x) (σ y)).length : ℤ) }
    rfl (σ x)
    (by change Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y))) x = tapeOf (σ x)
        rw [Function.update_of_ne hxj]
        exact hσ x)
    ((σ x).length : ℤ)
    (by change Function.update (Function.update (Function.update cfg.workTapePos x
          ((σ x).length : ℤ)) y ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
          ((sbsSem b (σ x) (σ y)).length : ℤ) x = ((σ x).length : ℤ)
        rw [Function.update_of_ne hxj, Function.update_of_ne hxy, Function.update_self])
    (by omega) (by omega) B
    (fun l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds y
        (fun n ↦ update_workTapePos_bounds x hpos _ (by omega) (by omega) n) _ (by omega)
        (by omega) m) _ (by omega) (by omega) l)
  rw [hret₃, show (((σ x).length : ℤ) + 2).toNat = (σ x).length + 2 from by omega] at r₃
  have r₄ := returnTape_runsTo y
    { cfg with
      state := some (returnTape y).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y)))
      workTapePos := Function.update (Function.update cfg.workTapePos y
        ((min (σ x).length (σ y).length : ℕ) : ℤ)) j ((sbsSem b (σ x) (σ y)).length : ℤ) }
    rfl (σ y)
    (by change Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y))) y = tapeOf (σ y)
        rw [Function.update_of_ne hyj]
        exact hσ y)
    ((min (σ x).length (σ y).length : ℕ) : ℤ)
    (by change Function.update (Function.update cfg.workTapePos y
          ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
          ((sbsSem b (σ x) (σ y)).length : ℤ) y = ((min (σ x).length (σ y).length : ℕ) : ℤ)
        rw [Function.update_of_ne hyj, Function.update_self])
    (by omega) (by omega) B
    (fun l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds y hpos _ (by omega) (by omega) m) _ (by omega)
      (by omega) l)
  rw [hret₄, show (((min (σ x).length (σ y).length : ℕ) : ℤ) + 2).toNat =
    min (σ x).length (σ y).length + 2 from by omega] at r₄
  have r₅ := returnTape_runsTo j
    { cfg with
      state := some (returnTape j).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y)))
      workTapePos := Function.update cfg.workTapePos j ((sbsSem b (σ x) (σ y)).length : ℤ) }
    rfl (sbsSem b (σ x) (σ y))
    (by change Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y))) j =
          tapeOf (sbsSem b (σ x) (σ y))
        rw [Function.update_self])
    ((sbsSem b (σ x) (σ y)).length : ℤ)
    (by change Function.update cfg.workTapePos j ((sbsSem b (σ x) (σ y)).length : ℤ) j =
          ((sbsSem b (σ x) (σ y)).length : ℤ)
        rw [Function.update_self])
    (by omega) (by omega) B
    (fun l ↦ update_workTapePos_bounds j hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself,
    show (((sbsSem b (σ x) (σ y)).length : ℤ) + 2).toNat =
      (sbsSem b (σ x) (σ y)).length + 2 from by omega] at r₅
  have h₄₅ := r₄.seq r₅
  rw [← liftL_start (returnTape y) (returnTape j)
    { cfg with
      state := some (seq (returnTape y) (returnTape j)).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y)))
      workTapePos := Function.update (Function.update cfg.workTapePos y
        ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
        ((sbsSem b (σ x) (σ y)).length : ℤ) } rfl] at h₄₅
  have h₃₄₅ := r₃.seq h₄₅
  rw [← liftL_start (returnTape x) (seq (returnTape y) (returnTape j))
    { cfg with
      state := some (seq (returnTape x) (seq (returnTape y) (returnTape j))).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y)))
      workTapePos := Function.update (Function.update (Function.update cfg.workTapePos x
        ((σ x).length : ℤ)) y ((min (σ x).length (σ y).length : ℕ) : ℤ)) j
        ((sbsSem b (σ x) (σ y)).length : ℤ) } rfl] at h₃₄₅
  have h₂₃₄₅ := r₂.seq h₃₄₅
  rw [← liftL_start (sbsWalk b x y j) (seq (returnTape x) (seq (returnTape y) (returnTape j)))
    { cfg with
      state := some (seq (sbsWalk b x y j)
        (seq (returnTape x) (seq (returnTape y) (returnTape j)))).q₀
      workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃₄₅
  have hall := r₁.seq h₂₃₄₅
  rw [← liftL_start (clear j)
    (seq (sbsWalk b x y j) (seq (returnTape x) (seq (returnTape y) (returnTape j))))
    cfg hq] at hall
  rw [show after cfg (Function.update σ j (sbsSem b (σ x) (σ y))) =
      liftR (liftR (liftR (liftR { cfg with
        state := none
        workTapes :=
          Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y))) }))) from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ j (sbsSem b (σ x) (σ y)) l) =
        Function.update cfg.workTapes j (tapeOf (sbsSem b (σ x) (σ y))) l
      by_cases hl : l = j
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl

end

end Geb.SizeBounded.Machine
