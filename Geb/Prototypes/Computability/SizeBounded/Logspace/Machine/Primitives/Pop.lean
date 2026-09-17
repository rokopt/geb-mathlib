/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Write
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.ReadBit

set_option doc.verso true in
/-!
# Popping and pushing a bit

Two primitives move one bit at the head of a register. {lit}`pop i j` peels
the head bit of register {lit}`i` into register {lit}`j`: it empties
{lit}`j`, walks {lit}`i`'s head to the blank after its word and one cell
back onto the head bit, moves that bit to {lit}`j` by
{name}`Geb.SizeBounded.Logspace.Machine.popStep`, and parks {lit}`i`. On an
empty {lit}`i` the walk stops at cell {lit}`0`, the step back reaches cell
{lit}`-1`, the pop step reads a blank and returns the head to cell {lit}`0`,
and {lit}`j` is left empty. {lit}`push c i` prepends the bit {lit}`c` to
register {lit}`i`: it walks to the blank after the word, writes {lit}`c`
there and parks. Each is a sequence of phase machines, and each transforms
the register valuation by {name}`Function.update`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`pop` — move the head bit of one register into another.
* {lit}`push` — prepend a bit to a register.

# Main statements

* {lit}`pop_transforms`, {lit}`push_transforms` — the contract of each
  primitive, naming its transformer and its step bound.

# Tags

Turing machine, register, stack, program
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Move the head bit of register {lit}`i` into register {lit}`j`: clear
{lit}`j`, walk {lit}`i` to its end and one cell back, pop, park {lit}`i`. -/
@[expose] def pop {k : ℕ} (i j : Fin k) :=
  seq (clear j) (seq (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i))))

/-- Prepend {lit}`c` to register {lit}`i`: walk to its end, write, park. -/
@[expose] def push {k : ℕ} (c : Bool) (i : Fin k) :=
  seq (walkEnd i) (seq (writeBit c i) (returnTape i))

/-- {name}`pop` transforms the valuation by moving the head bit of {lit}`i`,
when there is one, into {lit}`j`, in {lit}`4 * B + 12` steps. -/
theorem pop_transforms {k : ℕ} (i j : Fin k) (hij : i ≠ j) (B : ℕ) :
    Transforms (pop i j)
      (fun σ ↦ Function.update (Function.update σ j (σ i).head?.toList) i (σ i).tail)
      (4 * B + 12) B := by
  intro _ cfg σ hq hpark hσ hB _
  have hBi : (σ i).length ≤ B := hB i
  have hBj : (σ j).length ≤ B := hB j
  have hi := hσ i
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have hselfi : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from (hpark i).symm, Function.update_eq_self]
  have hbnd : ∀ (a : ℤ), -1 ≤ a → a ≤ B → ∀ l,
      -1 ≤ Function.update cfg.workTapePos i a l ∧ Function.update cfg.workTapePos i a l ≤ B :=
    fun a ha haB l ↦ update_workTapePos_bounds i hpos a ha haB l
  have r₁ := clear_runsTo j { cfg with state := some (clear j).q₀ } rfl (σ j) (hσ j) (hpark j)
    B hBj hpos
  rw [hself] at r₁
  have hi' : Function.update cfg.workTapes j (tapeOf []) i = tapeOf (σ i) := by
    rw [Function.update_of_ne hij, hi]
  change ∃ t ≤ 4 * B + 12, RunsTo (pop i j) cfg
    (after cfg (Function.update (Function.update σ j (σ i).head?.toList) i (σ i).tail)) t B
  rcases hsi : σ i with _ | ⟨c, r⟩
  · rw [hsi] at hi hi' hBi
    have r₂ := walkEnd_runsTo i
      { cfg with
        state := some (walkEnd i).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) }
      rfl [] hi' (hpark i) B hBi hpos
    rw [List.length_nil, Nat.cast_zero, hselfi] at r₂
    have r₃ := moveLeft_runsTo i
      { cfg with
        state := some (moveLeft i).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) }
      rfl B hpos (by change (0 : ℤ) ≤ cfg.workTapePos i; rw [hpark i])
    rw [hpark i, show (0 : ℤ) - 1 = -1 by omega] at r₃
    have r₄ := popStep_runsTo_nil i j
      { cfg with
        state := some (popStep i j).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i (-1) }
      rfl hi'
      (by change Function.update cfg.workTapePos i (-1) i = -1
          rw [Function.update_self])
      B (hbnd (-1) (by omega) (by omega))
    rw [Function.update_idem, hselfi] at r₄
    have r₅ := returnTape_runsTo i
      { cfg with
        state := some (returnTape i).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) }
      rfl [] hi' 0 (hpark i) (le_refl _) (by omega) B hpos
    rw [hselfi, show ((0 : ℤ) + 2).toNat = 2 by omega] at r₅
    have h₄₅ := r₄.seq r₅
    rw [← liftL_start (popStep i j) (returnTape i)
      { cfg with
        state := some (seq (popStep i j) (returnTape i)).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i (-1) } rfl] at h₄₅
    have h₃₄₅ := r₃.seq h₄₅
    rw [← liftL_start (moveLeft i) (seq (popStep i j) (returnTape i))
      { cfg with
        state := some (seq (moveLeft i) (seq (popStep i j) (returnTape i))).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₃₄₅
    have h₂₃₄₅ := r₂.seq h₃₄₅
    rw [← liftL_start (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))
      { cfg with
        state := some (seq (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃₄₅
    have hall := r₁.seq h₂₃₄₅
    rw [← liftL_start (clear j)
      (seq (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))) cfg hq] at hall
    change ∃ t ≤ 4 * B + 12, RunsTo (pop i j) cfg
      (after cfg (Function.update (Function.update σ j []) i [])) t B
    rw [show after cfg (Function.update (Function.update σ j []) i []) =
        liftR (liftR (liftR (liftR { cfg with
          state := none
          workTapes := Function.update cfg.workTapes j (tapeOf []) }))) from ?_]
    · exact ⟨_, by omega, hall⟩
    · apply Cfg.ext
      · rfl
      · rfl
      · funext l
        change tapeOf (Function.update (Function.update σ j []) i [] l) =
          Function.update cfg.workTapes j (tapeOf []) l
        by_cases hli : l = i
        · rw [hli, Function.update_self, Function.update_of_ne hij, hi]
        · rw [Function.update_of_ne hli]
          by_cases hl : l = j
          · rw [hl, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
      · rfl
      · rfl
  · rw [hsi] at hi hi' hBi
    rw [List.length_cons] at hBi
    have r₂ := walkEnd_runsTo i
      { cfg with
        state := some (walkEnd i).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) }
      rfl (c :: r) hi' (hpark i) B (by rw [List.length_cons]; exact hBi) hpos
    rw [List.length_cons] at r₂
    have r₃ := moveLeft_runsTo i
      { cfg with
        state := some (moveLeft i).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i ((r.length + 1 : ℕ) : ℤ) }
      rfl B (hbnd _ (by omega) (by omega))
      (by change (0 : ℤ) ≤ Function.update cfg.workTapePos i ((r.length + 1 : ℕ) : ℤ) i
          rw [Function.update_self]
          omega)
    simp only [Function.update_self, Function.update_idem] at r₃
    rw [show (((r.length + 1 : ℕ) : ℤ) - 1) = (r.length : ℤ) by omega] at r₃
    have r₄ := popStep_runsTo_cons i j hij
      { cfg with
        state := some (popStep i j).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i (r.length : ℤ) }
      rfl c r hi'
      (by change Function.update cfg.workTapePos i (r.length : ℤ) i = (r.length : ℤ)
          rw [Function.update_self])
      (by change Function.update cfg.workTapes j (tapeOf []) j = tapeOf []
          rw [Function.update_self])
      (by change Function.update cfg.workTapePos i (r.length : ℤ) j = 0
          rw [Function.update_of_ne hij.symm, hpark j])
      B (hbnd _ (by omega) (by omega))
    have htapes : Function.update (Function.update (Function.update cfg.workTapes j (tapeOf []))
        i (tapeOf r)) j (tapeOf [c]) =
        Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) := by
      rw [Function.update_comm hij.symm, Function.update_idem]
    rw [htapes] at r₄
    have r₅ := returnTape_runsTo i
      { cfg with
        state := some (returnTape i).q₀
        workTapes := Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c])
        workTapePos := Function.update cfg.workTapePos i (r.length : ℤ) }
      rfl r
      (by change Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) i =
            tapeOf r
          rw [Function.update_of_ne hij, Function.update_self])
      (r.length : ℤ)
      (by change Function.update cfg.workTapePos i (r.length : ℤ) i = (r.length : ℤ)
          rw [Function.update_self])
      (by omega) (le_refl _) B (hbnd _ (by omega) (by omega))
    rw [Function.update_idem, hselfi,
      show ((r.length : ℤ) + 2).toNat = r.length + 2 by omega] at r₅
    have h₄₅ := r₄.seq r₅
    rw [← liftL_start (popStep i j) (returnTape i)
      { cfg with
        state := some (seq (popStep i j) (returnTape i)).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i (r.length : ℤ) } rfl] at h₄₅
    have h₃₄₅ := r₃.seq h₄₅
    rw [← liftL_start (moveLeft i) (seq (popStep i j) (returnTape i))
      { cfg with
        state := some (seq (moveLeft i) (seq (popStep i j) (returnTape i))).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i ((r.length + 1 : ℕ) : ℤ) } rfl]
      at h₃₄₅
    have h₂₃₄₅ := r₂.seq h₃₄₅
    rw [← liftL_start (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))
      { cfg with
        state := some (seq (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))).q₀
        workTapes := Function.update cfg.workTapes j (tapeOf []) } rfl] at h₂₃₄₅
    have hall := r₁.seq h₂₃₄₅
    rw [← liftL_start (clear j)
      (seq (walkEnd i) (seq (moveLeft i) (seq (popStep i j) (returnTape i)))) cfg hq] at hall
    change ∃ t ≤ 4 * B + 12, RunsTo (pop i j) cfg
      (after cfg (Function.update (Function.update σ j [c]) i r)) t B
    rw [show after cfg (Function.update (Function.update σ j [c]) i r) =
        liftR (liftR (liftR (liftR { cfg with
          state := none
          workTapes :=
            Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) })))
      from ?_]
    · exact ⟨_, by omega, hall⟩
    · apply Cfg.ext
      · rfl
      · rfl
      · funext l
        change tapeOf (Function.update (Function.update σ j [c]) i r l) =
          Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) l
        by_cases hli : l = i
        · rw [hli, Function.update_self, Function.update_of_ne hij, Function.update_self]
        · rw [Function.update_of_ne hli]
          by_cases hl : l = j
          · rw [hl, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hl, Function.update_of_ne hl, Function.update_of_ne hli,
              hσ l]
      · rfl
      · rfl

/-- {name}`push` transforms the valuation by prepending {lit}`c` to {lit}`i`,
in {lit}`2 * B + 6` steps. The bound {lit}`(c :: σ i).length ≤ B` is the
contract's assumption on the transformed valuation. -/
theorem push_transforms {k : ℕ} (c : Bool) (i : Fin k) (B : ℕ) :
    Transforms (push c i) (fun σ ↦ Function.update σ i (c :: σ i)) (2 * B + 6) B := by
  intro _ cfg σ hq hpark hσ hB hFB
  have hBi : (σ i).length ≤ B := hB i
  have hcB : (σ i).length + 1 ≤ B := by
    have h : (Function.update σ i (c :: σ i) i).length ≤ B := hFB i
    rwa [Function.update_self, List.length_cons] at h
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hselfi : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from (hpark i).symm, Function.update_eq_self]
  have hbnd : ∀ l, -1 ≤ Function.update cfg.workTapePos i ((σ i).length : ℤ) l ∧
      Function.update cfg.workTapePos i ((σ i).length : ℤ) l ≤ B :=
    fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l
  have r₁ := walkEnd_runsTo i { cfg with state := some (walkEnd i).q₀ } rfl (σ i) (hσ i)
    (hpark i) B hBi hpos
  have r₂ := writeBit_runsTo c i
    { cfg with
      state := some (writeBit c i).q₀
      workTapePos := Function.update cfg.workTapePos i ((σ i).length : ℤ) }
    rfl (σ i) (hσ i)
    (by change Function.update cfg.workTapePos i ((σ i).length : ℤ) i = ((σ i).length : ℤ)
        rw [Function.update_self])
    B hbnd
  have r₃ := returnTape_runsTo i
    { cfg with
      state := some (returnTape i).q₀
      workTapes := Function.update cfg.workTapes i (tapeOf (c :: σ i))
      workTapePos := Function.update cfg.workTapePos i ((σ i).length : ℤ) }
    rfl (c :: σ i)
    (by change Function.update cfg.workTapes i (tapeOf (c :: σ i)) i = tapeOf (c :: σ i)
        rw [Function.update_self])
    ((σ i).length : ℤ)
    (by change Function.update cfg.workTapePos i ((σ i).length : ℤ) i = ((σ i).length : ℤ)
        rw [Function.update_self])
    (by omega) (by rw [List.length_cons]; omega) B hbnd
  rw [Function.update_idem, hselfi,
    show (((σ i).length : ℤ) + 2).toNat = (σ i).length + 2 from by omega] at r₃
  have h₂₃ := r₂.seq r₃
  rw [← liftL_start (writeBit c i) (returnTape i)
    { cfg with
      state := some (seq (writeBit c i) (returnTape i)).q₀
      workTapePos := Function.update cfg.workTapePos i ((σ i).length : ℤ) } rfl] at h₂₃
  have hall := r₁.seq h₂₃
  rw [← liftL_start (walkEnd i) (seq (writeBit c i) (returnTape i)) cfg hq] at hall
  rw [show after cfg (Function.update σ i (c :: σ i)) =
      liftR (liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (c :: σ i)) }) from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ i (c :: σ i) l) =
        Function.update cfg.workTapes i (tapeOf (c :: σ i)) l
      by_cases hl : l = i
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl
    · rfl

end

end Geb.SizeBounded.Logspace.Machine
