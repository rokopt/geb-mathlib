/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.InputMove

set_option doc.verso true in
/-!
# Seeking the input head by a counter

{lit}`seekLeft S` moves the input head left as many cells as the counter in
register {lit}`S` holds, consuming the counter: while {lit}`S` is nonempty,
one step left and one decrement. It is the loop
{name}`Geb.SizeBounded.Logspace.Machine.whileNonblank` at the probe {lit}`S`
over the body {lit}`seq inBack (dec S)`, and its run is read off
{name}`Geb.SizeBounded.Machine.RunsTo.whileNonblank` over the family of
configurations after each iteration, the head one cell further left and the
counter one less.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`seekLeft` — the seek.
* {lit}`SeekState` — its state type.

# Main statements

* {lit}`seekLeft_runsTo` — from a parked configuration whose counter holds
  {lit}`l` and whose input head is at least {lit}`l` cells in, the seek runs
  to the configuration with the head {lit}`l` cells further left and the
  counter empty, within {lit}`l * (2 * B + 8) + 1` steps.

# Tags

Turing machine, input head, counter, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The state type of {lit}`seekLeft`. -/
abbrev SeekState : Type := Unit ⊕ (Unit ⊕ (Fin 3 ⊕ (Unit ⊕ Unit)))

/-- Move the input head left as many cells as the counter in {lit}`S` holds,
consuming the counter. -/
@[expose] def seekLeft {k : ℕ} (S : Fin k) : MultiTapeTM k Bool SeekState :=
  whileNonblank (some S) (seq inBack (dec S))

/-- The run of the seek: from a parked configuration in its initial state
holding {lit}`σ` with the counter {lit}`l` in {lit}`S` and the input head at
least {lit}`l` cells in, to the halted configuration with the head {lit}`l`
cells further left, {lit}`S` empty and every other tape as before, within
{lit}`l * (2 * B + 8) + 1` steps. -/
theorem seekLeft_runsTo {k : ℕ} {input : List Bool} (S : Fin k)
    (cfg : Cfg k Bool SeekState input) (hq : cfg.state = some (seekLeft S).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg) (l : ℕ)
    (hS : σ S = counterWord l) (hlp : l ≤ cfg.inputPos.val) (B : ℕ) (hB : Bounded σ B) :
    ∃ t ≤ l * (2 * B + 8) + 1,
      RunsTo (seekLeft S) cfg
        { cfg with
          state := none
          inputPos := ⟨cfg.inputPos.val - l, by have := cfg.inputPos.isLt; omega⟩
          workTapes := fun i ↦ tapeOf (Function.update σ S [] i) } t B := by
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have hlen : ∀ j, (counterWord j).length ≤ (counterWord l).length → (counterWord j).length ≤ B :=
    fun j hj ↦ hj.trans (hS ▸ hB S)
  have hbnd : ∀ j, j ≤ l → Bounded (Function.update σ S (counterWord j)) B :=
    fun j hj ↦ hB.update (hlen j (length_counterWord_le_of_le hj))
  -- The configurations after each iteration, at the body's state type.
  let c : ℕ → Cfg k Bool (Unit ⊕ (Fin 3 ⊕ (Unit ⊕ Unit))) input := fun j ↦
    ⟨none, ⟨cfg.inputPos.val - j, by have := cfg.inputPos.isLt; omega⟩,
      fun i ↦ tapeOf (Function.update σ S (counterWord (l - j)) i), cfg.workTapePos, cfg.output⟩
  have hprobe : ∀ j, probeOf (some S) (c j) = tapeOf (counterWord (l - j)) 0 := by
    intro j
    change tapeOf (Function.update σ S (counterWord (l - j)) S) (cfg.workTapePos S) = _
    rw [Function.update_self, hpark S]
  obtain ⟨t, ht, r⟩ := RunsTo.whileNonblank (some S) (seq inBack (dec S)) B (2 * B + 7) l c
    (fun j hj ↦ by
      rw [hprobe]
      intro h
      have := (counterWord_eq_nil_iff _).mp ((tapeOf_zero_eq_none_iff _).mp h)
      omega)
    (by
      rw [hprobe, Nat.sub_self]
      exact (tapeOf_zero_eq_none_iff _).mpr ((counterWord_eq_nil_iff 0).mpr rfl))
    (fun j hj ↦ by
      -- One iteration: the step left, then the decrement.
      have r₁ := inBack_runsTo_of_pos (k := k) { c j with state := some () } rfl
        (by change cfg.inputPos.val - j ≠ 0; omega) B (fun i ↦ hpB i)
      have hl : l - j = (l - (j + 1)) + 1 := by omega
      have r₂ := dec_transforms S B (input := input)
        { c j with
          state := some (dec S).q₀
          inputPos := ⟨cfg.inputPos.val - j - 1, by have := cfg.inputPos.isLt; omega⟩ }
        (Function.update σ S (counterWord (l - j))) rfl hpark (fun i ↦ rfl) (hbnd _ (by omega))
        (by
          dsimp only
          rw [Function.update_self, hl, decL_counterWord_succ, Function.update_idem]
          exact hbnd _ (by omega))
      obtain ⟨t, ht, r₂⟩ := r₂
      refine ⟨1 + t, by omega, ?_⟩
      refine (RunsTo.seqStart (cfg := { c j with state := some (seq inBack (dec S)).q₀ }) rfl r₁
        r₂).congr_target ?_
      apply Cfg.ext
      · rfl
      · apply Fin.ext
        change cfg.inputPos.val - j - 1 = cfg.inputPos.val - (j + 1)
        omega
      · funext i
        change tapeOf (Function.update (Function.update σ S (counterWord (l - j))) S
          (decL (Function.update σ S (counterWord (l - j)) S).reverse).reverse i) =
          tapeOf (Function.update σ S (counterWord (l - (j + 1))) i)
        rw [Function.update_self, hl, decL_counterWord_succ, Function.update_idem]
      · rfl
      · rfl)
    (fun i ↦ by change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B; exact hpB i)
  have h8 : 2 * B + 7 + 1 = 2 * B + 8 := by omega
  rw [h8] at ht
  refine ⟨t, ht, ?_⟩
  have hcfg : { c 0 with state := some (Sum.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · apply Fin.ext
      change cfg.inputPos.val - 0 = cfg.inputPos.val
      omega
    · funext i
      change tapeOf (Function.update σ S (counterWord (l - 0)) i) = cfg.workTapes i
      rw [Nat.sub_zero, ← hS, Function.update_eq_self, hσ i]
    · rfl
    · rfl
  rw [hcfg] at r
  refine r.congr_target ?_
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    change tapeOf (Function.update σ S (counterWord (l - l)) i) = _
    rw [Nat.sub_self]
    rfl
  · rfl
  · rfl

end

end Geb.SizeBounded.Logspace.Machine
