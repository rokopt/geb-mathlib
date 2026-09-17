/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Inc
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.InputMove
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Const

set_option doc.verso true in
/-!
# Counting the input's length

{lit}`countInput C` writes the input's length into the counter register
{lit}`C`: it empties {lit}`C`, walks the input head from the first symbol to
the blank past the input incrementing {lit}`C` at each symbol, and walks the
head home. The walk is the loop
{name}`Geb.SizeBounded.Logspace.Machine.whileNonblank` at the input probe over
the body {lit}`seq (inc C) inStepRight`, and its run is read off
{name}`Geb.SizeBounded.Machine.RunsTo.whileNonblank` over the family of
configurations after each symbol. The primitive starts at the first symbol,
where {name}`Turing.Cfg.init` puts the head, and ends at the blank before the
input, where every program of the calculus starts.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`countInput` — the primitive.
* {lit}`CountBodyState` — the state type of its loop body.
* {lit}`countInputTime` — its step bound.

# Main statements

* {lit}`countInput_runsTo` — the run of the primitive from the first symbol.

# Tags

Turing machine, input tape, counter, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The state type of the loop body of {lit}`countInput`. -/
abbrev CountBodyState : Type := (Unit ⊕ (Unit ⊕ Unit)) ⊕ Unit

/-- Write the input's length into {lit}`C`, from the input head at the first
symbol, ending with the head at the blank before the input. -/
@[expose] def countInput {k : ℕ} (C : Fin k) :=
  seq (const [] C) (seq (whileNonblank none (seq (inc C) inStepRight)) (seq inBack inHome))

/-- The step bound of {name}`countInput` at a length bound {lit}`B` and an input
length {lit}`n`. -/
@[expose] def countInputTime (B n : ℕ) : ℕ :=
  (4 * B + 9) + (n * (2 * B + 6 + 1) + 1) + 1 + (n + 1)

/-- The run of {name}`countInput`: from a parked configuration in its initial
state holding {lit}`σ`, the input head at the first symbol, to the halted
configuration with the head at the blank before the input and {lit}`C` holding
the input's length, within {name}`countInputTime`, provided the length bound
admits that counter. -/
theorem countInput_runsTo {k : ℕ} {input : List Bool} (C : Fin k)
    (cfg : Cfg k Bool (StateOf (countInput C)) input) (hq : cfg.state = some (countInput C).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg) (hp : cfg.inputPos.val = 1)
    (B : ℕ) (hB : Bounded σ B) (hBn : Nat.size input.length ≤ B) :
    ∃ t ≤ countInputTime B input.length,
      RunsTo (countInput C) cfg
        { cfg with
          state := none
          inputPos := ⟨0, by omega⟩
          workTapes := fun i ↦ tapeOf (Function.update σ C (counterWord input.length) i) }
        t B := by
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have hbnd : ∀ j, j ≤ input.length → Bounded (Function.update σ C (counterWord j)) B :=
    fun j hj ↦ hB.update ((length_counterWord_le_of_le hj).trans
      ((length_counterWord _).le.trans hBn))
  -- The clear.
  obtain ⟨t₁, ht₁, r₁⟩ := const_transforms [] C B { cfg with state := some (const [] C).q₀ }
    σ rfl hpark hσ hB (hB.update (Nat.zero_le _))
  -- The configurations after each symbol, at the loop body's state type.
  let c : ℕ → Cfg k Bool CountBodyState input := fun j ↦
    ⟨none, ⟨min (1 + j) (input.length + 1), by omega⟩,
      fun i ↦ tapeOf (Function.update σ C (counterWord j) i), cfg.workTapePos, cfg.output⟩
  have hprobe : ∀ j, j ≤ input.length → probeOf none (c j) = input[j]? := by
    intro j hj
    change (c j).inputSymbol = _
    rcases Nat.lt_or_ge j input.length with h | h
    · rw [inputSymbolInner j (by change min (1 + j) (input.length + 1) = 1 + j; omega) h,
        List.getElem?_eq_getElem h]
    · have hj' : j = input.length := by omega
      subst hj'
      rw [List.getElem?_length]
      unfold Cfg.inputSymbol
      rw [dite_eq_right (by
          intro h0
          have := congrArg Fin.val h0
          change min (1 + input.length) (input.length + 1) = 0 at this
          omega),
        dite_eq_left (by
          change min (1 + input.length) (input.length + 1) = input.length + 1
          omega)]
  obtain ⟨t₂, ht₂, r₂⟩ := RunsTo.whileNonblank none (seq (inc C) inStepRight) B (2 * B + 6)
    input.length c
    (fun j hj ↦ by
      rw [hprobe j (by omega), List.getElem?_eq_getElem hj]
      exact Option.some_ne_none _)
    (by rw [hprobe _ (le_refl _), List.getElem?_length])
    (fun j hj ↦ by
      -- One iteration: the increment, then the step right.
      obtain ⟨t, ht, r⟩ := inc_transforms C B { c j with state := some (inc C).q₀ }
        (Function.update σ C (counterWord j)) rfl hpark (fun i ↦ rfl) (hbnd j (by omega))
        (by
          dsimp only
          rw [Function.update_self, incL_counterWord, Function.update_idem]
          exact hbnd (j + 1) hj)
      have r' := inStepRight_runsTo (k := k) (input := input)
        { after { c j with state := some (inc C).q₀ } (Function.update
          (Function.update σ C (counterWord j)) C
          (incL (Function.update σ C (counterWord j) C).reverse).reverse) with state := some () }
        rfl (by change min (1 + j) (input.length + 1) < input.length + 1; omega) B hpB
      refine ⟨t + 1, by omega, ?_⟩
      refine (RunsTo.seqStart (cfg := { c j with state := some (seq (inc C) inStepRight).q₀ })
        rfl r r').congr_target ?_
      apply Cfg.ext
      · rfl
      · apply Fin.ext
        change min (1 + j) (input.length + 1) + 1 = min (1 + (j + 1)) (input.length + 1)
        omega
      · funext i
        change tapeOf (Function.update (Function.update σ C (counterWord j)) C
          (incL (Function.update σ C (counterWord j) C).reverse).reverse i) =
          tapeOf (Function.update σ C (counterWord (j + 1)) i)
        rw [Function.update_self, incL_counterWord, Function.update_idem]
      · rfl
      · rfl)
    (fun i ↦ by change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B; exact hpB i)
  -- The step back and the walk home.
  have r₃ := inBack_runsTo_of_pos (k := k) (input := input)
    { c input.length with state := some () } rfl
    (by change min (1 + input.length) (input.length + 1) ≠ 0; omega) B hpB
  have r₄ := inHome_runsTo (k := k) (input := input)
    { c input.length with
      state := some ()
      inputPos := ⟨min (1 + input.length) (input.length + 1) - 1, by omega⟩ } rfl
    (by change min (1 + input.length) (input.length + 1) - 1 ≤ input.length; omega) B hpB
  refine ⟨t₁ + (t₂ + (1 + (min (1 + input.length) (input.length + 1) - 1 + 1))), ?_, ?_⟩
  · unfold countInputTime
    have : min (1 + input.length) (input.length + 1) = input.length + 1 := by omega
    omega
  · have hstart : ({ after { cfg with state := some (const [] C).q₀ } (Function.update σ C []) with
        state := some (whileNonblank none (seq (inc C) inStepRight)).q₀ } :
        Cfg k Bool (Unit ⊕ CountBodyState) input) = { c 0 with state := some (Sum.inl ()) } := by
      apply Cfg.ext
      · rfl
      · apply Fin.ext
        change cfg.inputPos.val = min (1 + 0) (input.length + 1)
        omega
      · rfl
      · rfl
      · rfl
    rw [← hstart] at r₂
    refine (RunsTo.seqStart hq r₁ (RunsTo.seqStart rfl r₂
      (RunsTo.seqStart rfl r₃ r₄))).congr_target ?_
    apply Cfg.ext <;> rfl

end

end Geb.SizeBounded.Logspace.Machine
