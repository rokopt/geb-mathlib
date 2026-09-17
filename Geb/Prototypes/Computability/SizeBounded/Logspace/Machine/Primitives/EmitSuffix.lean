/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Seek
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.EmitRight
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Mathlib.Data.List.DropRight

set_option doc.verso true in
/-!
# Emitting an end segment of the input

{lit}`emitSuffix C S` emits the end segment of the input whose length the
counter in {lit}`C` holds: it copies the counter into the scratch register
{lit}`S`, walks the input head to the blank past the input, seeks left by the
scratch counter, and emits every symbol from there to the end. It is the
last phase of the machine of an expression, the end segment part of the
output's representation; the word part is emitted by
{lit}`writer`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`emitSuffix` — the primitive.
* {lit}`emitSuffixTime` — its step bound.

# Main statements

* {lit}`emitSuffix_emits` — the emission of the primitive from the head at the
  blank before the input.

# Tags

Turing machine, output, end segment, counter, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Emit the end segment of the input of the length the counter in {lit}`C`
holds, through the scratch counter {lit}`S`. -/
@[expose] def emitSuffix {k : ℕ} (C S : Fin k) :=
  seq (copy C S) (seq inStepRight (seq inRight (seq (seekLeft S) emitRight)))

/-- The step bound of {name}`emitSuffix` at a length bound {lit}`B` and an
input length {lit}`n`. -/
@[expose] def emitSuffixTime (B n : ℕ) : ℕ :=
  (5 * B + 12) + 1 + (n + 1) + (n * (2 * B + 8) + 1) + (n + 1)

/-- The emission of {name}`emitSuffix`: from a parked configuration in its
initial state holding {lit}`σ` with the counter {lit}`l` in {lit}`C`, at most
the input's length, and the input head at the blank before the input, the
primitive emits the last {lit}`l` symbols of the input and halts with the head
past the input and {lit}`S` empty, within {name}`emitSuffixTime`. -/
theorem emitSuffix_emits {k : ℕ} {input : List Bool} (C S : Fin k) (hCS : C ≠ S)
    (cfg : Cfg k Bool (StateOf (emitSuffix C S)) input) (hq : cfg.state = some (emitSuffix C S).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg) (hpos : cfg.inputPos.val = 0)
    (l : ℕ) (hC : σ C = counterWord l) (hl : l ≤ input.length) (B : ℕ) (hB : Bounded σ B) :
    ∃ t ≤ emitSuffixTime B input.length,
      Emits (emitSuffix C S) cfg
        { cfg with
          state := none
          inputPos := ⟨input.length + 1, by omega⟩
          workTapes := fun i ↦ tapeOf (Function.update (Function.update σ S (σ C)) S [] i)
          output := cfg.output ++ input.rtake l }
        (input.rtake l) t B := by
  have hn := cfg.inputPos.isLt
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have hB1 : Bounded (Function.update σ S (σ C)) B := hB.update (hB C)
  -- The copy.
  obtain ⟨t₁, ht₁, r₁⟩ := copy_transforms C S hCS B (input := input)
    { cfg with state := some (copy C S).q₀ } σ rfl hpark hσ hB hB1
  -- The step onto the first symbol and the walk to the end.
  have r₂ := inStepRight_runsTo (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some () } rfl (by change cfg.inputPos.val < _; omega) B hpB
  have r₃ := inRight_runsTo (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ } rfl (by change cfg.inputPos.val + 1 = 1; omega)
    B hpB
  -- The seek.
  obtain ⟨t₄, ht₄, r₄⟩ := seekLeft_runsTo (input := input) S
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some (seekLeft S).q₀
      inputPos := ⟨input.length + 1, by omega⟩ } rfl (Function.update σ S (σ C)) (fun i ↦ rfl)
    hpark l (by rw [Function.update_self, hC]) (by change l ≤ input.length + 1; omega) B hB1
  -- The emission.
  have r₅ := emitRight_emits (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨input.length + 1 - l, by omega⟩
      workTapes := fun i ↦ tapeOf (Function.update (Function.update σ S (σ C)) S [] i) } rfl
    (input.length + 1 - l) rfl (by omega) (by omega) B hpB
  have hdrop : input.drop (input.length + 1 - l - 1) = input.rtake l := by
    unfold List.rtake
    congr 1
    omega
  rw [hdrop] at r₅
  refine ⟨t₁ + (1 + ((input.length + 1) + (t₄ + (input.length + 2 - (input.length + 1 - l))))),
    ?_, ?_⟩
  · have := Nat.mul_le_mul_right (2 * B + 8) hl
    unfold emitSuffixTime
    omega
  · refine (RunsTo.seqStartEmits hq r₁ (RunsTo.seqStartEmits rfl r₂
      (RunsTo.seqStartEmits rfl r₃ (RunsTo.seqStartEmits rfl r₄ r₅)))).congr_target ?_
    apply Cfg.ext <;> rfl

end

end Geb.SizeBounded.Logspace.Machine
