/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Rep
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Seek
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.ReadBit
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Const

set_option doc.verso true in
/-!
# Reading the input bit at an end segment's head

{lit}`readInput C S F` writes into the flag register {lit}`F` the bit of the
input at the head of its end segment of length one more than the counter in
{lit}`C` holds, {name}`Geb.SizeBounded.Logspace.bitAt` at that count: it copies
the counter into the scratch register {lit}`S`, walks the input head to the
blank past the input, seeks left by the scratch counter and one cell more,
empties the flag, writes the symbol under the head into it, and walks the
head home. Under the contract {name}`Geb.SizeBounded.Logspace.Machine.TransformsIn`
its precondition is that {lit}`C` holds a counter below the input's length,
and its transformer empties {lit}`S` and sets {lit}`F` to that bit.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`readInput` — the primitive.
* {lit}`readInputTime` — its step bound at a length bound and an input length.

# Main statements

* {lit}`readInput_transformsIn` — the primitive's contract.

# Tags

Turing machine, input tape, counter, flag, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Read the input bit at the head of the end segment one longer than the
counter in {lit}`C` into the flag {lit}`F`, through the scratch counter
{lit}`S`. -/
@[expose] def readInput {k : ℕ} (C S F : Fin k) :=
  seq (copy C S) (seq inStepRight (seq inRight (seq (seekLeft S) (seq inBack
    (seq (const [] F) (seq (readBit F) inHome))))))

/-- The step bound of {name}`readInput` at a length bound {lit}`B` and an input
length {lit}`n`: the copy, the walk to the end, the seek, the clear, and the
walk home. -/
@[expose] def readInputTime (B n : ℕ) : ℕ :=
  (5 * B + 12) + 1 + (n + 1) + (n * (2 * B + 8) + 1) + 1 + (4 * B + 9) + 1 + (n + 1)

/-- The contract of {name}`readInput`: when {lit}`C` holds a counter {lit}`l`
below the input's length, the primitive empties {lit}`S` and sets {lit}`F` to
the bit {name}`Geb.SizeBounded.Logspace.bitAt` the input at {lit}`l`, within
{name}`readInputTime`, provided the length bound admits a one-bit word. -/
theorem readInput_transformsIn {k : ℕ} (C S F : Fin k) (hCS : C ≠ S) (hCF : C ≠ F) (hSF : S ≠ F)
    (B : ℕ → ℕ) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (readInput C S F)
      (fun input σ ↦ ∃ l, σ C = counterWord l ∧ l < input.length)
      (fun input σ ↦
        Function.update (Function.update σ S []) F [bitAt input (counterValue (σ C))])
      (fun n ↦ readInputTime (B n) n) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨l, hC, hl⟩ := hpre
  have hn := cfg.inputPos.isLt
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    intro i
    rw [hpark i]
    constructor <;> omega
  -- The valuations along the way.
  have hB1' : Bounded (Function.update σ S (σ C)) (B input.length) := hB.update (hB C)
  have hB2 : Bounded (Function.update (Function.update σ S (σ C)) S []) (B input.length) :=
    hB1'.update (Nat.zero_le _)
  have hB3 : Bounded (Function.update (Function.update (Function.update σ S (σ C)) S []) F [])
      (B input.length) := hB2.update (Nat.zero_le _)
  refine ⟨?_, ?_⟩
  · exact (hB.update (Nat.zero_le _)).update (by rw [List.length_singleton]; exact hB1 _)
  -- The copy.
  obtain ⟨t₁, ht₁, r₁⟩ := copy_transforms C S hCS (B input.length) (input := input)
    { cfg with state := some (copy C S).q₀ } σ rfl hpark hσ hB hB1'
  -- The step onto the first symbol.
  have r₂ := inStepRight_runsTo (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some () } rfl (by change cfg.inputPos.val < _; omega) (B input.length) hpB
  -- The walk to the blank past the input.
  have r₃ := inRight_runsTo (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ } rfl (by change cfg.inputPos.val + 1 = 1; omega)
    (B input.length) hpB
  -- The seek by the scratch counter.
  obtain ⟨t₄, ht₄, r₄⟩ := seekLeft_runsTo (input := input) S
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some (seekLeft S).q₀
      inputPos := ⟨input.length + 1, by omega⟩ } rfl (Function.update σ S (σ C)) (fun i ↦ rfl)
    hpark l (by rw [Function.update_self, hC]) (by change l ≤ input.length + 1; omega)
    (B input.length) hB1'
  -- The step back onto the bit.
  have r₅ := inBack_runsTo_of_pos (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨input.length + 1 - l, by omega⟩
      workTapes := fun i ↦ tapeOf (Function.update (Function.update σ S (σ C)) S [] i) } rfl
    (by change input.length + 1 - l ≠ 0; omega) (B input.length) hpB
  -- The clear of the flag.
  obtain ⟨t₆, ht₆, r₆⟩ := const_transforms [] F (B input.length) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some (const [] F).q₀
      inputPos := ⟨input.length + 1 - l - 1, by omega⟩
      workTapes := fun i ↦ tapeOf (Function.update (Function.update σ S (σ C)) S [] i) }
    (Function.update (Function.update σ S (σ C)) S []) rfl hpark (fun i ↦ rfl) hB2 hB3
  -- The read of the bit.
  have hsym : ∀ (cfg' : Cfg k Bool Unit input), cfg'.inputPos.val = input.length + 1 - l - 1 →
      cfg'.inputSymbol = some (bitAt input l) := by
    intro cfg' hp'
    rw [inputSymbolInner (input.length - 1 - l) (by omega) (by omega), bitAt_eq_getElem input hl]
  have r₇ := readBit_runsTo (input := input) F
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨input.length + 1 - l - 1, by omega⟩
      workTapes := fun i ↦ tapeOf (Function.update (Function.update (Function.update σ S (σ C))
        S []) F [] i) } rfl (by change tapeOf _ = _; rw [Function.update_self]) (hpark F)
    (B input.length) hpB
  rw [hsym _ rfl] at r₇
  -- The walk home.
  have r₈ := inHome_runsTo (k := k) (input := input)
    { after { cfg with state := some (copy C S).q₀ } (Function.update σ S (σ C)) with
      state := some ()
      inputPos := ⟨input.length + 1 - l - 1, by omega⟩
      workTapes := Function.update (fun i ↦ tapeOf (Function.update (Function.update
        (Function.update σ S (σ C)) S []) F [] i)) F (tapeOf (some (bitAt input l)).toList) } rfl
    (by change input.length + 1 - l - 1 ≤ input.length; omega) (B input.length) hpB
  refine ⟨t₁ + (1 + ((input.length + 1) + (t₄ + (1 + (t₆ +
    (1 + (input.length + 1 - l - 1 + 1))))))), ?_, ?_⟩
  · have := Nat.mul_le_mul_right (2 * B input.length + 8) (Nat.le_of_lt hl)
    change _ ≤ readInputTime (B input.length) input.length
    unfold readInputTime
    omega
  · refine (RunsTo.seqStart hq r₁ (RunsTo.seqStart rfl r₂ (RunsTo.seqStart rfl r₃
      (RunsTo.seqStart rfl r₄ (RunsTo.seqStart rfl r₅ (RunsTo.seqStart rfl r₆
        (RunsTo.seqStart rfl r₇ r₈))))))).congr_target ?_
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      exact hpos.symm
    · funext i
      change Function.update (fun i ↦ tapeOf (Function.update (Function.update
        (Function.update σ S (σ C)) S []) F [] i)) F (tapeOf [bitAt input l]) i =
        tapeOf (Function.update (Function.update σ S []) F [bitAt input (counterValue (σ C))] i)
      rw [hC, counterValue_counterWord, Function.update_idem]
      by_cases hi : i = F
      · subst hi
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi]
    · rfl
    · rfl

end

end Geb.SizeBounded.Logspace.Machine
