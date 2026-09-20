/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.While
public import Geb.Prototypes.Computability.Oitavem.Machine.CountOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.ReadOutput
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Count
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.Oitavem.Derived
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.EmitRight
import Mathlib.Tactic.Linarith
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Streaming repeated input

A counter controls repeated scans of the read-only input. Each scan writes its
symbols directly to the output and returns the input head home. In particular,
the word-square function can have quadratic output while using logarithmic work
space.

## Main definitions

* {lit}`repeatBody` emits the input once and decrements a counter.
* {lit}`repeatInput` repeats that scan, consuming the counter.
* {lit}`squareInput` squares the input while preserving caller registers.
* {lit}`squareMachine` first counts the input and then repeats it that many times.

## Main statements

* {lit}`repeatBody_emits` gives the exact effect of one scan.
* {lit}`repeatInput_emits` gives the full output and the time and space bounds.
* {lit}`computableInTimeAndSpace_squareWord` proves the machine-computability
  statement for the quadratic-output expression.
* {lit}`squareLength_runsTo` counts that generated output on two logarithmic tapes.
* {lit}`squareDigit_runsTo` reads a generated digit on three logarithmic tapes.
* {lit}`computableInTimeAndSpace_length_squareWord` computes numerical length after
  the square expression, with the result emitted in the algebra's encoding.

## Implementation notes

These machine statements inherit {lit}`Classical.choice` from CSLib's
configurations. This module is included in {lit}`GebMeta.classicalAllowedModules`.

## References

* {cite}`Oitavem2010`, Definition 3.1: string product and normal composition.

## Tags

Turing machine, streaming, word product, logarithmic space
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Emit the entire input, return its head home, and decrement the counter. -/
@[expose] def repeatBody {k : ℕ} (C : Fin k) :=
  seq inStepRight (seq emitRight (seq inBack (seq inHome (dec C))))

/-- A scan emits exactly the input and changes only the repetition counter. -/
theorem repeatBody_emits {k : ℕ} {input : List Bool} (C : Fin k)
    (cfg : Cfg k Bool (StateOf (repeatBody C)) input)
    (hq : cfg.state = some (repeatBody C).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg)
    (hp : cfg.inputPos.val = 0) (l B : ℕ) (hC : σ C = counterWord (l + 1))
    (hB : Bounded σ B) :
    ∃ t ≤ 2 * input.length + 2 * B + 10,
      Emits (repeatBody C) cfg
        { cfg with state := none
                   workTapes := fun i ↦ tapeOf (Function.update σ C (counterWord l) i)
                   output := cfg.output ++ input } input t B := by
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have r₁ := inStepRight_runsTo { cfg with state := some () } rfl
    (by change cfg.inputPos.val < input.length + 1; omega) B hpB
  have r₂ := emitRight_emits (input := input)
    { cfg with state := some (), inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ }
    rfl 1 (by change cfg.inputPos.val + 1 = 1; omega) (by omega) (by omega) B hpB
  simp only [Nat.sub_self, List.drop_zero] at r₂
  have r₃ := inBack_runsTo_of_pos (input := input)
    { cfg with state := some (), inputPos := ⟨input.length + 1, by omega⟩
               output := cfg.output ++ input }
    rfl (by change input.length + 1 ≠ 0; omega) B hpB
  have r₄ := inHome_runsTo (input := input)
    { cfg with state := some (), inputPos := ⟨input.length + 1 - 1, by omega⟩
               output := cfg.output ++ input }
    rfl (by change input.length + 1 - 1 ≤ input.length; omega) B hpB
  obtain ⟨t, ht, r₅⟩ := dec_transforms C B (input := input)
    { cfg with state := some (dec C).q₀, inputPos := ⟨0, by omega⟩
               output := cfg.output ++ input }
    σ rfl hpark hσ hB (by
      dsimp only
      rw [hC, decL_counterWord_succ]
      exact hB.update ((length_counterWord_le_of_le (Nat.le_succ l)).trans (hC ▸ hB C)))
  have r₄₅ := RunsTo.seqStart (P := inHome) (Q := dec C) (input := input)
    (cfg := { cfg with state := some (seq inHome (dec C)).q₀
                       inputPos := ⟨input.length + 1 - 1, by omega⟩
                       output := cfg.output ++ input }) rfl r₄ r₅
  have r₃₄₅ := RunsTo.seqStart (P := inBack) (Q := seq inHome (dec C)) (input := input)
    (cfg := { cfg with state := some (seq inBack (seq inHome (dec C))).q₀
                       inputPos := ⟨input.length + 1, by omega⟩
                       output := cfg.output ++ input }) rfl r₃ r₄₅
  have r₂₃₄₅ := r₂.seqEmits r₃₄₅.toEmits
  rw [List.append_nil] at r₂₃₄₅
  rw [← liftL_start emitRight (seq inBack (seq inHome (dec C)))
    { cfg with state := some (seq emitRight (seq inBack (seq inHome (dec C)))).q₀
               inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ } rfl] at r₂₃₄₅
  refine ⟨1 + (input.length + 2 - 1 + (1 + (input.length + 1 - 1 + 1 + t))),
    by omega, ?_⟩
  refine (RunsTo.seqStartEmits hq r₁ r₂₃₄₅).congr_target ?_
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    exact hp.symm
  · funext i
    change tapeOf (Function.update σ C (decL (σ C).reverse).reverse i) = _
    rw [hC, decL_counterWord_succ]
  · rfl
  · rfl

/-- Repeat the physical input as many times as the counter specifies. -/
@[expose] def repeatInput {k : ℕ} (C : Fin k) :=
  whileNonblank (some C) (repeatBody C)

/-- The repetition loop streams all copies, clears the counter, and returns
with the same head positions and all other registers preserved. -/
theorem repeatInput_emits {k : ℕ} {input : List Bool} (C : Fin k)
    (cfg : Cfg k Bool (StateOf (repeatInput C)) input)
    (hq : cfg.state = some (repeatInput C).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg)
    (hp : cfg.inputPos.val = 0) (l B : ℕ) (hC : σ C = counterWord l)
    (hB : Bounded σ B) :
    ∃ t ≤ l * (2 * input.length + 2 * B + 11) + 1,
      Emits (repeatInput C) cfg
        { cfg with state := none
                   workTapes := fun i ↦ tapeOf (Function.update σ C [] i)
                   output := cfg.output ++ (List.replicate l input).flatten }
        (List.replicate l input).flatten t B := by
  let c : ℕ → Cfg k Bool (StateOf (repeatBody C)) input := fun j ↦
    { cfg with state := none
               workTapes := fun i ↦ tapeOf (Function.update σ C (counterWord (l - j)) i)
               output := cfg.output ++ (List.replicate j input).flatten }
  have hprobe (j : ℕ) : probeOf (some C) (c j) = tapeOf (counterWord (l - j)) 0 := by
    change tapeOf (Function.update σ C (counterWord (l - j)) C) (cfg.workTapePos C) = _
    rw [Function.update_self, hpark C]
  obtain ⟨t, ht, h⟩ := arrives_whileNonblank (some C) (repeatBody C) B
    (2 * input.length + 2 * B + 10) l c
    (by
      intro j hj hzero
      rw [hprobe] at hzero
      have := (counterWord_eq_nil_iff _).mp ((tapeOf_zero_eq_none_iff _).mp hzero)
      omega)
    (by rw [hprobe, Nat.sub_self]; rfl)
    (by
      intro j hj
      have hl : l - j = (l - (j + 1)) + 1 := by omega
      obtain ⟨s, hs, h⟩ := repeatBody_emits C { c j with state := some (repeatBody C).q₀ }
        rfl (Function.update σ C (counterWord (l - j))) (fun _ ↦ rfl) hpark hp
        (l - (j + 1)) B (by rw [Function.update_self, hl])
        (hB.update ((length_counterWord_le_of_le (Nat.sub_le _ _)).trans (hC ▸ hB C)))
      refine ⟨s, hs, ?_⟩
      have heq : ({ c j with
          state := none
          workTapes := fun i ↦ tapeOf
            (Function.update (Function.update σ C (counterWord (l - j))) C
              (counterWord (l - (j + 1))) i)
          output := (c j).output ++ input } : Cfg k Bool (StateOf (repeatBody C)) input) =
          { c (j + 1) with state := none } := by
        apply Cfg.ext
        · rfl
        · rfl
        · simp only [Function.update_idem]; rfl
        · rfl
        · change cfg.output ++ (List.replicate j input).flatten ++ input =
            cfg.output ++ (List.replicate (j + 1) input).flatten
          rw [List.replicate_succ', List.flatten_append, List.flatten_singleton,
            List.append_assoc]
      exact heq ▸ h.toArrives)
    (by
      intro i
      change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B
      rw [hpark i]
      constructor <;> omega)
  have hstart : { c 0 with state := some (.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      change tapeOf (Function.update σ C (counterWord (l - 0)) i) = cfg.workTapes i
      rw [Nat.sub_zero, ← hC, Function.update_eq_self, hσ i]
    · rfl
    · simp [c]
  rw [hstart] at h
  refine ⟨t, by omega, ⟨?_, ?_, rfl⟩⟩
  · simpa only [repeatInput, c, Nat.sub_self, show counterWord 0 = [] from rfl] using h
  · change (whileNonblank (some C) (repeatBody C)).outputString cfg t = _
    apply List.append_cancel_left (as := cfg.output)
    rw [← runFrom_output, h.runFrom_eq]

/-- Square the physical input using one designated scratch counter. -/
@[expose] def squareInput {k : ℕ} (C : Fin k) := seq (countInput C) (repeatInput C)

/-- Squaring clears its scratch counter, parks the input head, and preserves all
caller registers and the previous output. The scratch counter may initially be dirty. -/
theorem squareInput_emits {k : ℕ} {input : List Bool} (C : Fin k)
    (cfg : Cfg k Bool (StateOf (squareInput C)) input)
    (hq : cfg.state = some (squareInput C).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg)
    (hp : cfg.inputPos.val = 1) (B : ℕ) (hB : Bounded σ B) (hn : input.length.size ≤ B) :
    ∃ t ≤ countInputTime B input.length +
        (input.length * (2 * input.length + 2 * B + 11) + 1),
      Emits (squareInput C) cfg
        { cfg with state := none
                   inputPos := ⟨0, by omega⟩
                   workTapes := fun i ↦ tapeOf (Function.update σ C [] i)
                   output := cfg.output ++ (List.replicate input.length input).flatten }
        (List.replicate input.length input).flatten t B := by
  obtain ⟨t₁, ht₁, h₁⟩ := countInput_runsTo C
    { cfg with state := some (countInput C).q₀ } rfl σ hσ hpark hp B hB hn
  obtain ⟨t₂, ht₂, h₂⟩ := repeatInput_emits C
    { cfg with state := some (repeatInput C).q₀
               inputPos := ⟨0, by omega⟩
               workTapes := fun i ↦ tapeOf (Function.update σ C (counterWord input.length) i) }
    rfl (Function.update σ C (counterWord input.length)) (fun _ ↦ rfl)
    hpark rfl input.length B (Function.update_self ..)
    (hB.update (by rwa [length_counterWord]))
  have h := RunsTo.seqStartEmits hq h₁ h₂
  simp only [Function.update_idem] at h
  exact ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, h⟩

/-- A one-work-tape machine for {name}`squareWord`. -/
@[expose] def squareMachine := squareInput (0 : Fin 1)

/-- The square machine halts with the quadratic output and visits at most a
logarithmic interval of its single work tape. -/
theorem squareMachine_emits (w : List Bool) :
    ∃ cfg' t,
      t ≤ countInputTime w.length.size w.length +
        (w.length * (2 * w.length + 2 * w.length.size + 11) + 1) ∧
      Emits squareMachine (squareMachine.initCfg w) cfg'
        (squareWord.eval ![w] Fin.elim0) t w.length.size := by
  obtain ⟨t, ht, h⟩ := squareInput_emits (0 : Fin 1) (squareMachine.initCfg w)
    rfl (fun _ ↦ []) (fun _ ↦ tapeOf_nil.symm) (by intro i; rfl) rfl w.length.size
    (by intro i; exact Nat.zero_le _) le_rfl
  exact ⟨_, t, ht, h⟩

/-- The quadratic-output Logs expression has simultaneous quadratic time and
logarithmic work space on a concrete one-work-tape transducer. -/
theorem computableInTimeAndSpace_squareWord :
    ComputableInTimeAndSpaceOfLength (fun w ↦ squareWord.eval ![w] Fin.elim0)
      (.refl _) (.refl _) (fun n ↦ 32 * (n + 1) ^ 2)
      (fun n ↦ 32 * (n.size + 1)) := by
  refine ⟨1, StateOf squareMachine, inferInstance, squareMachine, fun w ↦ ?_⟩
  obtain ⟨cfg', t, ht, h⟩ := squareMachine_emits w
  refine ⟨t, ?_, squareMachine.spaceUsed (squareMachine.initCfg w) t,
    ?_, ?_, ?_, rfl⟩
  · have hs := size_le_self w.length
    change t ≤ 32 * (w.length + 1) ^ 2
    apply ht.trans
    unfold countInputTime
    nlinarith [Nat.mul_le_mul_left w.length hs]
  · change squareMachine.spaceUsed (squareMachine.initCfg w) t ≤
      32 * (w.length.size + 1)
    exact h.spaceUsed_le.trans (by omega)
  · change (squareMachine.runFrom (squareMachine.initCfg w) t).state = none
    rw [h.runFrom_eq]
    exact h.halted
  · rw [initCfg_runFrom_output]
    exact h.output

private theorem size_square_add_one_le (n : ℕ) : (n * n + 1).size ≤ 2 * n.size + 1 := by
  apply Geb.BitTree.Counter.size_le_of_lt_pow
  rw [show 2 * n.size + 1 = n.size + n.size + 1 by omega, Nat.pow_succ, Nat.pow_add]
  have hp := Nat.two_pow_pos n.size
  have hn := Nat.mul_self_lt_mul_self (Geb.BitTree.Counter.lt_pow_size n)
  nlinarith

/-- A runtime query into the quadratic word, including the first out-of-range
index, takes cubic time and logarithmic space. The query is on a work tape,
the result is at most one bit, and the caller's output is preserved. -/
theorem squareDigit_runsTo (w : List Bool) (query : ℕ) (out : List Bool)
    (hq : query ≤ w.length * w.length) :
    ∃ cfg' t, t ≤ 320 * (w.length + 1) ^ 3 ∧
      RunsTo (readOutput squareMachine)
        (wrapCfg (squareMachine.initCfg w) false query [] out)
        (wrapCfg cfg' (((squareWord.eval ![w] Fin.elim0)[query]?).isSome) 0
          (((squareWord.eval ![w] Fin.elim0)[query]?).toList) out)
        t (2 * w.length.size + 1) := by
  obtain ⟨cfg', t, ht, h⟩ := squareMachine_emits w
  have hsize : query.size ≤ 2 * w.length.size + 1 :=
    (size_le_size (hq.trans (Nat.le_succ _))).trans (size_square_add_one_le w.length)
  obtain ⟨u, hu, r⟩ := readOutput_runsTo squareMachine h query out
    (2 * w.length.size + 1) (by omega) hsize
  rw [length_squareWord, Nat.sub_eq_zero_of_le hq] at r
  refine ⟨cfg', u, ?_, r⟩
  have hn := size_le_self w.length
  have ht' : t ≤ 32 * (w.length + 1) ^ 2 := by
    apply ht.trans
    unfold countInputTime
    nlinarith [Nat.mul_le_mul_left w.length hn]
  calc
    u ≤ t * (2 * (2 * w.length.size + 1) + 8) := hu
    _ ≤ (32 * (w.length + 1) ^ 2) * (10 * (w.length + 1)) :=
      Nat.mul_le_mul ht' (by omega)
    _ = 320 * (w.length + 1) ^ 3 := by nlinarith

/-- The generated quadratic word has an exact length reader on two work tapes.
The counter is logarithmic and no part of the generated word is stored or emitted. -/
theorem squareLength_runsTo (w : List Bool) :
    ∃ cfg' t, t ≤ 224 * (w.length + 1) ^ 3 ∧
      RunsTo (countOutput squareMachine) ((countOutput squareMachine).initCfg w)
        (countOutputCfg cfg' (w.length * w.length) []) t (2 * w.length.size + 1) := by
  obtain ⟨cfg', t, ht, h⟩ := squareMachine_emits w
  have hs := size_square_add_one_le w.length
  have hm : Emits squareMachine (squareMachine.initCfg w) cfg'
      (squareWord.eval ![w] Fin.elim0) t (2 * w.length.size + 1) := {
    live := h.live
    runFrom_eq := h.runFrom_eq
    pos := fun j hj i ↦ ⟨(h.pos j hj i).1, (h.pos j hj i).2.trans (by omega)⟩
    output := h.output
    halted := h.halted }
  obtain ⟨u, hu, r⟩ := countOutput_runsTo squareMachine hm 0 []
    (by simpa only [Nat.zero_add, length_squareWord] using hs)
  rw [countOutput_initCfg, Nat.zero_add, length_squareWord] at r
  refine ⟨cfg', u, ?_, r⟩
  have hn := size_le_self w.length
  have ht' : t ≤ 32 * (w.length + 1) ^ 2 := by
    apply ht.trans
    unfold countInputTime
    nlinarith [Nat.mul_le_mul_left w.length hn]
  calc
    u ≤ t * (2 * (2 * w.length.size + 1) + 5) := hu
    _ ≤ (32 * (w.length + 1) ^ 2) * (7 * (w.length + 1)) :=
      Nat.mul_le_mul ht' (by omega)
    _ = 224 * (w.length + 1) ^ 3 := by nlinarith

/-- A concrete composition over a generated quadratic word: numerical length
after {name}`squareWord`, with cubic time and logarithmic space on two tapes. -/
theorem computableInTimeAndSpace_length_squareWord :
    ComputableInTimeAndSpaceOfLength
      (fun w ↦ (Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![w] Fin.elim0)
      (.refl _) (.refl _) (fun n ↦ 256 * (n + 1) ^ 3)
      (fun n ↦ 6 * (n.size + 1)) := by
  have h := lengthMachine_computable squareMachine
    (fun w ↦ squareWord.eval ![w] Fin.elim0) (fun n ↦ 32 * (n + 1) ^ 2)
    (fun n ↦ 2 * n.size + 1)
    (by
      intro w
      obtain ⟨cfg', t, ht, e⟩ := squareMachine_emits w
      refine ⟨cfg', t, ?_, { e with
        pos := fun j hj i ↦ ⟨(e.pos j hj i).1, (e.pos j hj i).2.trans (by omega)⟩ }⟩
      apply ht.trans
      unfold countInputTime
      have hs := size_le_self w.length
      nlinarith [Nat.mul_le_mul_left w.length hs])
    (fun w ↦ by rw [length_squareWord]; exact size_square_add_one_le w.length)
  have heq : (fun w ↦
      (Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![w] Fin.elim0) =
      fun w ↦ unrank (squareWord.eval ![w] Fin.elim0).length := by
    funext w
    rw [Expr.eval_comp]
    simpa only [Matrix.cons_fin_one] using eval_lengthByRec (squareWord.eval ![w] Fin.elim0)
  rw [heq]
  apply h.mono
  · intro w
    change (32 * (w.length + 1) ^ 2) * (2 * (2 * w.length.size + 1) + 5) +
      (3 * (2 * w.length.size + 1) + 5) ≤ 256 * (w.length + 1) ^ 3
    have hs := size_le_self w.length
    have hf : 2 * (2 * w.length.size + 1) + 5 ≤ 7 * (w.length + 1) := by omega
    nlinarith [Nat.mul_le_mul_left (32 * (w.length + 1) ^ 2) hf]
  · intro w
    change (1 + 1) * (2 * w.length.size + 1 + 2) ≤ 6 * (w.length.size + 1)
    omega

end

end Geb.Oitavem.Machine
