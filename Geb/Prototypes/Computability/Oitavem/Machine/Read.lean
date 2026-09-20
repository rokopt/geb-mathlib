/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Count
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Pop
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reusable word readers

Readers for the physical input and for words retained on work tapes use the
valuation contract of the existing logarithmic-space machine library. They return
with parked work heads and the input head at its home position, preserving registers
outside their specified outputs and scratch tapes. Repeated calls therefore need
no assumption that scratch tapes are initially empty.

## Main definitions

* {lit}`inputLength` and {lit}`storedLength` count physical and stored words.
* {lit}`inputAt` and {lit}`readStored` query the physical input and stored words.
* {lit}`seekInputRight` consumes a binary counter to position the input head.

## Main statements

* {lit}`inputLength_transformsIn` and {lit}`storedLength_transformsIn` establish
  the length readers' contracts.
* {lit}`inputAt_transformsIn` and {lit}`readStored_transformsIn` establish digit
  order, out-of-range behavior, workspace bounds, and register preservation.

## Implementation notes

The machine contracts use CSLib configurations and inherit their
{lit}`Classical.choice` dependency. This module is included in
{lit}`GebMeta.classicalAllowedModules`.

## Tags

Turing machine, logarithmic space, word reader, register preservation
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- A right step saturates at the right boundary, including on empty input. -/
theorem inputStepRight_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inStepRight cfg
      { cfg with state := none
                 inputPos := ⟨min (cfg.inputPos.val + 1) (input.length + 1), by omega⟩ }
      1 B := by
  by_cases hp : cfg.inputPos.val < input.length + 1
  · simpa only [Nat.min_eq_left (by omega : cfg.inputPos.val + 1 ≤ input.length + 1)]
      using inStepRight_runsTo cfg hq hp B hpos
  · have hp' : cfg.inputPos.val = input.length + 1 := by have := cfg.inputPos.isLt; omega
    have hhalt : (inStepRight (k := k)).step cfg = { cfg with state := none } := by
      rw [step_of_state _ _ () hq]
      apply Cfg.ext
      · rfl
      · change moveInputPos cfg.inputPos SignType.pos = cfg.inputPos
        rw [show cfg.inputPos = ⟨input.length + 1, by omega⟩ from Fin.ext hp']
        exact moveInputPos_rightBoundary
      · rfl
      · funext i
        change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
        rw [SignType.coe_zero, add_zero]
      · exact List.append_nil _
    have h := RunsTo.ofFamily (inStepRight (k := k)) (fun _ ↦ cfg) 0 B
      { cfg with state := none } (by intro _ _; rw [hq]; exact Option.some_ne_none _)
      (by intro _ h; omega) hhalt rfl (by intro _ _; simp [outputSymbol, hq, inStepRight])
      (fun _ _ i ↦ hpos i) hpos
    refine h.congr_target ?_
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change cfg.inputPos.val = min (cfg.inputPos.val + 1) (input.length + 1)
      omega
    · rfl
    · rfl
    · rfl

/-- Move right by a binary counter, consuming it and stopping at the input boundary. -/
@[expose] def seekInputRight {k : ℕ} (S : Fin k) :=
  whileNonblank (some S) (seq inStepRight (dec S))

/-- Seeking by an arbitrary counter preserves all other registers and saturates
the input position, so out-of-range reads need no separate comparison routine. -/
theorem seekInputRight_runsTo {k : ℕ} {input : List Bool} (S : Fin k)
    (cfg : Cfg k Bool (StateOf (seekInputRight S)) input)
    (hq : cfg.state = some (seekInputRight S).q₀)
    (σ : Fin k → List Bool) (hσ : Holds cfg σ) (hpark : Parked cfg)
    (q B : ℕ) (hS : σ S = counterWord q) (hB : Bounded σ B) :
    ∃ t ≤ q * (2 * B + 8) + 1,
      RunsTo (seekInputRight S) cfg
        { cfg with state := none
                   inputPos := ⟨min (cfg.inputPos.val + q) (input.length + 1), by omega⟩
                   workTapes := fun i ↦ tapeOf (Function.update σ S [] i) } t B := by
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have hbnd (j : ℕ) (hj : j ≤ q) : Bounded (Function.update σ S (counterWord j)) B :=
    hB.update ((length_counterWord_le_of_le hj).trans (hS ▸ hB S))
  let c : ℕ → Cfg k Bool (StateOf (seq inStepRight (dec S))) input := fun j ↦
    { cfg with state := none
               inputPos := ⟨min (cfg.inputPos.val + j) (input.length + 1), by omega⟩
               workTapes := fun i ↦ tapeOf (Function.update σ S (counterWord (q - j)) i) }
  have hprobe (j : ℕ) : probeOf (some S) (c j) = tapeOf (counterWord (q - j)) 0 := by
    change tapeOf (Function.update σ S (counterWord (q - j)) S) (cfg.workTapePos S) = _
    rw [Function.update_self, hpark S]
  obtain ⟨t, ht, h⟩ := RunsTo.whileNonblank (some S) (seq inStepRight (dec S))
    B (2 * B + 7) q c
    (by
      intro j hj hzero
      rw [hprobe] at hzero
      have := (counterWord_eq_nil_iff _).mp ((tapeOf_zero_eq_none_iff _).mp hzero)
      omega)
    (by rw [hprobe, Nat.sub_self]; rfl)
    (by
      intro j hj
      have r₁ := inputStepRight_runsTo { c j with state := some () } rfl B hpB
      have hl : q - j = (q - (j + 1)) + 1 := by omega
      obtain ⟨u, hu, r₂⟩ := dec_transforms S B (input := input)
        { c j with state := some (dec S).q₀
                   inputPos := ⟨min ((c j).inputPos.val + 1) (input.length + 1), by omega⟩ }
        (Function.update σ S (counterWord (q - j))) rfl hpark (fun _ ↦ rfl)
        (hbnd _ (by omega)) (by
          dsimp only
          rw [Function.update_self, hl, decL_counterWord_succ, Function.update_idem]
          exact hbnd _ (by omega))
      refine ⟨1 + u, by omega, ?_⟩
      refine (RunsTo.seqStart (cfg := { c j with state := some (seq inStepRight (dec S)).q₀ })
        rfl r₁ r₂).congr_target ?_
      apply Cfg.ext
      · rfl
      · apply Fin.ext
        change min (min (cfg.inputPos.val + j) (input.length + 1) + 1) (input.length + 1) =
          min (cfg.inputPos.val + (j + 1)) (input.length + 1)
        omega
      · funext i
        change tapeOf (Function.update (Function.update σ S (counterWord (q - j))) S
          (decL (Function.update σ S (counterWord (q - j)) S).reverse).reverse i) = _
        rw [Function.update_self, hl, decL_counterWord_succ, Function.update_idem]
      · rfl
      · rfl)
    (fun i ↦ hpB i)
  have hstart : { c 0 with state := some (.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · apply Fin.ext
      change min (cfg.inputPos.val + 0) (input.length + 1) = cfg.inputPos.val
      have := cfg.inputPos.isLt
      omega
    · funext i
      change tapeOf (Function.update σ S (counterWord (q - 0)) i) = cfg.workTapes i
      rw [Nat.sub_zero, ← hS, Function.update_eq_self, hσ i]
    · rfl
    · rfl
  rw [hstart] at h
  exact ⟨t, by omega, by
    simpa only [seekInputRight, c, Nat.sub_self, show counterWord 0 = [] from rfl] using h⟩

/-- Count the input from the home position, restoring that position on return. -/
@[expose] def inputLength {k : ℕ} (C : Fin k) := seq inStepRight (countInput C)

/-- The length reader overwrites only its result register, including on empty input. -/
theorem inputLength_transformsIn {k : ℕ} (C : Fin k) (B : ℕ → ℕ)
    (hB : ∀ n, n.size ≤ B n) :
    TransformsIn (inputLength C) (fun _ _ ↦ True)
      (fun input σ ↦ Function.update σ C (counterWord input.length))
      (fun n ↦ 1 + countInputTime (B n) n) B := by
  intro input cfg σ hq hpark hpos hσ _ hσB
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    intro i
    rw [hpark i]
    constructor <;> omega
  have r₁ := inStepRight_runsTo { cfg with state := some () } rfl
    (by change cfg.inputPos.val < input.length + 1; omega) (B input.length) hpB
  obtain ⟨t, ht, r₂⟩ := countInput_runsTo C
    { cfg with state := some (countInput C).q₀
               inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ }
    rfl σ hσ hpark (by change cfg.inputPos.val + 1 = 1; omega) (B input.length) hσB
    (hB input.length)
  refine ⟨hσB.update (by rw [length_counterWord]; exact hB _), 1 + t,
    Nat.add_le_add_left ht 1, ?_⟩
  refine (RunsTo.seqStart hq r₁ r₂).congr_target ?_
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    exact hpos.symm
  · rfl
  · rfl
  · rfl

/-- Read the physical input in list order, preserving the index and clearing the
scratch counter. The result is empty outside the input. -/
@[expose] def inputAt {k : ℕ} (C S F : Fin k) :=
  seq (copy C S) (seq inStepRight (seq (seekInputRight S)
    (seq (const [] F) (seq (readBit F) (seq inBack inHome)))))

/-- Time for a physical-input query with bounded binary index. -/
@[expose] def inputAtTime (B Q n : ℕ) : ℕ :=
  (5 * B + 12) + 1 + (Q * (2 * B + 8) + 1) + (4 * B + 9) + 1 + 1 + (n + 1)

/-- The physical-input reader and the stored-word reader use the same indexing
and out-of-range convention, and preserve all caller registers outside their
declared scratch and result tapes. -/
theorem inputAt_transformsIn {k : ℕ} (C S F : Fin k)
    (hCS : C ≠ S) (_hCF : C ≠ F) (_hSF : S ≠ F) (B Q : ℕ → ℕ)
    (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (inputAt C S F)
      (fun input σ ↦ ∃ q, σ C = counterWord q ∧ q ≤ Q input.length)
      (fun input σ ↦ Function.update (Function.update σ S []) F
        (input[counterValue (σ C)]?).toList)
      (fun n ↦ inputAtTime (B n) (Q n) n) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨q, hC, hQ⟩ := hpre
  have hpB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    intro i
    rw [hpark i]
    constructor <;> omega
  let σ₁ := Function.update σ S (σ C)
  let σ₂ := Function.update σ₁ S []
  let σ₃ := Function.update σ₂ F []
  have hb₁ : Bounded σ₁ (B input.length) := hB.update (hB C)
  have hb₂ : Bounded σ₂ (B input.length) := hb₁.update (Nat.zero_le _)
  have hb₃ : Bounded σ₃ (B input.length) := hb₂.update (Nat.zero_le _)
  refine ⟨(hB.update (Nat.zero_le _)).update ?_, ?_⟩
  · exact Option.length_toList_le.trans (hB1 _)
  obtain ⟨t₁, ht₁, r₁⟩ := copy_transforms C S hCS (B input.length)
    { cfg with state := some (copy C S).q₀ } σ rfl hpark hσ hB hb₁
  let cfg₁ : Cfg k Bool Unit input :=
    { cfg with state := some (), workTapes := fun i ↦ tapeOf (σ₁ i) }
  have r₂ := inStepRight_runsTo cfg₁ rfl
    (by change cfg.inputPos.val < input.length + 1; omega) (B input.length) hpB
  obtain ⟨t₃, ht₃, r₃⟩ := seekInputRight_runsTo S (input := input)
    { cfg₁ with state := some (seekInputRight S).q₀
                inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ }
    rfl σ₁ (fun _ ↦ rfl) hpark q (B input.length)
    (by simpa only [σ₁, Function.update_self] using hC) hb₁
  let pos : Fin (input.length + 2) :=
    ⟨min (cfg.inputPos.val + 1 + q) (input.length + 1), by omega⟩
  let cfg₂ : Cfg k Bool Unit input :=
    { cfg₁ with inputPos := pos, workTapes := fun i ↦ tapeOf (σ₂ i) }
  obtain ⟨t₄, ht₄, r₄⟩ := const_transforms [] F (B input.length)
    { cfg₂ with state := some (const [] F).q₀ } σ₂ rfl hpark (fun _ ↦ rfl) hb₂ hb₃
  let cfg₃ : Cfg k Bool Unit input :=
    { cfg₂ with workTapes := fun i ↦ tapeOf (σ₃ i) }
  have hsym : cfg₃.inputSymbol = input[q]? := by
    by_cases hin : q < input.length
    · rw [inputSymbolInner q (by change min _ _ = 1 + q; omega) hin,
        List.getElem?_eq_getElem hin]
    · have he : cfg₃.inputPos.val = input.length + 1 := by
        change min _ _ = _
        omega
      rw [List.getElem?_eq_none (by omega)]
      unfold Cfg.inputSymbol
      rw [dite_eq_right (by
        intro hz
        have := congrArg Fin.val hz
        change min _ _ = 0 at this
        omega), dite_eq_left he]
  have r₅ := readBit_runsTo F cfg₃ rfl (by exact congrArg tapeOf (Function.update_self ..))
    (hpark F) (B input.length) hpB
  rw [hsym] at r₅
  let cfg₄ : Cfg k Bool Unit input :=
    { cfg₃ with workTapes := Function.update cfg₃.workTapes F (tapeOf (input[q]?).toList) }
  have r₆ := inBack_runsTo_of_pos cfg₄ rfl
    (by change min _ _ ≠ 0; omega) (B input.length) hpB
  have r₇ := inHome_runsTo (input := input)
    { cfg₄ with inputPos := ⟨pos.val - 1, by have := pos.isLt; omega⟩ }
    rfl (by have := pos.isLt; change pos.val - 1 ≤ input.length; omega) (B input.length) hpB
  refine ⟨t₁ + (1 + (t₃ + (t₄ + (1 + (1 + (pos.val - 1 + 1)))))), ?_, ?_⟩
  · have := Nat.mul_le_mul_right (2 * B input.length + 8) hQ
    have := pos.isLt
    change _ ≤ inputAtTime (B input.length) (Q input.length) input.length
    unfold inputAtTime
    omega
  · refine (RunsTo.seqStart hq r₁ (RunsTo.seqStart rfl r₂
      (RunsTo.seqStart rfl r₃ (RunsTo.seqStart rfl r₄
        (RunsTo.seqStart rfl r₅ (RunsTo.seqStart rfl r₆ r₇)))))).congr_target ?_
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      exact hpos.symm
    · funext i
      change Function.update (fun i ↦ tapeOf (σ₃ i)) F (tapeOf (input[q]?).toList) i = _
      simp only [σ₃, σ₂, σ₁, Function.update_idem, hC, counterValue_counterWord]
      by_cases hi : i = F
      · subst i
        simp
      · simp [hi]
    · rfl
    · rfl

/-- Read a stored word at a binary index. Registers are the source word, index,
scratch word, scratch counter, and result. Both scratch registers are cleared. -/
@[expose] def readStored {k : ℕ} (r : Fin 5 → Fin k) :=
  seq (copy (r 0) (r 2)) (seq (copy (r 1) (r 3))
    (seq (whileNonblank (some (r 3)) (seq (pop (r 2) (r 4)) (dec (r 3))))
      (seq (pop (r 2) (r 4)) (const [] (r 2)))))

/-- A stored-word reader's time bound for indices at most {lit}`q` and register
lengths at most {lit}`B`. -/
@[expose] def readStoredTime (B q : ℕ) : ℕ :=
  (5 * B + 12) + ((5 * B + 12) +
    (q * ((4 * B + 12) + (2 * B + 6) + 1) + 1 + ((4 * B + 12) + (4 * B + 9))))

/-- The stored-word reader returns a singleton for an in-range digit and the
empty word otherwise. The source and index are preserved; scratch tapes need
not be empty on entry and are empty on return. -/
theorem readStored_transformsIn {k : ℕ} (r : Fin 5 → Fin k)
    (hr : Function.Injective r) (B Q : ℕ → ℕ) :
    TransformsIn (readStored r)
      (fun input σ ↦ ∃ q, σ (r 1) = counterWord q ∧ q ≤ Q input.length)
      (fun _ σ ↦ Function.update (Function.update (Function.update σ (r 2) []) (r 3) [])
        (r 4) ((σ (r 0))[counterValue (σ (r 1))]?).toList)
      (fun n ↦ readStoredTime (B n) (Q n)) B := by
  have hne {i j : Fin 5} (h : i ≠ j) : r i ≠ r j := hr.ne h
  have h23 : r 2 ≠ r 3 := hne (by decide)
  have h24 : r 2 ≠ r 4 := hne (by decide)
  have h34 : r 3 ≠ r 4 := hne (by decide)
  let P : (Fin k → List Bool) → Fin k → List Bool := fun σ ↦
    Function.update (Function.update σ (r 4) (σ (r 2)).head?.toList) (r 2) (σ (r 2)).tail
  let D : (Fin k → List Bool) → Fin k → List Bool := fun σ ↦
    Function.update σ (r 3) (decL (σ (r 3)).reverse).reverse
  let F := D ∘ P
  have hpop : TransformsIn (pop (r 2) (r 4)) (fun _ _ ↦ True) (fun _ ↦ P)
      (fun n ↦ 4 * B n + 12) B := by
    apply Transforms.toIn_of (fun n ↦ pop_transforms (r 2) (r 4) h24 (B n))
    intro input σ hb _
    apply Bounded.update
    · apply hb.update
      cases hw : σ (r 2) with
      | nil => simp
      | cons b w => simpa [hw] using (show 1 ≤ B input.length by
          have := hb (r 2); simp only [hw, List.length_cons] at this; omega)
    · rw [List.length_tail]
      exact (Nat.sub_le _ _).trans (hb (r 2))
  have hdec : TransformsIn (dec (r 3)) (fun _ _ ↦ True) (fun _ ↦ D)
      (fun n ↦ 2 * B n + 6) B := by
    apply Transforms.toIn_of (fun n ↦ dec_transforms (r 3) (B n))
    intro input σ hb _
    apply hb.update
    simpa only [List.length_reverse] using
      (length_decL_le (σ (r 3)).reverse).trans (by simpa using hb (r 3))
  have hbody : TransformsIn (seq (pop (r 2) (r 4)) (dec (r 3)))
      (fun _ _ ↦ True) (fun _ ↦ F) (fun n ↦ (4 * B n + 12) + (2 * B n + 6)) B :=
    (hpop.seq hdec).mono_pre (fun _ _ _ _ ↦ ⟨trivial, trivial⟩)
  have hcount (σ : Fin k → List Bool) (q : ℕ) (hq : σ (r 3) = counterWord q) :
      ∀ j ≤ q, (F^[j] σ) (r 3) = counterWord (q - j) := by
    refine Nat.rec (fun _ ↦ by simpa using hq) (fun j ih hj ↦ ?_)
    rw [Function.iterate_succ_apply']
    have hj' : q - j = (q - (j + 1)) + 1 := by omega
    simp only [F, Function.comp_apply, D, P, Function.update_self,
      Function.update_of_ne h23.symm, Function.update_of_ne h34, ih (by omega), hj',
      decL_counterWord_succ]
  have hword (σ : Fin k → List Bool) :
      ∀ j, (F^[j] σ) (r 2) = (σ (r 2)).drop j := by
    refine Nat.rec (by simp) (fun j ih ↦ ?_)
    rw [Function.iterate_succ_apply']
    simp only [F, Function.comp_apply, D, P, Function.update_of_ne h23,
      Function.update_self, ih, List.tail_drop]
  have hpres (σ : Fin k → List Bool) (t : Fin k) (ht2 : t ≠ r 2)
      (ht3 : t ≠ r 3) (ht4 : t ≠ r 4) : ∀ j, F^[j] σ t = σ t := by
    refine Nat.rec rfl (fun j ih ↦ ?_)
    rw [Function.iterate_succ_apply']
    simpa only [F, Function.comp_apply, D, P, Function.update_of_ne ht2,
      Function.update_of_ne ht3, Function.update_of_ne ht4] using ih
  have hloop := TransformsIn.whileReg (r 3) hbody
    (fun input σ ↦ ∃ q, σ (r 3) = counterWord q ∧ q ≤ Q input.length)
    (fun _ σ ↦ counterValue (σ (r 3))) Q
    (by
      rintro input σ ⟨q, hq, hQ⟩
      simpa only [hq, counterValue_counterWord] using hQ)
    (by
      rintro input σ ⟨q, hq, _⟩ j hj
      simp only [hq, counterValue_counterWord] at hj
      refine ⟨?_, trivial⟩
      rw [hcount σ q hq j (by omega)]
      intro hzero
      have := (counterWord_eq_nil_iff _).mp hzero
      omega)
    (by
      rintro input σ ⟨q, hq, _⟩
      simp only [hq, counterValue_counterWord]
      rw [hcount σ q hq q (by omega), Nat.sub_self]
      rfl)
  have hcopy (i j : Fin k) (hij : i ≠ j) :
      TransformsIn (copy i j) (fun _ _ ↦ True) (fun _ σ ↦ Function.update σ j (σ i))
        (fun n ↦ 5 * B n + 12) B :=
    Transforms.toIn_of (fun n ↦ copy_transforms i j hij (B n)) _
      (fun _ _ hb _ ↦ hb.update (hb i))
  have hclear : TransformsIn (const [] (r 2)) (fun _ _ ↦ True)
      (fun _ σ ↦ Function.update σ (r 2) []) (fun n ↦ 4 * B n + 9) B :=
    Transforms.toIn_of (fun n ↦ const_transforms [] (r 2) (B n)) _
      (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
  have h := (hcopy (r 0) (r 2) (hne (by decide))).seq
    ((hcopy (r 1) (r 3) (hne (by decide))).seq (hloop.seq (hpop.seq hclear)))
  have h' := h.mono_pre (Pre' := fun input σ ↦
      ∃ q, σ (r 1) = counterWord q ∧ q ≤ Q input.length) (by
    rintro input σ _ ⟨q, hq, hQ⟩
    refine ⟨trivial, trivial, ⟨q, ?_, hQ⟩, trivial, trivial⟩
    simp only [Function.update_self, Function.update_of_ne (hne (by decide : (1 : Fin 5) ≠ 2)), hq])
  apply h'.congr
  rintro input σ ⟨q, hq, _⟩
  let σ₀ := Function.update (Function.update σ (r 2) (σ (r 0))) (r 3) (σ (r 1))
  have hc : σ₀ (r 3) = counterWord q := by simp [σ₀, hq]
  have hw : σ₀ (r 2) = σ (r 0) := by simp [σ₀, h23]
  simp only [Function.update_of_ne (hne (by decide : (1 : Fin 5) ≠ 2))]
  change Function.update (P (F^[counterValue (σ₀ (r 3))] σ₀)) (r 2) [] = _
  rw [hc, counterValue_counterWord]
  funext t
  by_cases ht2 : t = r 2
  · subst t
    simp [h23, h24]
  · by_cases ht3 : t = r 3
    · subst t
      simp only [Function.update_of_ne h23.symm, P, Function.update_of_ne h34,
        hcount σ₀ q hc q (by omega), Nat.sub_self, Function.update_self]
      rfl
    · by_cases ht4 : t = r 4
      · subst t
        simp only [Function.update_of_ne h24.symm, P, Function.update_self,
          hword σ₀ q, hw, List.head?_drop, hq, counterValue_counterWord]
      · simp only [Function.update_of_ne ht2, Function.update_of_ne ht3,
          Function.update_of_ne ht4, P, hpres σ₀ t ht2 ht3 ht4 q, σ₀]

/-- Count a stored word without changing it. Registers are the source, scratch
word, result counter, and scratch flag; both scratch registers are cleared. -/
@[expose] def storedLength {k : ℕ} (r : Fin 4 → Fin k) :=
  seq (copy (r 0) (r 1)) (seq (const [] (r 2))
    (seq (whileNonblank (some (r 1)) (seq (pop (r 1) (r 3)) (inc (r 2))))
      (const [] (r 3))))

/-- The stored-length reader's time bound at a register-length bound. -/
@[expose] def storedLengthTime (B : ℕ) : ℕ :=
  (5 * B + 12) + ((4 * B + 9) + (B * ((4 * B + 12) + (2 * B + 6) + 1) + 1 +
    (4 * B + 9)))

/-- The stored-length reader returns the exact length in ordinary binary,
preserving the source and every unrelated register. -/
theorem storedLength_transformsIn {k : ℕ} (r : Fin 4 → Fin k)
    (hr : Function.Injective r) (B : ℕ → ℕ) :
    TransformsIn (storedLength r) (fun _ _ ↦ True)
      (fun _ σ ↦ Function.update (Function.update (Function.update σ (r 1) [])
        (r 2) (counterWord (σ (r 0)).length)) (r 3) [])
      (fun n ↦ storedLengthTime (B n)) B := by
  intro input cfg σ hq hpark _ hσ _ hB
  have hne {i j : Fin 4} (h : i ≠ j) : r i ≠ r j := hr.ne h
  have h12 : r 1 ≠ r 2 := hne (by decide)
  have h13 : r 1 ≠ r 3 := hne (by decide)
  have h23 : r 2 ≠ r 3 := hne (by decide)
  let w := σ (r 0)
  have hwB : w.length ≤ B input.length := hB (r 0)
  let σ₀ := Function.update (Function.update σ (r 1) w) (r 2) []
  let val : ℕ → Fin k → List Bool := fun j ↦
    Function.update (Function.update (Function.update σ₀ (r 1) (w.drop j))
      (r 2) (counterWord j)) (r 3) (if j = 0 then σ₀ (r 3) else (w[j - 1]?).toList)
  have hval0 : val 0 = σ₀ := by
    have hw : w = σ₀ (r 1) := by simp [σ₀, h12]
    have hc : counterWord 0 = σ₀ (r 2) := by simp [σ₀]; rfl
    simp only [val, List.drop_zero, hw, hc, Function.update_eq_self, ite_true]
  have hb₀ : Bounded σ₀ (B input.length) :=
    (hB.update (hB (r 0))).update (Nat.zero_le _)
  have hvalB (j : ℕ) (hj : j ≤ w.length) : Bounded (val j) (B input.length) := by
    apply Bounded.update
    · apply Bounded.update
      · apply hb₀.update
        rw [List.length_drop]
        exact (Nat.sub_le _ _).trans hwB
      · rw [length_counterWord]
        exact (size_le_self j).trans (hj.trans (hB (r 0)))
    · split
      · exact hb₀ (r 3)
      · exact Option.length_toList_le.trans (by omega)
  let body := seq (pop (r 1) (r 3)) (inc (r 2))
  let c : ℕ → Cfg k Bool (StateOf body) input := fun j ↦
    { cfg with state := none, workTapes := fun i ↦ tapeOf (val j i) }
  have hprobe (j : ℕ) : probeOf (some (r 1)) (c j) = tapeOf (w.drop j) 0 := by
    change tapeOf (val j (r 1)) (cfg.workTapePos (r 1)) = _
    simp only [val, Function.update_of_ne h13,
      Function.update_of_ne h12, Function.update_self, hpark (r 1)]
  obtain ⟨t₂, ht₂, h₂⟩ := RunsTo.whileNonblank (some (r 1)) body
    (B input.length) ((4 * B input.length + 12) + (2 * B input.length + 6)) w.length c
    (by
      intro j hj hzero
      rw [hprobe] at hzero
      have := congrArg List.length ((tapeOf_zero_eq_none_iff _).mp hzero)
      simp only [List.length_drop, List.length_nil] at this
      omega)
    (by rw [hprobe, List.drop_length]; rfl)
    (by
      intro j hj
      let σp := Function.update (Function.update (val j) (r 3)
        ((val j) (r 1)).head?.toList) (r 1) ((val j) (r 1)).tail
      have hword : val j (r 1) = w.drop j := by simp [val, h13, h12]
      have hpB : Bounded σp (B input.length) := by
        apply Bounded.update
        · exact (hvalB j (by omega)).update (Option.length_toList_le.trans
            (by omega))
        · rw [List.length_tail]
          exact (Nat.sub_le _ _).trans (hvalB j (by omega) (r 1))
      have hcounter : σp (r 2) = counterWord j := by simp [σp, val, h23, h12.symm]
      have hnext : Function.update σp (r 2) (incL (σp (r 2)).reverse).reverse =
          val (j + 1) := by
        rw [hcounter, incL_counterWord]
        funext i
        simp only [σp, val, hword, List.head?_drop, List.tail_drop, Nat.add_sub_cancel,
          show j + 1 ≠ 0 by omega, ite_false]
        by_cases hi1 : i = r 1
        · subst i; simp [h12, h13]
        · by_cases hi2 : i = r 2
          · subst i; simp [h23]
          · by_cases hi3 : i = r 3
            · subst i; simp [h23.symm, h13.symm]
            · simp [hi1, hi2, hi3]
      obtain ⟨u, hu, ru⟩ := pop_transforms (r 1) (r 3) h13 (B input.length)
        { c j with state := some (pop (r 1) (r 3)).q₀ } (val j) rfl hpark (fun _ ↦ rfl)
        (hvalB j (by omega)) hpB
      obtain ⟨v, hv, rv⟩ := inc_transforms (r 2) (B input.length)
        { cfg with state := some (inc (r 2)).q₀, workTapes := fun i ↦ tapeOf (σp i) }
        σp rfl hpark (fun _ ↦ rfl) hpB (by
          dsimp only
          rw [hnext]
          exact hvalB _ (by omega))
      refine ⟨u + v, by omega, ?_⟩
      refine (RunsTo.seqStart (cfg := { c j with state := some body.q₀ }) rfl ru rv).congr_target ?_
      apply Cfg.ext
      · rfl
      · rfl
      · exact congrArg (fun σ i ↦ tapeOf (σ i)) hnext
      · rfl
      · rfl)
    (by intro i; change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ _
        rw [hpark i]; constructor <;> omega)
  have hcopyB : Bounded (Function.update σ (r 1) w) (B input.length) :=
    hB.update (hB (r 0))
  obtain ⟨t₀, ht₀, h₀⟩ := copy_transforms (r 0) (r 1) (hne (by decide)) (B input.length)
    { cfg with state := some (copy (r 0) (r 1)).q₀ } σ rfl hpark hσ hB hcopyB
  obtain ⟨t₁, ht₁, h₁⟩ := const_transforms [] (r 2) (B input.length)
    { cfg with state := some (const [] (r 2)).q₀
               workTapes := fun i ↦ tapeOf (Function.update σ (r 1) w i) }
    (Function.update σ (r 1) w) rfl hpark (fun _ ↦ rfl) hcopyB hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := const_transforms [] (r 3) (B input.length)
    { c w.length with state := some (const [] (r 3)).q₀ } (val w.length)
    rfl hpark (fun _ ↦ rfl) (hvalB _ (le_refl _))
    ((hvalB _ (le_refl _)).update (Nat.zero_le _))
  have hend : Function.update (val w.length) (r 3) [] =
      Function.update (Function.update (Function.update σ (r 1) [])
        (r 2) (counterWord w.length)) (r 3) [] := by
    funext i
    by_cases hi1 : i = r 1
    · subst i; simp [val, h12, h13]
    · by_cases hi2 : i = r 2
      · subst i; simp [val, h23]
      · by_cases hi3 : i = r 3
        · subst i; simp
        · simp [val, σ₀, hi1, hi2, hi3]
  refine ⟨?_, t₀ + (t₁ + (t₂ + t₃)), ?_, ?_⟩
  · change Bounded (Function.update (Function.update (Function.update σ (r 1) [])
      (r 2) (counterWord w.length)) (r 3) []) (B input.length)
    rw [← hend]
    exact (hvalB _ (le_refl _)).update (Nat.zero_le _)
  · have := Nat.mul_le_mul_right ((4 * B input.length + 12) + (2 * B input.length + 6) + 1)
      hwB
    change _ ≤ storedLengthTime (B input.length)
    unfold storedLengthTime
    omega
  · simp only [c, hval0] at h₂
    refine (RunsTo.seqStart hq h₀ (RunsTo.seqStart rfl h₁
      (RunsTo.seqStart rfl h₂ h₃))).congr_target ?_
    apply Cfg.ext
    · rfl
    · rfl
    · exact congrArg (fun σ i ↦ tapeOf (σ i)) hend
    · rfl
    · rfl

end

end Geb.Oitavem.Machine
