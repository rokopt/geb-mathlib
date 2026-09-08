/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Machine
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Difference
public import Geb.Prototypes.Computability.BitTree.Counter
public import Mathlib.Data.Nat.Bitwise

set_option doc.verso true

/-!
# Representation invariants for binary counters

The representation relation records digit values, origin markers and the
mismatch count. It permits either blank cells or explicit zero digits beyond
the represented number. The fixed width bounds both binary counters throughout
a complete execution.

## Main definitions

* {lit}`bitsAt` extends a natural number's digits by zero.
* {lit}`Represents` describes configurations at scan boundaries.

## Tags

Turing machine, binary representation, simulation
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- A natural number's little-endian bit sequence, extended by zero. -/
def bitsAt (n j : ℕ) : Bool := (n.bits[j]?).getD false

/-- The zero-extended list representation agrees with bit testing. -/
theorem bitsAt_eq_testBit (n j : ℕ) : bitsAt n j = n.testBit j := by
  rw [Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  rfl

/-- Zero-extended binary representations determine their natural numbers. -/
theorem bitsAt_injective {a b : ℕ} (h : bitsAt a = bitsAt b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simpa only [bitsAt_eq_testBit] using congrFun h i

/-- All digits beyond the binary size are zero. -/
theorem bitsAt_of_size_le (n j : ℕ) (h : n.size ≤ j) : bitsAt n j = false := by
  have hl : n.bits.length ≤ j := by rw [Counter.length_bits]; exact h
  simp only [bitsAt, List.getElem?_eq_none hl, Option.getD_none]

/-- Scan-boundary configurations represent two bounded binary counters. -/
structure Represents {input : List (Fin 4)} (width : ℕ)
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (q : Fin 10) (a b : ℕ) : Prop where
  /-- Finite control at the scan boundary. -/
  state : cfg.state = some q
  /-- The fork counter is read at its least significant digit. -/
  forkPos : cfg.workTapePos 0 = 0
  /-- The leaf counter is read at its least significant digit. -/
  leafPos : cfg.workTapePos 1 = 0
  /-- Digit representation of the fork counter. -/
  forkDigits : digits cfg 0 = bitsAt a
  /-- Digit representation of the leaf counter. -/
  leafDigits : digits cfg 1 = bitsAt b
  /-- Only the origin is tagged on the first binary tape. -/
  originTag : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)
  /-- The mismatch tape contains only its origin marker. -/
  marker : ∀ z, cfg.workTapes 2 z = if z = 0 then some 0 else none
  /-- The third head counts unequal digit positions. -/
  mismatchPos : cfg.workTapePos 2 = (mismatchCount width (bitsAt a) (bitsAt b) : ℤ)
  /-- The fork counter fits within the fixed width. -/
  forkSize : a.size ≤ width
  /-- The leaf counter fits within the fixed width. -/
  leafSize : b.size ≤ width

/-- The mismatch head is at the origin exactly when the two counters are equal. -/
theorem Represents.mismatchPos_eq_zero_iff {input : List (Fin 4)} {width a b : ℕ}
    {cfg : Cfg 3 (Fin 4) (Fin 10) input} {q : Fin 10}
    (h : Represents width cfg q a b) : cfg.workTapePos 2 = 0 ↔ a = b := by
  have he := mismatchCount_eq_zero_iff_eq width (bitsAt a) (bitsAt b) (by
    intro j hj
    rw [bitsAt_of_size_le a j (Nat.le_trans h.forkSize hj),
      bitsAt_of_size_le b j (Nat.le_trans h.leafSize hj)])
  constructor
  · intro hz
    have hc : mismatchCount width (bitsAt a) (bitsAt b) = 0 := by
      have hp := h.mismatchPos
      omega
    exact bitsAt_injective (he.mp hc)
  · intro hab
    have hc := he.mpr (congrArg bitsAt hab)
    rw [h.mismatchPos, hc]
    rfl

/-- The initial counters differ only at their least significant digit. -/
theorem mismatchCount_one_zero (width : ℕ) (hw : 1 ≤ width) :
    mismatchCount width (bitsAt 1) (bitsAt 0) = 1 := by
  cases width with
  | zero => omega
  | succ width =>
    apply Nat.rec (motive := fun k ↦ mismatchCount (k + 1) (bitsAt 1) (bitsAt 0) = 1)
      ?_ ?_ width
    · rfl
    · intro k ih
      rw [mismatchCount_succ, ih]
      have h1 : bitsAt 1 (k + 1) = false := bitsAt_of_size_le 1 (k + 1) (by change 1 ≤ k + 1; omega)
      have h0 : bitsAt 0 (k + 1) = false := bitsAt_of_size_le 0 (k + 1) (Nat.zero_le _)
      rw [h1, h0]
      rfl

/-- Initialization establishes the boundary representation with one pending root. -/
theorem represents_startCfg (input : List (Fin 4)) (width : ℕ) (hw : 1 ≤ width) :
    Represents width (startCfg input) stTree 1 0 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext j
    change digit (if (j : ℤ) = 0 then some 3 else none) = ([true][j]?).getD false
    cases j with
    | zero => rfl
    | succ j =>
      rw [ite_eq_right (by omega)]
      rfl
  · funext j
    change digit (if (j : ℤ) = 0 then some 2 else none) = false
    split_ifs <;> rfl
  · intro z
    change origin (if z = 0 then some 3 else none) = decide (z = 0)
    split_ifs with hz
    · rw [decide_eq_true hz]
      rfl
    · rw [decide_eq_false hz]
      rfl
  · intro z
    rfl
  · change (1 : ℤ) = (mismatchCount width (bitsAt 1) (bitsAt 0) : ℤ)
    rw [mismatchCount_one_zero width hw]
    rfl
  · exact hw
  · exact Nat.zero_le _

/-- The representation invariant is preserved by a pure input transition. -/
theorem Represents.consume {input : List (Fin 4)} {width a b : ℕ}
    {cfg : Cfg 3 (Fin 4) (Fin 10) input} {q : Fin 10}
    (h : Represents width cfg q a b) (q' : Fin 10) :
    Represents width (consumeCfg cfg q') q' a b :=
  { h with state := rfl }

/-- A scan-boundary representation bounds all three heads. -/
theorem Represents.headBound {input : List (Fin 4)} {width a b : ℕ}
    {cfg : Cfg 3 (Fin 4) (Fin 10) input} {q : Fin 10}
    (h : Represents width cfg q a b) : HeadBound width cfg := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j ↦ Fin.elim0 j))) i
  · change 0 ≤ cfg.workTapePos 0 ∧ cfg.workTapePos 0 ≤ (width : ℤ)
    rw [h.forkPos]
    exact ⟨Int.le_refl _, Int.natCast_nonneg _⟩
  · change 0 ≤ cfg.workTapePos 1 ∧ cfg.workTapePos 1 ≤ (width : ℤ)
    rw [h.leafPos]
    exact ⟨Int.le_refl _, Int.natCast_nonneg _⟩
  · change 0 ≤ cfg.workTapePos 2 ∧ cfg.workTapePos 2 ≤ (width : ℤ)
    rw [h.mismatchPos]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (mismatchCount_le width (bitsAt a) (bitsAt b))⟩

/-- Returning reconstructs the boundary representation and tests counter equality. -/
theorem returnedCfg_represents {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (width a b : ℕ)
    (hd0 : digits cfg 0 = bitsAt a) (hd1 : digits cfg 1 = bitsAt b)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0))
    (hmark : ∀ z, cfg.workTapes 2 z = if z = 0 then some 0 else none)
    (hm : cfg.workTapePos 2 = (mismatchCount width (bitsAt a) (bitsAt b) : ℤ))
    (ha : a.size ≤ width) (hb : b.size ≤ width) :
    Represents width (returnedCfg cfg) (if a = b then stDone else stTree) a b := by
  have hr : Represents width (returnedCfg cfg)
      (if cfg.workTapes 2 (cfg.workTapePos 2) == some 0 then stDone else stTree) a b :=
    ⟨rfl, rfl, rfl, hd0, hd1, ho, hmark, hm, ha, hb⟩
  have he : cfg.workTapePos 2 = 0 ↔ a = b := hr.mismatchPos_eq_zero_iff
  have hs : (if cfg.workTapes 2 (cfg.workTapePos 2) == some 0 then stDone else stTree) =
      (if a = b then stDone else stTree) := by
    by_cases hab : a = b
    · have hp := he.mpr hab
      rw [hmark, ite_eq_left hp, ite_eq_left hab]
      rfl
    · have hp : cfg.workTapePos 2 ≠ 0 := fun hh ↦ hab (he.mp hh)
      rw [hmark, ite_eq_right hp, ite_eq_right hab]
      rfl
  rw [hs] at hr
  exact hr

end Geb.BitTree.BinaryMachine
