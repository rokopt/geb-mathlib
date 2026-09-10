/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Representation

set_option doc.verso true

/-!
# Counter layouts shared by the increment sites

A counter pair occupies two digit tapes and one mismatch tape. Its least significant digits
sit at a common cell, tagged on the first tape, and its digits extend from that cell in a
fixed direction. A carry flips the selected tape's digits away from the tagged cell and moves
the mismatch head by the local digit comparison; a return moves both digit heads back to the
tagged cell and reads the mismatch marker to decide equality of the two counters. The
transitions are stated once for any layout, so the same execution proofs serve every site.

## Main definitions

* {lit}`Layout` names the three tapes and the digit direction of a counter pair.
* {lit}`cell` locates a digit of given significance.
* {lit}`digitsFrom` reads a tape as a bit stream from its least significant cell.
* {lit}`carry` and {lit}`returnTr` are the two transitions of an increment.
* {lit}`PairData` records the contents of a counter pair at a scan boundary.
* {lit}`PairRep` adds the head positions at the least significant cell.

## Tags

Turing machine, binary counter, layout
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (digit origin flipped mismatchMove mismatchCount bitsAt)

/-- The finite control of the machine. -/
abbrev Control := Fin 30

/-- The three tapes and the digit direction of a counter pair. -/
structure Layout where
  /-- The digit tape carrying the least-significant tag. -/
  first : Fin 9
  /-- The digit tape without tags. -/
  second : Fin 9
  /-- The tape whose head position counts unequal digits. -/
  mism : Fin 9
  /-- The direction from the least significant digit towards more significant ones. -/
  dir : SignType
  deriving DecidableEq

/-- A layout is proper when its tapes are distinct and its direction is nonzero. -/
structure Layout.Proper (lay : Layout) : Prop where
  /-- The two digit tapes differ. -/
  first_ne_second : lay.first ≠ lay.second
  /-- The mismatch tape differs from the first digit tape. -/
  first_ne_mism : lay.first ≠ lay.mism
  /-- The mismatch tape differs from the second digit tape. -/
  second_ne_mism : lay.second ≠ lay.mism
  /-- The digits extend in a definite direction. -/
  dir_ne_zero : lay.dir ≠ 0

/-- The cell holding the digit of the given significance. -/
def cell (lsb : ℤ) (d : SignType) (j : ℕ) : ℤ := lsb + (d : ℤ) * j

/-- The next more significant cell lies one step in the digit direction. -/
theorem cell_succ (lsb : ℤ) (d : SignType) (j : ℕ) : cell lsb d (j + 1) = cell lsb d j + d := by
  simp only [cell, Nat.cast_succ, Int.mul_add, Int.mul_one, Int.add_assoc]

/-- The least significant cell has significance zero. -/
theorem cell_zero (lsb : ℤ) (d : SignType) : cell lsb d 0 = lsb := by
  simp [cell]

/-- Distinct significances occupy distinct cells in a nonzero direction. -/
theorem cell_injective (lsb : ℤ) (d : SignType) (hd : d ≠ 0) (i j : ℕ)
    (h : cell lsb d i = cell lsb d j) : i = j := by
  cases d with
  | zero => exact (hd rfl).elim
  | neg => simp only [cell, SignType.cast] at h; omega
  | pos => simp only [cell, SignType.cast] at h; omega

/-- Read a tape as a bit stream indexed by significance. -/
def digitsFrom {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (i : Fin 9)
    (lsb : ℤ) (d : SignType) (j : ℕ) : Bool := digit (cfg.workTapes i (cell lsb d j))

/-- Flip the selected tape's current digit and maintain the mismatch count, moving the
digit heads one cell towards higher significance. The first zero ends the carry. -/
def carry (lay : Layout) (sel : Bool) (stC stR : Control)
    (work : Fin 9 → Option (Fin 4)) : TransitionOut 9 (Fin 4) Control :=
  let s : Fin 9 := if sel then lay.second else lay.first
  { inputMove := 0
    workActions := fun i ↦
      if i = lay.mism then (none, mismatchMove (work lay.first) (work lay.second))
      else if i = lay.first ∨ i = lay.second then
        (if i = s then some (some (flipped (work i))) else none, lay.dir)
      else (none, 0)
    outS := none
    q' := some (if digit (work s) then stC else stR) }

/-- Move both digit heads towards the tagged cell; at the tag, read the mismatch marker to
select the continuation for equal or unequal counters. -/
def returnTr (lay : Layout) (stR stZ stN : Control)
    (work : Fin 9 → Option (Fin 4)) : TransitionOut 9 (Fin 4) Control :=
  if origin (work lay.first) then
    { inputMove := 0
      workActions := fun _ ↦ (none, 0)
      outS := none
      q' := some (if work lay.mism == some 0 then stZ else stN) }
  else
    { inputMove := 0
      workActions := fun i ↦ (none, if i = lay.first ∨ i = lay.second then -lay.dir else 0)
      outS := none
      q' := some stR }

/-- The contents of a counter pair, without constraints on its digit heads. -/
structure PairData {input : List (Fin 4)} (lay : Layout) (lsb : ℤ) (width : ℕ)
    (cfg : Cfg 9 (Fin 4) Control input) (a b : ℕ) : Prop where
  /-- Digit representation of the first counter. -/
  firstDigits : digitsFrom cfg lay.first lsb lay.dir = bitsAt a
  /-- Digit representation of the second counter. -/
  secondDigits : digitsFrom cfg lay.second lsb lay.dir = bitsAt b
  /-- Only the least significant cell is tagged on the first tape. -/
  originTag : ∀ z, origin (cfg.workTapes lay.first z) = decide (z = lsb)
  /-- The first tape is blank exactly beyond the represented digits. -/
  firstBlank : ∀ j, cfg.workTapes lay.first (cell lsb lay.dir j) = none ↔ a.size ≤ j
  /-- The mismatch tape contains only its origin marker. -/
  marker : ∀ z, cfg.workTapes lay.mism z = if z = 0 then some 0 else none
  /-- The mismatch head counts unequal digit positions. -/
  mismatchPos : cfg.workTapePos lay.mism = (mismatchCount width (bitsAt a) (bitsAt b) : ℤ)
  /-- The first counter fits within the width. -/
  firstSize : a.size ≤ width
  /-- The second counter fits within the width. -/
  secondSize : b.size ≤ width

/-- A counter pair with both digit heads at the least significant cell. -/
structure PairRep {input : List (Fin 4)} (lay : Layout) (lsb : ℤ) (width : ℕ)
    (cfg : Cfg 9 (Fin 4) Control input) (a b : ℕ) : Prop extends
    PairData lay lsb width cfg a b where
  /-- The first digit head reads the least significant digit. -/
  firstPos : cfg.workTapePos lay.first = lsb
  /-- The second digit head reads the least significant digit. -/
  secondPos : cfg.workTapePos lay.second = lsb

/-- The mismatch head is at the origin exactly when the two counters are equal. -/
theorem PairData.mismatchPos_eq_zero_iff {input : List (Fin 4)} {lay : Layout} {lsb : ℤ}
    {width a b : ℕ} {cfg : Cfg 9 (Fin 4) Control input}
    (h : PairData lay lsb width cfg a b) : cfg.workTapePos lay.mism = 0 ↔ a = b := by
  have he := Geb.BitTree.BinaryMachine.mismatchCount_eq_zero_iff_eq width (bitsAt a)
    (bitsAt b) (by
      intro j hj
      rw [Geb.BitTree.BinaryMachine.bitsAt_of_size_le a j (Nat.le_trans h.firstSize hj),
        Geb.BitTree.BinaryMachine.bitsAt_of_size_le b j (Nat.le_trans h.secondSize hj)])
  constructor
  · intro hz
    have hc : mismatchCount width (bitsAt a) (bitsAt b) = 0 := by
      have hp := h.mismatchPos
      omega
    exact Geb.BitTree.BinaryMachine.bitsAt_injective (he.mp hc)
  · intro hab
    have hc := he.mpr (congrArg bitsAt hab)
    rw [h.mismatchPos, hc]
    rfl

end Geb.BitTree.EliasBinary
