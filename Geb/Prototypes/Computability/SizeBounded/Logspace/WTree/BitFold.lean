/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScanExpr
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A lockstep fold over the bits of two numerals

A simultaneous recursion over the word that visits the indices of the bits of
three coded numbers at three positions in lockstep: at each index it reads
the bit of each number there, by
{name}`Geb.SizeBounded.Logspace.WTree.NumExpr.numHit`, and updates a family
of registers by an expression given as a parameter. The comparisons of
numerals, the check of a sum, and the reading of a numeral into a counter are
instances, each a choice of bases and of an update.

# Main definitions

* {lit}`regSlot`, {lit}`parSlot`, {lit}`idxV`, {lit}`hitA`, {lit}`hitB`,
  {lit}`hitC`, {lit}`updEnv` — the slots of the step environment, the three
  bits, and the environment an update reads.
* {lit}`foldBase`, {lit}`foldStep`, {lit}`foldReg`, {lit}`bitFold` — the
  recursion, and a register after the fold over the word as an expression
  of arity four.
* {lit}`updF`, {lit}`iter` — the update's meaning on registers and bits,
  and its iteration over the indices below a bound.

# Main statements

* {lit}`regs_eq` — after a prefix of the word, the registers hold the
  iteration over the prefix's length.
* {lit}`sem_bitFold` — a register's value is the iteration over the word's
  length.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, simultaneous recursion on notation, binary numeral, lockstep
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.BitFold

open Numeral

public section

variable {k : ℕ}

/-- The index register's slot: the first register. -/
@[expose] def idxSlot : Fin (k + 1 + 4 + 1) := Fin.succ (Fin.castAdd 4 0)

/-- A register's slot, after the index. -/
@[expose] def regSlot (j : Fin k) : Fin (k + 1 + 4 + 1) := Fin.succ (Fin.castAdd 4 j.succ)

/-- A parameter's slot: the word and the three positions. -/
@[expose] def parSlot (j : Fin 4) : Fin (k + 1 + 4 + 1) := Fin.succ (Fin.natAdd (k + 1) j)

/-- The index register. -/
@[expose] def idxV : LOf (k + 1 + 4 + 1) := projL _ idxSlot

/-- The word. -/
@[expose] def wordV : LOf (k + 1 + 4 + 1) := projL _ (parSlot 0)

/-- The first position. -/
@[expose] def pAV : LOf (k + 1 + 4 + 1) := projL _ (parSlot 1)

/-- The second position. -/
@[expose] def pBV : LOf (k + 1 + 4 + 1) := projL _ (parSlot 2)

/-- The third position. -/
@[expose] def pCV : LOf (k + 1 + 4 + 1) := projL _ (parSlot 3)

/-- The bit at the index of the number at the first position. -/
@[expose] def hitA : LOf (k + 1 + 4 + 1) := compL NumExpr.numHit ![wordV, pAV, idxV]

/-- The bit at the index of the number at the second position. -/
@[expose] def hitB : LOf (k + 1 + 4 + 1) := compL NumExpr.numHit ![wordV, pBV, idxV]

/-- The bit at the index of the number at the third position. -/
@[expose] def hitC : LOf (k + 1 + 4 + 1) := compL NumExpr.numHit ![wordV, pCV, idxV]

/-- The environment an update reads: the registers, the three bits and the
word. -/
@[expose] def updEnv : Fin (k + 4) → LOf (k + 1 + 4 + 1) :=
  Fin.append (fun j ↦ projL _ (regSlot j)) ![hitA, hitB, hitC, wordV]

/-- A register's step: its update at the registers, the three bits and the
word. -/
@[expose] def regStep (upd : Fin k → LOf (k + 4)) (j : Fin k) : LOf (k + 1 + 4 + 1) :=
  compL (upd j) updEnv

/-- The recursion's steps: the index's tail and the registers' updates, the
same for either bit of the counter. -/
@[expose] def foldStep (upd : Fin k → LOf (k + 4)) : Bool → Fin (k + 1) → LOf (k + 1 + 4 + 1) :=
  fun _ ↦ Fin.cons (tailAppL idxV) (regStep upd)

/-- The recursion's bases: the word for the index at zero, and the given
bases. -/
@[expose] def foldBase (base : Fin k → LOf 4) : Fin (k + 1) → LOf 4 := Fin.cons (projL 4 0) base

/-- A step environment of the recursion: the level, the index and the
registers, and the word and the two positions. -/
@[expose] def envOf (v : List Bool) (vals : Fin (k + 1) → List Bool) (x : Fin 4 → List Bool) :
    Fin (k + 1 + 4 + 1) → List Bool :=
  stepEnv (a := 4) (b := k + 1) v vals x

/-- The registers, as expressions of arity five: the counter, the word and
the three positions. -/
@[expose] def foldReg (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (l : Fin (k + 1)) :
    LOf 5 :=
  srnL (foldBase base) (foldStep upd) l

/-- A register after the fold over the word, of arity four: the word and
the three positions. -/
@[expose] def bitFold (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (j : Fin k) : LOf 4 :=
  compL (foldReg base upd j.succ) ![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3]

/-- The update's meaning on registers and three bits, at a word. -/
@[expose] def updF (upd : Fin k → LOf (k + 4)) (y : List Bool) (regs : Fin k → List Bool)
    (a b c : Bool) : Fin k → List Bool :=
  fun j ↦ (upd j).sem (Fin.append regs ![boolWord a, boolWord b, boolWord c, y])

/-- The registers after the indices below a bound: the update iterated on the
bits of the three numbers at the successive indices. -/
@[expose] def iter (upd : Fin k → LOf (k + 4)) (y : List Bool) (pA pB pC : ℕ)
    (regs0 : Fin k → List Bool) : ℕ → Fin k → List Bool :=
  Nat.rec regs0 fun i regs ↦
    updF upd y regs (nrun pA i y).hit (nrun pB i y).hit (nrun pC i y).hit

/-- The bases' meanings at a word and three positions. -/
@[expose] def regs0 (base : Fin k → LOf 4) (y : List Bool) (pA pB pC : ℕ) : Fin k → List Bool :=
  fun j ↦ (base j).sem ![y, y.drop pA, y.drop pB, y.drop pC]

/-- The registers' meanings at a counter, a word and three positions. -/
@[expose] def regs (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (u y : List Bool)
    (pA pB pC : ℕ) : Fin (k + 1) → List Bool :=
  fun l ↦ (foldReg base upd l).sem (Fin.cons u ![y, y.drop pA, y.drop pB, y.drop pC])

/-- On the empty counter the registers hold the word for the index and the
bases. -/
theorem regs_nil (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (y : List Bool)
    (pA pB pC : ℕ) : regs base upd [] y pA pB pC = Fin.cons y (regs0 base y pA pB pC) := by
  funext l
  refine Fin.cases (motive := fun l ↦ regs base upd [] y pA pB pC l =
    (Fin.cons y (regs0 base y pA pB pC) : Fin (k + 1) → List Bool) l) rfl (fun j ↦ ?_) l
  rw [Fin.cons_succ]
  change (foldReg base upd j.succ).sem (Fin.cons [] ![y, y.drop pA, y.drop pB, y.drop pC]) = _
  rw [foldReg, sem_srnL_nil, foldBase, Fin.cons_succ]
  rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the parameters. -/
theorem regs_cons (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (b : Bool) (v y : List Bool)
    (pA pB pC : ℕ) (l : Fin (k + 1)) :
    regs base upd (b :: v) y pA pB pC l =
      (foldStep upd b l).sem
        (envOf v (regs base upd v y pA pB pC) ![y, y.drop pA, y.drop pB, y.drop pC]) :=
  sem_srnL_cons (foldBase base) (foldStep upd) l b v ![y, y.drop pA, y.drop pB, y.drop pC]

/-- The index register's slot of a step environment. -/
theorem envOf_idxSlot (v : List Bool) (vals : Fin (k + 1) → List Bool)
    (x : Fin 4 → List Bool) : envOf v vals x idxSlot = vals 0 := by
  rw [envOf, stepEnv, idxSlot, Fin.cons_succ, Fin.append_left]

/-- A register's slot of a step environment. -/
theorem envOf_regSlot (v : List Bool) (vals : Fin (k + 1) → List Bool) (x : Fin 4 → List Bool)
    (j : Fin k) : envOf v vals x (regSlot j) = vals j.succ := by
  rw [envOf, stepEnv, regSlot, Fin.cons_succ, Fin.append_left]

/-- A parameter's slot of a step environment. -/
theorem envOf_parSlot (v : List Bool) (vals : Fin (k + 1) → List Bool) (x : Fin 4 → List Bool)
    (j : Fin 4) : envOf v vals x (parSlot j) = x j := by
  rw [envOf, stepEnv, parSlot, Fin.cons_succ, Fin.append_right]

/-- The update's environment on a step environment holding the index and the
registers is the registers, the three bits at the index, and the word. -/
theorem sem_updEnv (v y : List Bool) (pA pB pC n : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length)
    (hC : pC ≤ y.length) (hn : n ≤ y.length) (rs : Fin k → List Bool) :
    (fun i ↦ (updEnv i).sem
      (envOf v (Fin.cons (y.drop n) rs) ![y, y.drop pA, y.drop pB, y.drop pC])) =
      Fin.append rs ![boolWord (nrun pA n y).hit, boolWord (nrun pB n y).hit,
        boolWord (nrun pC n y).hit, y] := by
  funext i
  refine Fin.addCases (motive := fun i ↦ (updEnv i).sem
    (envOf v (Fin.cons (y.drop n) rs) ![y, y.drop pA, y.drop pB, y.drop pC]) =
      Fin.append rs ![boolWord (nrun pA n y).hit, boolWord (nrun pB n y).hit,
        boolWord (nrun pC n y).hit, y] i)
    (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [updEnv, Fin.append_left, Fin.append_left, sem_projL, envOf_regSlot, Fin.cons_succ]
  · rw [updEnv, Fin.append_right, Fin.append_right]
    have hw : ∀ m : Fin 4, (fun i ↦ (![wordV, projL (k + 1 + 4 + 1) (parSlot m), idxV] i).sem
        (envOf v (Fin.cons (y.drop n) rs) ![y, y.drop pA, y.drop pB, y.drop pC])) =
        ![y, ![y, y.drop pA, y.drop pB, y.drop pC] m, y.drop n] := fun m ↦ funext fun i ↦
      match i with
      | 0 => by
        change wordV.sem _ = y
        rw [wordV, sem_projL, envOf_parSlot]
        rfl
      | 1 => by
        change (projL (k + 1 + 4 + 1) (parSlot m)).sem _ = _
        rw [sem_projL, envOf_parSlot]
        rfl
      | 2 => by
        change idxV.sem _ = y.drop n
        rw [idxV, sem_projL, envOf_idxSlot, Fin.cons_zero]
    match j with
    | 0 =>
      change hitA.sem _ = boolWord (nrun pA n y).hit
      rw [hitA, sem_compL, pAV, hw 1]
      exact NumExpr.sem_numHit y pA n hA hn
    | 1 =>
      change hitB.sem _ = boolWord (nrun pB n y).hit
      rw [hitB, sem_compL, pBV, hw 2]
      exact NumExpr.sem_numHit y pB n hB hn
    | 2 =>
      change hitC.sem _ = boolWord (nrun pC n y).hit
      rw [hitC, sem_compL, pCV, hw 3]
      exact NumExpr.sem_numHit y pC n hC hn
    | 3 =>
      change wordV.sem _ = y
      rw [wordV, sem_projL, envOf_parSlot]
      rfl

/-- After a prefix of the word is read, the index register holds the word
dropped by the prefix's length and the registers the iteration over it. -/
theorem regs_eq (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (y : List Bool) (pA pB pC : ℕ)
    (hA : pA ≤ y.length) (hB : pB ≤ y.length) (hC : pC ≤ y.length) :
    ∀ u : List Bool, u.length ≤ y.length →
      regs base upd u y pA pB pC =
        Fin.cons (y.drop u.length) (iter upd y pA pB pC (regs0 base y pA pB pC) u.length) :=
  List.rec (fun _ ↦ regs_nil base upd y pA pB pC) (fun b v ih hu ↦ by
    rw [List.length_cons] at hu ⊢
    funext l
    rw [regs_cons, ih (by omega)]
    refine Fin.cases (motive := fun l ↦ (foldStep upd b l).sem (envOf v
        (Fin.cons (y.drop v.length) (iter upd y pA pB pC (regs0 base y pA pB pC) v.length))
        ![y, y.drop pA, y.drop pB, y.drop pC]) =
      (Fin.cons (y.drop (v.length + 1))
        (iter upd y pA pB pC (regs0 base y pA pB pC) (v.length + 1)) :
        Fin (k + 1) → List Bool) l)
      ?_ (fun j ↦ ?_) l
    · rw [Fin.cons_zero]
      change (tailAppL idxV).sem _ = _
      rw [sem_tailAppL, idxV, sem_projL, envOf_idxSlot, Fin.cons_zero, List.tail_drop]
    · rw [Fin.cons_succ]
      change (regStep upd j).sem _ =
        updF upd y _ (nrun pA v.length y).hit (nrun pB v.length y).hit (nrun pC v.length y).hit j
      rw [regStep, sem_compL, sem_updEnv v y pA pB pC v.length hA hB hC (by omega)]
      rfl)

/-- A register after the fold over the word is the iteration over the word's
length. -/
theorem sem_bitFold (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (y : List Bool)
    (pA pB pC : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length) (hC : pC ≤ y.length) (j : Fin k) :
    (bitFold base upd j).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      iter upd y pA pB pC (regs0 base y pA pB pC) y.length j := by
  rw [bitFold, sem_compL]
  rw [show (fun i ↦ (![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3] i).sem
      ![y, y.drop pA, y.drop pB, y.drop pC]) = Fin.cons y ![y, y.drop pA, y.drop pB, y.drop pC] from
    funext fun i ↦ match i with | 0 | 1 | 2 | 3 | 4 => rfl]
  have h := congrFun (regs_eq base upd y pA pB pC hA hB hC y (Nat.le_refl _)) j.succ
  rw [Fin.cons_succ] at h
  exact h

end

end Geb.SizeBounded.Logspace.WTree.BitFold
