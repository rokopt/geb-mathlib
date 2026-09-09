/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.Machine
public import Mathlib.Logic.Function.Basic

set_option doc.verso true

/-!
# Configurations at delta-decoder phase boundaries

The binary fields are finite words with fixed marked origins. During cleanup a
field is truncated at the head position; this gives an explicit description of
every intermediate configuration, including when the shorter field has already
been erased.

## Main definitions

* {lit}`prefixTape` restricts a binary field to a most-significant prefix.
* {lit}`clearingCfg` describes the simultaneous erasure of two binary fields.
* {lit}`clearedCfg` describes the state after both fields are erased.

## Tags

Elias delta code, Turing machine, configuration
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Reading a split binary word selects its displayed middle digit. -/
theorem wordTape_split (lower higher : List Bool) (b : Bool) :
    wordTape (lower ++ b :: higher) (higher.length + 1 : ℕ) = some (boolEmb b) := by
  rw [wordTape_succ, List.reverse_append, List.reverse_cons, List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_reverse])]
  rw [List.length_reverse, Nat.sub_self]
  rfl

/-- Updating an existing most-significant-first digit updates precisely its tape cell. -/
theorem wordTape_update (xs : List Bool) (p : ℕ) (b : Bool) (hp : p < xs.length) :
    Function.update (wordTape xs.reverse) (p + 1 : ℕ) (some (boolEmb b)) =
      wordTape (xs.set p b).reverse := by
  funext z
  by_cases he : z = (p + 1 : ℕ)
  · subst z
    rw [Function.update_self, wordTape_succ, List.reverse_reverse,
      List.getElem?_set_self hp]
    rfl
  · rw [Function.update_of_ne he]
    unfold wordTape
    by_cases hz : z = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
    · rw [ite_eq_right hz, ite_eq_right hz]
      by_cases hzpos : 0 < z
      · rw [ite_eq_left hzpos, ite_eq_left hzpos, List.reverse_reverse,
          List.reverse_reverse, List.getElem?_set_ne (by omega)]
      · rw [ite_eq_right hzpos, ite_eq_right hzpos]

/-- Changing the middle digit of a split word writes its one corresponding tape cell. -/
theorem wordTape_update_split (lower higher : List Bool) (b b' : Bool) :
    Function.update (wordTape (lower ++ b :: higher)) (higher.length + 1 : ℕ)
      (some (boolEmb b')) = wordTape (lower ++ b' :: higher) := by
  have h := wordTape_update (higher.reverse ++ b :: lower.reverse) higher.length b'
    (by rw [List.length_append, List.length_reverse, List.length_cons]; omega)
  rw [List.set_append_right _ _ (by rw [List.length_reverse]), List.length_reverse,
    Nat.sub_self, List.set_cons_zero] at h
  simpa only [List.reverse_append, List.reverse_cons, List.reverse_reverse,
    List.append_assoc, List.singleton_append] using h

/-- Appending an input digit writes the blank immediately after the stored field. -/
theorem wordTape_cons (bs : List Bool) (b : Bool) :
    Function.update (wordTape bs) (bs.length + 1 : ℕ) (some (boolEmb b)) =
      wordTape (b :: bs) := by
  funext z
  by_cases he : z = (bs.length + 1 : ℕ)
  · subst z
    rw [Function.update_self, wordTape_succ, List.reverse_cons,
      List.getElem?_append_right (by rw [List.length_reverse]), List.length_reverse,
      Nat.sub_self]
    rfl
  · rw [Function.update_of_ne he]
    unfold wordTape
    by_cases hz : z = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
    · rw [ite_eq_right hz, ite_eq_right hz]
      by_cases hzpos : 0 < z
      · rw [ite_eq_left hzpos, ite_eq_left hzpos, List.reverse_cons]
        by_cases hj : z.toNat - 1 < bs.length
        · rw [List.getElem?_append_left (by rwa [List.length_reverse])]
        · have hne : z.toNat - 1 ≠ bs.length := by omega
          rw [List.getElem?_eq_none (by rw [List.length_reverse]; omega),
            List.getElem?_eq_none (by
              rw [List.length_append, List.length_reverse, List.length_singleton]
              omega)]
      · rw [ite_eq_right hzpos, ite_eq_right hzpos]

/-- A marked tape containing at most the first {lit}`p` most-significant digits. -/
def prefixTape (bs : List Bool) (p : ℕ) : ℤ → Option (Fin 3) :=
  wordTape ((bs.reverse.take p).reverse)

/-- A prefix tape always retains its origin marker. -/
theorem prefixTape_zero (bs : List Bool) (p : ℕ) : prefixTape bs p 0 = some 2 := rfl

/-- Removing all digits leaves only the origin marker. -/
theorem prefixTape_empty (bs : List Bool) : prefixTape bs 0 = wordTape [] := rfl

/-- Keeping at least the full width retains every digit. -/
theorem prefixTape_full (bs : List Bool) {p : ℕ} (h : bs.length ≤ p) :
    prefixTape bs p = wordTape bs := by
  unfold prefixTape
  rw [List.take_of_length_le (by rwa [List.length_reverse]), List.reverse_reverse]

/-- The cell erased at a positive position is never an origin marker. -/
theorem prefixTape_succ_ne_marker (bs : List Bool) (p : ℕ) :
    prefixTape bs (p + 1) (p + 1 : ℕ) ≠ some 2 := by
  unfold prefixTape
  rw [wordTape_succ, List.reverse_reverse]
  cases (bs.reverse.take (p + 1))[p]? with
  | none => exact (by decide)
  | some b => cases b <;> exact (by decide)

/-- The current cell is an origin marker exactly when the head position is zero. -/
theorem prefixTape_marker (bs : List Bool) (p : ℕ) :
    (prefixTape bs p (p : ℤ) == some 2) = decide (p = 0) := by
  cases p with
  | zero => rfl
  | succ p =>
    change (prefixTape bs (p + 1) (p + 1 : ℕ) == some 2) = false
    unfold prefixTape
    rw [wordTape_succ, List.reverse_reverse]
    cases (bs.reverse.take (p + 1))[p]? with
    | none => rfl
    | some b => cases b <;> rfl

/-- Erasing the current positive cell shortens a prefix tape by one position. -/
theorem prefixTape_erase (bs : List Bool) (p : ℕ) :
    Function.update (prefixTape bs (p + 1)) (p + 1 : ℕ) none = prefixTape bs p := by
  funext z
  by_cases he : z = (p + 1 : ℕ)
  · subst z
    rw [Function.update_self]
    unfold prefixTape
    rw [wordTape_succ, List.reverse_reverse,
      List.getElem?_take_eq_none (Nat.le_refl p)]
    rfl
  · rw [Function.update_of_ne he]
    unfold prefixTape wordTape
    by_cases hz : z = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
    · rw [ite_eq_right hz, ite_eq_right hz]
      by_cases hp : 0 < z
      · rw [ite_eq_left hp, ite_eq_left hp, List.reverse_reverse, List.reverse_reverse,
          List.getElem?_take, List.getElem?_take]
        have hn : z.toNat - 1 ≠ p := by omega
        by_cases hj : z.toNat - 1 < p
        · rw [ite_eq_left (by omega), ite_eq_left hj]
        · rw [ite_eq_right (by omega), ite_eq_right hj]
      · rw [ite_eq_right hp, ite_eq_right hp]

/-- The binary fields after each has erased down to its current head position. -/
def clearingCfg {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) : Cfg 4 (Fin 3) Control input where
  state := some stClear
  inputPos := cfg.inputPos
  workTapes i :=
    if i = 2 then prefixTape bs p
    else if i = 3 then prefixTape cs r
    else cfg.workTapes i
  workTapePos i := if i = 2 then p else if i = 3 then r else cfg.workTapePos i

/-- Erasure finishes with both heads ready to append a fresh binary field. -/
def clearedCfg {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input) :
    Cfg 4 (Fin 3) Control input where
  state := some stLeaf
  inputPos := cfg.inputPos
  workTapes i := if i = 2 ∨ i = 3 then wordTape [] else cfg.workTapes i
  workTapePos i :=
    if i = 0 then cfg.workTapePos 0 - 1
    else if i = 1 then cfg.workTapePos 1
    else 1

/-- Completing a leaf selects the next constructor or the end-of-tree state. -/
def completedCfg {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input) :
    Cfg 4 (Fin 3) Control input :=
  { clearedCfg cfg with
    state := some (if cfg.workTapes 0 (cfg.workTapePos 0 - 1) == some 2 then stDone else stTree) }

/-- Replacing a counter configuration preserves a bound containing its selected head. -/
theorem headBound_counterCfg {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs : List Bool) (q : Control) (p width : ℕ)
    (hcfg : HeadBound width cfg) (hp : p ≤ width) :
    HeadBound width (counterCfg cfg v bs q p) := by
  intro i
  by_cases hi : i = counterTape v
  · simp only [counterCfg, hi, ite_true]
    exact ⟨by omega, by exact_mod_cast hp⟩
  · simpa only [counterCfg, hi, ite_false] using hcfg i

end Geb.BitTree.Elias.Machine
