/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Tapes

set_option doc.verso true

/-!
# The two-pass tree scanner's closed forms

The configurations {name}`Geb.BitTreeScanner.bitTreeScanner`'s runs pass
through, as closed forms: the configuration a step lands on given the
transition's actions, the intermediate closed forms of each chain, and the
bound every head keeps to, three cells above the input length's digit
count, with the proof that each closed form keeps to it.

## Main definitions

* {lit}`Geb.BitTreeScanner.applyAct`, {lit}`Geb.BitTreeScanner.next` — a work
  tape's action applied, and the configuration a step lands on.
* {lit}`Geb.BitTreeScanner.headBound`, {lit}`Geb.BitTreeScanner.HeadsLE` — the
  cell every head stays at or below, and a configuration's heads within it.
* {lit}`Geb.BitTreeScanner.seekCarryCfg`, {lit}`Geb.BitTreeScanner.seekBackCfg`
  — the closed forms of a carry of the input's count and of its return.
* {lit}`Geb.BitTreeScanner.incCarryCfg`, {lit}`Geb.BitTreeScanner.incBackCfg`
  — the closed forms of a carry of the pending count and of its return.
* {lit}`Geb.BitTreeScanner.decBorrowCfg`, {lit}`Geb.BitTreeScanner.decTape`,
  {lit}`Geb.BitTreeScanner.decTopCfg`, {lit}`Geb.BitTreeScanner.decEraseCfg`,
  {lit}`Geb.BitTreeScanner.decBackCfg`, {lit}`Geb.BitTreeScanner.mainCfg` —
  the closed forms of a borrow of the pending count, the test above the
  lowered digit, its erasure, the return, and the configuration expecting the
  next tree the return ends in.
* {lit}`Geb.BitTreeScanner.borrowState`, {lit}`Geb.BitTreeScanner.returnState`
  — the borrowing and returning states of either decrement phase of the
  leaf's count.
* {lit}`Geb.BitTreeScanner.borrowCfg`, {lit}`Geb.BitTreeScanner.returnCfg`,
  {lit}`Geb.BitTreeScanner.clearCfg` — the closed forms of a borrow of the
  leaf's count, its return, and the erasure after a failed one.

## Main statements

* {lit}`Geb.BitTreeScanner.headsLE_cfgAt` and the other {lit}`headsLE_` lemmas
  — every closed form keeps its heads within the bound.
* {lit}`Geb.BitTreeScanner.cfgAt_count`, {lit}`Geb.BitTreeScanner.clearCfg_zero`,
  {lit}`Geb.BitTreeScanner.mainCfg_eq_cfgAt` — the closed forms a chain
  begins or ends at are the scan's closed forms.

## Implementation notes

The head bounds are stated as pairs of inequalities and proved a side at a
time, since {lit}`omega` closing a conjunction depends on
{lit}`Classical.choice` and the module is held to the standard axiom set.

## Tags

Turing machine, configuration, closed form, space bound
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Step

variable {input : List (Fin 4)}

/-- Two triples are equal when their components are. -/
theorem vec3_ext {α : Type} {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁)
    (h₂ : a₂ = b₂) : ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by
  rw [h₀, h₁, h₂]

/-- A work tape's action applied to its content at its head: the write, if
any. -/
def applyAct (a : Act) (t : ℤ → Option (Fin 4)) (p : ℤ) : ℤ → Option (Fin 4) :=
  match a.1 with
  | none => t
  | some x => Function.update t p x

/-- The configuration a step lands on, given the successor state, the input
head's move and the tapes' actions. -/
def next (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q' : Fin stateCount) (m : SignType)
    (a₀ a₁ a₂ : Act) : Cfg 3 (Fin 4) (Fin stateCount) input where
  state := some q'
  inputPos := moveInputPos cfg.inputPos m
  workTapes := ![applyAct a₀ (cfg.workTapes 0) (cfg.workTapePos 0),
    applyAct a₁ (cfg.workTapes 1) (cfg.workTapePos 1),
    applyAct a₂ (cfg.workTapes 2) (cfg.workTapePos 2)]
  workTapePos := ![cfg.workTapePos 0 + (a₀.2 : ℤ), cfg.workTapePos 1 + (a₁.2 : ℤ),
    cfg.workTapePos 2 + (a₂.2 : ℤ)]

end Step

section Heads

variable (w : List Bool)

/-- The cell every head stays at or below: three above the bound. -/
def headBound : ℤ := bound w + 3

/-- A configuration's heads are within the bound: each at a cell from
{lit}`0` to {name}`headBound`. -/
def HeadsLE (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) : Prop :=
  ∀ i, 0 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ headBound w

/-- The heads of a configuration given by its fields are within the bound
when each is. -/
theorem headsLE_mk (st : Option (Fin stateCount)) (pos : Fin ((w.map boolEmb).length + 2))
    (tapes : Fin 3 → ℤ → Option (Fin 4)) (p₀ p₁ p₂ : ℤ) (h₀ : 0 ≤ p₀ ∧ p₀ ≤ headBound w)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ headBound w) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ headBound w) :
    HeadsLE w
      { state := st, inputPos := pos, workTapes := tapes, workTapePos := ![p₀, p₁, p₂] } := by
  intro i
  match i with
  | 0 => exact h₀
  | 1 => exact h₁
  | 2 => exact h₂

/-- The heads of the initial configuration are within the bound. -/
theorem headsLE_initCfg : HeadsLE w (bitTreeScanner.initCfg (w.map boolEmb)) := fun i ↦ by
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ headBound w
  rw [headBound]
  exact ⟨by omega, by omega⟩

/-- The heads of the scan's initial closed form are within the bound. -/
theorem headsLE_cfgAt_init : HeadsLE w (cfgAt w 0 (Nat.zero_le _) init []) :=
  headsLE_mk w _ _ _ 1 0 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of the return's closed form are within the bound. -/
theorem headsLE_backCfg (i : ℕ) (hi : i ≤ w.length) : HeadsLE w (backCfg w i hi) :=
  headsLE_mk w _ _ _ 1 0 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

end Heads

section Scan

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length)

/-- The closed form's heads are within the bound at any state satisfying the
invariant. -/
theorem headsLE_cfgAt (s : Scan) (hs : Good (bound w) s) (l : List Redundant.Digit) :
    HeadsLE w (cfgAt w k hk s l) := by
  obtain ⟨m, c, wd, d⟩ := s
  refine headsLE_mk w _ _ _ 1 (headLeaf ⟨m, c, wd, d⟩) (headRuler ⟨m, c, wd, d⟩)
    ⟨by omega, by rw [headBound]; omega⟩ ?_ ?_ <;> cases m <;> dsimp only [Good] at hs
  · rw [headLeaf_term, headBound]; exact ⟨by omega, by omega⟩
  · rw [headLeaf_zeros, headBound]; exact ⟨by omega, by omega⟩
  · rw [headLeaf_bits, headBound]; exact ⟨by omega, by omega⟩
  · rw [headLeaf_count, headBound]; exact ⟨by omega, by omega⟩
  · rw [headLeaf_done, headBound]; exact ⟨by omega, by omega⟩
  · rw [headLeaf_dead, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_term, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_zeros, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_bits, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_count, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_done, headBound]; exact ⟨by omega, by omega⟩
  · rw [headRuler_dead, headBound]; exact ⟨by omega, by omega⟩

/-- The closed form's heads are within the bound while reading the digits,
the digits complete or not. -/
theorem headsLE_cfgAt_bits (c wd : ℕ) (d : List Bool) (hle : d.length ≤ wd)
    (hw : wd ≤ bound w + 2) (l : List Redundant.Digit) :
    HeadsLE w (cfgAt w k hk ⟨.bits, c, wd, d⟩ l) :=
  headsLE_mk w _ _ _ 1 (headLeaf ⟨.bits, c, wd, d⟩) (headRuler ⟨.bits, c, wd, d⟩)
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by rw [headLeaf_bits]; omega, by rw [headLeaf_bits, headBound]; omega⟩
    ⟨by rw [headRuler_bits]; omega, by rw [headRuler_bits, headBound]; omega⟩

end Scan

section Seek

variable (w : List Bool) (i : ℕ) (hi : i ≤ w.length)

/-- The configuration {lit}`j` cells into a carry of the count: the digits
below cell {lit}`j` turned to zeros, the head at cell {lit}`j + 1`. -/
def seekCarryCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stSeekCarry
  inputPos := ⟨i + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount [], tapeDigits [],
    fun z ↦ if 1 ≤ z ∧ z ≤ j then some 0 else tapeDigits i.bits z]
  workTapePos := ![1, 0, (j : ℤ) + 1]

/-- The configuration returning from a carry of the count, at cell
{lit}`j`: the count incremented, the head at cell {lit}`j`. -/
def seekBackCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stSeekBack
  inputPos := ⟨i + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount [], tapeDigits [], tapeDigits (i + 1).bits]
  workTapePos := ![1, 0, (j : ℤ)]

/-- The count's digits are within the bound. -/
theorem bits_length_le_headBound (hi : i ≤ w.length) : (i.bits.length : ℤ) + 1 ≤ headBound w := by
  have := bits_length_mono hi
  rw [headBound, bound]
  omega

/-- The heads of the counting pass's closed form are within the bound. -/
theorem headsLE_seekCfg : HeadsLE w (seekCfg w i hi) :=
  headsLE_mk w _ _ _ 1 0 1 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of a carry's closed form are within the bound. -/
theorem headsLE_seekCarryCfg (j : ℕ) (hj : j ≤ carryLengthB i.bits) :
    HeadsLE w (seekCarryCfg w i hi j) :=
  headsLE_mk w _ _ _ 1 0 ((j : ℤ) + 1) ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by
      have := bits_length_le_headBound w i hi
      have := carryLengthB_le_length i.bits
      omega⟩

/-- The heads of a carry's return are within the bound. -/
theorem headsLE_seekBackCfg (j : ℕ) (hj : j ≤ carryLengthB i.bits) :
    HeadsLE w (seekBackCfg w i hi j) :=
  headsLE_mk w _ _ _ 1 0 (j : ℤ) ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by
      have := bits_length_le_headBound w i hi
      have := carryLengthB_le_length i.bits
      omega⟩

end Seek

section Inc

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (c : ℕ) (l : List Redundant.Digit)

/-- The configuration {lit}`j` cells into a carry of the pending count: the
digits below cell {lit}`j` turned to ones, the head at cell {lit}`j + 1`. -/
def incCarryCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stIncCarry
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![fun z ↦ if 1 ≤ z ∧ z ≤ j then some 1 else tapeCount l z, tapeBase,
    tapeDigits w.length.bits]
  workTapePos := ![(j : ℤ) + 1, 0, 0]

/-- The configuration returning from a carry of the pending count, at cell
{lit}`j`: the count incremented, the head at cell {lit}`j`. -/
def incBackCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stIncBack
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount (Redundant.inc l), tapeBase, tapeDigits w.length.bits]
  workTapePos := ![(j : ℤ), 0, 0]

/-- The heads of the closed form at a state expecting a tree are within the
bound. -/
theorem headsLE_cfgAt_term : HeadsLE w (cfgAt w k hk ⟨.term, c, 0, []⟩ l) :=
  headsLE_mk w _ _ _ 1 0 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of a carry's closed form are within the bound. -/
theorem headsLE_incCarryCfg (hl : l.length ≤ bound w) (j : ℕ) (hj : j ≤ Redundant.carryLength l) :
    HeadsLE w (incCarryCfg w k hk l j) :=
  headsLE_mk w _ _ _ ((j : ℤ) + 1) 0 0
    ⟨by omega, by have := Redundant.carryLength_le_length l; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of a carry's return are within the bound. -/
theorem headsLE_incBackCfg (hl : l.length ≤ bound w) (j : ℕ) (hj : j ≤ Redundant.carryLength l) :
    HeadsLE w (incBackCfg w k hk l j) :=
  headsLE_mk w _ _ _ (j : ℤ) 0 0
    ⟨by omega, by have := Redundant.carryLength_le_length l; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The closed form at a state expecting a tree reads the pending count's
lowest digit. -/
theorem workTapeSymbols_cfgAt_term :
    (cfgAt w k hk ⟨.term, c, 0, []⟩ l).workTapeSymbols = ![tapeCount l 1, some 3, some 3] := by
  rw [workTapeSymbols_eq]
  rfl

end Inc

section Dec

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- The configuration {lit}`j` cells into a borrow of the pending count: the
digits below cell {lit}`j` turned to ones, the head at cell {lit}`j + 1`. At
cell {lit}`0` it is the configuration the leaf's erasure ends in, whose
state is the erasing one. -/
def decBorrowCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some (if j = 0 then stClear else stDecBorrow)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![fun z ↦ if 1 ≤ z ∧ z ≤ j then some 1 else tapeCount l z, tapeBase,
    tapeDigits w.length.bits]
  workTapePos := ![(j : ℤ) + 1, 0, 0]

/-- The count tape after a borrow absorbed at a one, which is lowered to a
zero, before the test for its being the top. -/
def decTape (z : ℤ) : Option (Fin 4) :=
  if 1 ≤ z ∧ z ≤ Redundant.borrowLength l then some 1
  else if z = Redundant.borrowLength l + 1 then some 0 else tapeCount l z

/-- The configuration testing whether the lowered digit was the top: the
head above it. -/
def decTopCfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stDecTop
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![decTape l, tapeBase, tapeDigits w.length.bits]
  workTapePos := ![(Redundant.borrowLength l : ℤ) + 2, 0, 0]

/-- The configuration erasing the lowered top digit: the head at it. -/
def decEraseCfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stDecErase
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![decTape l, tapeBase, tapeDigits w.length.bits]
  workTapePos := ![(Redundant.borrowLength l : ℤ) + 1, 0, 0]

/-- The configuration returning from a borrow of the pending count, at cell
{lit}`j`: the count decremented, the head at cell {lit}`j`. -/
def decBackCfg (j : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stDecBack
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount (Redundant.dec l), tapeBase, tapeDigits w.length.bits]
  workTapePos := ![(j : ℤ), 0, 0]

/-- The heads of a borrow's closed form are within the bound. -/
theorem headsLE_decBorrowCfg (hl : l.length ≤ bound w) (j : ℕ)
    (hj : j ≤ Redundant.borrowLength l) : HeadsLE w (decBorrowCfg w k hk l j) :=
  headsLE_mk w _ _ _ ((j : ℤ) + 1) 0 0
    ⟨by omega, by have := Redundant.borrowLength_le_length l; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of the top test are within the bound. -/
theorem headsLE_decTopCfg (hn : Redundant.nlz l = true) (h : l ≠ []) (hl : l.length ≤ bound w) :
    HeadsLE w (decTopCfg w k hk l) :=
  headsLE_mk w _ _ _ ((Redundant.borrowLength l : ℤ) + 2) 0 0
    ⟨by omega, by have := borrowLength_lt_length_of_nlz l hn h; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of the erasure are within the bound. -/
theorem headsLE_decEraseCfg (hl : l.length ≤ bound w) : HeadsLE w (decEraseCfg w k hk l) :=
  headsLE_mk w _ _ _ ((Redundant.borrowLength l : ℤ) + 1) 0 0
    ⟨by omega, by have := Redundant.borrowLength_le_length l; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of a borrow's return are within the bound. -/
theorem headsLE_decBackCfg (hl : l.length ≤ bound w) (j : ℕ)
    (hj : j ≤ Redundant.borrowLength l + 1) : HeadsLE w (decBackCfg w k hk l j) :=
  headsLE_mk w _ _ _ (j : ℤ) 0 0
    ⟨by omega, by have := Redundant.borrowLength_le_length l; rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩ ⟨by omega, by rw [headBound]; omega⟩

/-- The borrow's family reads the cell above the ones. -/
theorem workTapeSymbols_decBorrowCfg (j : ℕ) :
    (decBorrowCfg w k hk l j).workTapeSymbols = ![tapeCount l ((j : ℤ) + 1), some 3, some 3] := by
  rw [workTapeSymbols_eq]
  change ![if 1 ≤ ((j : ℤ) + 1) ∧ ((j : ℤ) + 1) ≤ j then some 1 else tapeCount l ((j : ℤ) + 1),
    tapeBase 0, tapeDigits w.length.bits 0] = _
  rw [ite_eq_right (by omega)]
  rfl

/-- The configuration expecting the next tree at a count, with the leaf tape
holding the base marker alone. -/
def mainCfg (l : List Redundant.Digit) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stMain
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount l, tapeBase, tapeDigits w.length.bits]
  workTapePos := ![1, 0, 0]

/-- The heads of the configuration expecting the next tree are within the
bound. -/
theorem headsLE_mainCfg (l : List Redundant.Digit) : HeadsLE w (mainCfg w k hk l) :=
  headsLE_mk w _ _ _ 1 0 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The configuration expecting the next tree is the closed form at the
state expecting a tree. -/
theorem mainCfg_eq_cfgAt (c : ℕ) (l : List Redundant.Digit) :
    mainCfg w k hk l = cfgAt w k hk ⟨.term, c, 0, []⟩ l := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext j
  match j with
  | 0 => rfl
  | 1 => exact (tapeLeaf_blank ⟨.term, c, 0, []⟩ (Or.inl rfl)).symm
  | 2 => rfl

end Dec

section Leaf

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- The borrowing state of a decrement of the leaf's count: the first
decrement's or a payload bit's. -/
def borrowState (first : Bool) : Fin stateCount := cond first stBorrowInit stBorrow

/-- The returning state of a decrement of the leaf's count: the first
decrement's or a payload bit's. -/
def returnState (first : Bool) : Fin stateCount := cond first stReturnInit stReturn

/-- The configuration {lit}`i` cells into a borrow over the digits {lit}`d`: the
digits below cell {lit}`i` turned to ones, the head at cell {lit}`i + 1`. At
{lit}`i = 0`, the configuration at the lowest digit that begins the
decrement. -/
def borrowCfg (first : Bool) (d : List Bool) (i : ℕ) :
    Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some (borrowState first)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount l, fun z ↦ if 1 ≤ z ∧ z ≤ i then some 1 else tapeDigits d z,
    tapeDigits w.length.bits]
  workTapePos := ![1, (i : ℤ) + 1, 0]

/-- The configuration returning from a borrow over the digits {lit}`d`, at
cell {lit}`i`: the digits decremented, the head at cell {lit}`i`. -/
def returnCfg (first : Bool) (d : List Bool) (i : ℕ) :
    Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some (returnState first)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount l, tapeDigits (decList d), tapeDigits w.length.bits]
  workTapePos := ![1, (i : ℤ), 0]

/-- The heads of a borrow's closed form are within the bound. -/
theorem headsLE_borrowCfg (first : Bool) (d : List Bool) (hd : d.length ≤ bound w + 2) (i : ℕ)
    (hi : i ≤ d.length) : HeadsLE w (borrowCfg w k hk l first d i) :=
  headsLE_mk w _ _ _ 1 ((i : ℤ) + 1) 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The heads of a return's closed form are within the bound. -/
theorem headsLE_returnCfg (first : Bool) (d : List Bool) (hd : d.length ≤ bound w + 2) (i : ℕ)
    (hi : i ≤ d.length) : HeadsLE w (returnCfg w k hk l first d i) :=
  headsLE_mk w _ _ _ 1 (i : ℤ) 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The borrow's family reads the cell above the ones. -/
theorem workTapeSymbols_borrowCfg (first : Bool) (d : List Bool) (i : ℕ) :
    (borrowCfg w k hk l first d i).workTapeSymbols =
      ![tapeCount l 1, tapeDigits d ((i : ℤ) + 1), some 3] := by
  rw [workTapeSymbols_eq]
  change ![tapeCount l 1, if 1 ≤ ((i : ℤ) + 1) ∧ ((i : ℤ) + 1) ≤ i then some 1
    else tapeDigits d ((i : ℤ) + 1), tapeDigits w.length.bits 0] = _
  rw [ite_eq_right (show ¬(1 ≤ ((i : ℤ) + 1) ∧ ((i : ℤ) + 1) ≤ i) by omega)]
  rfl

/-- The configuration erasing the digits after a decrement found the count at
zero, at cell {lit}`i`: the digits below it still ones, those above it blank,
the head at cell {lit}`i`. -/
def clearCfg (i : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stClear
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount l, fun z ↦ if 1 ≤ z ∧ z ≤ i then some 1 else tapeBase z,
    tapeDigits w.length.bits]
  workTapePos := ![1, (i : ℤ), 0]

/-- The heads of the erasure's closed form are within the bound. -/
theorem headsLE_clearCfg (i : ℕ) (hi : i ≤ bound w + 2) : HeadsLE w (clearCfg w k hk l i) :=
  headsLE_mk w _ _ _ 1 (i : ℤ) 0 ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩
    ⟨by omega, by rw [headBound]; omega⟩

/-- The erasure's end is the configuration the pending count's decrement
begins from. -/
theorem clearCfg_zero : clearCfg w k hk l 0 = decBorrowCfg w k hk l 0 := by
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change tapeCount l z = if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeCount l z
      rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega)]
    | 1 =>
      change (if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeBase z) = tapeBase z
      rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega)]
    | 2 => rfl
  · rfl

/-- The closed form in the countdown is the configuration at the lowest digit
that begins a decrement. -/
theorem cfgAt_count (c wd : ℕ) (d : List Bool) :
    cfgAt w k hk ⟨.count, c, wd, d⟩ l = borrowCfg w k hk l false d 0 := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext j z
  match j with
  | 0 => rfl
  | 1 =>
    change tapeLeaf ⟨.count, c, wd, d⟩ z =
      if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits d z
    rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega), tapeLeaf, tapeDigits]
  | 2 => rfl

end Leaf

end Geb.BitTreeScanner
