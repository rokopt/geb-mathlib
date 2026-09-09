/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Machine

set_option doc.verso true

/-!
# The one-pass tree scanner's transition, resolved

{name}`Geb.BitTreeScanner.bitTreeScanner`'s transition resolved at each case of
its table, and the machine's configuration shown to be the closed form
{name}`Geb.BitTreeScanner.cfgOf` after each input bit's steps. Between two
consecutive closed forms the machine runs the bit's cost,
{name}`Geb.BitTreeScanner.cost`, which is one step except through a leaf's count: a
decrement borrows outward and returns, and the decrement finding the count at
zero erases the digits and leaves the leaf. Those runs are proved by inner
recursions over intermediate closed forms, and composed with the single steps
into {lit}`Geb.BitTreeScanner.configs_cfgOf`, the configuration and output at
the time each prefix is consumed. The input's end is the emitting step, whose
symbol is {name}`Geb.BitTreeScanner.validBool` at the input.

## Main definitions

* {lit}`Geb.BitTreeScanner.applyAct` — a work tape's action applied.
* {lit}`Geb.BitTreeScanner.borrowState`, {lit}`Geb.BitTreeScanner.returnState`
  — the borrowing and returning states of either decrement phase.
* {lit}`Geb.BitTreeScanner.borrowCfg`, {lit}`Geb.BitTreeScanner.returnCfg`,
  {lit}`Geb.BitTreeScanner.clearCfg` — the intermediate closed forms of a
  decrement's borrow, its return, and the erasure after a failed one.

## Main statements

* {lit}`Geb.BitTreeScanner.inputSymbol_of_inputPos`,
  {lit}`Geb.BitTreeScanner.inputSymbol_end` — the input symbol at any
  configuration whose head is past a prefix, short of the input's end and at
  it.
* {lit}`Geb.BitTreeScanner.tr_first_pair` through
  {lit}`Geb.BitTreeScanner.tr_dead_end`, and
  {lit}`Geb.BitTreeScanner.tr_borrowState_zero`,
  {lit}`Geb.BitTreeScanner.tr_borrowState_one`,
  {lit}`Geb.BitTreeScanner.tr_returnState_digit` — the transition resolved at
  each case of its table, the decrement rows at either phase.
* {lit}`Geb.BitTreeScanner.halts_at`, {lit}`Geb.BitTreeScanner.outputString_eq`
  — the machine halts after {lit}`time w + endCost (scanFinal w)` steps having
  emitted the decision function's value.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the machine's behaviour under {name}`Turing.MultiTapeTM.step`,
{name}`Turing.MultiTapeTM.configs` and {name}`Turing.MultiTapeTM.outputString`,
and its statements read the input through
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`; each of those depends on
{lit}`Classical.choice` through Cslib's {lit}`Cfg.inputSymbol` and
{name}`Turing.MultiTapeTM.inputSymbolInner`, so nothing here can be stated
choice-free.

A transition resolution is stated over an arbitrary work-symbol function
wherever the table's row does not read it, and at a pair literal where it
does, which is the form {name}`Geb.BitTreeScanner.workTapeSymbols_eq` reduces
to. A row that is a catch-all in the input column or reads a digit is
resolved at {lit}`some (boolEmb b)` by cases on the bit.

## Tags

Turing machine, transition, tree, prefix code, binary counter
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner
open Geb.TreeScanner (step_of_state)

section InputSymbol

/-- A configuration whose input head is past a prefix short of the input's end
reads the bit at the prefix's length. -/
theorem inputSymbol_of_inputPos (w : List Bool) (k : ℕ) (h : k < w.length)
    (cfg : Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb)) (hpos : cfg.inputPos.val = k + 1) :
    cfg.inputSymbol = some (boolEmb w[k]) := by
  have hi := inputSymbolInner (cfg := cfg) k (by rw [hpos]; omega)
    (by rw [List.length_map]; exact h)
  rw [hi, List.getElem_map]

/-- A configuration whose input head is past the whole input reads blank. This
takes {name}`Turing.MultiTapeTM.Cfg.inputSymbol`'s second guard, an equality at
{lit}`ℕ`. -/
theorem inputSymbol_end (w : List Bool) (cfg : Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb))
    (hpos : cfg.inputPos.val = w.length + 1) : cfg.inputSymbol = none := by
  have hend : (cfg.inputPos : ℕ) = (w.map boolEmb).length + 1 := by
    rw [hpos, List.length_map]
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

end InputSymbol

section Transition

variable (work : Fin 2 → Option (Fin 4)) (t₀ : Option (Fin 4)) (inSym : Option (Fin 4))

/-- The first step over a pair bit writes both markers and moves the count
head right. -/
theorem tr_first_pair :
    bitTreeScanner.tr stFirst (some (boolEmb true)) work =
      advance stMain (some (some 0), 1) (some (some 3), 0) := rfl

/-- The first step over a leaf bit writes both markers and moves the digit
head to the first digit cell. -/
theorem tr_first_leaf :
    bitTreeScanner.tr stFirst (some (boolEmb false)) work =
      advance stZeros (some (some 0), 0) (some (some 3), 1) := rfl

/-- The first step at the input's end rejects. -/
theorem tr_first_end : bitTreeScanner.tr stFirst none work = halt 0 := rfl

/-- A pair bit in the main state moves the count head right. -/
theorem tr_main_pair :
    bitTreeScanner.tr stMain (some (boolEmb true)) work = advance stMain (none, 1) idle := rfl

/-- A leaf bit in the main state moves the digit head to the first digit
cell. -/
theorem tr_main_leaf :
    bitTreeScanner.tr stMain (some (boolEmb false)) work = advance stZeros idle (none, 1) := rfl

/-- The main state at the input's end rejects. -/
theorem tr_main_end : bitTreeScanner.tr stMain none work = halt 0 := rfl

/-- A zero of the gamma code writes a mark and moves the digit head right. -/
theorem tr_zeros_zero :
    bitTreeScanner.tr stZeros (some (boolEmb false)) work =
      advance stZeros idle (some (some 2), 1) := rfl

/-- The one of the gamma code writes the most significant digit and moves the
digit head left. -/
theorem tr_zeros_one :
    bitTreeScanner.tr stZeros (some (boolEmb true)) work =
      advance stBits idle (some (some 1), -1) := rfl

/-- The zeros state at the input's end rejects. -/
theorem tr_zeros_end : bitTreeScanner.tr stZeros none work = halt 0 := rfl

/-- A digit of the gamma code over a mark is written and the digit head moves
left. -/
theorem tr_bits_mark (b : Bool) :
    bitTreeScanner.tr stBits (some (boolEmb b)) ![t₀, some 2] =
      advance stBits idle (some (some (boolEmb b)), -1) := rfl

/-- The digits state over a mark at the input's end rejects. -/
theorem tr_bits_mark_end : bitTreeScanner.tr stBits none ![t₀, some 2] = halt 0 := rfl

/-- The digits state at the base marker: the digits are complete, and the
head moves to the lowest to begin the first decrement. -/
theorem tr_bits_base :
    bitTreeScanner.tr stBits inSym ![t₀, some 3] = stay stBorrowInit idle (none, 1) := rfl

/-- The first decrement's return reaches the base marker and steps to the
lowest digit, where the countdown begins. -/
theorem tr_returnInit_base :
    bitTreeScanner.tr stReturnInit inSym ![t₀, some 3] = stay stBorrow idle (none, 1) := rfl

/-- A decrement running into blank found the count at zero and turns back to
erase. -/
theorem tr_borrow_blank :
    bitTreeScanner.tr stBorrow inSym ![t₀, none] = stay stClear idle (none, -1) := rfl

/-- A decrement's return reaches the base marker and consumes the payload bit,
stepping to the lowest digit. -/
theorem tr_return_base_bit (b : Bool) :
    bitTreeScanner.tr stReturn (some (boolEmb b)) ![t₀, some 3] =
      advance stBorrow idle (none, 1) := by
  cases b <;> rfl

/-- A decrement's return reaching the base marker at the input's end rejects. -/
theorem tr_return_base_end : bitTreeScanner.tr stReturn none ![t₀, some 3] = halt 0 := rfl

/-- Erasure blanks a digit and moves left. -/
theorem tr_clear_digit (b : Bool) :
    bitTreeScanner.tr stClear inSym ![t₀, some (boolEmb b)] =
      stay stClear idle (some none, -1) := by
  cases b <;> rfl

/-- Erasure reaching the base marker under the count marker closes the last
pending tree: the scan completes. -/
theorem tr_clear_base_last :
    bitTreeScanner.tr stClear inSym ![some 0, some 3] = stay stDone idle idle := rfl

/-- Erasure reaching the base marker over a blank count cell closes the leaf
and moves the count head left: the next tree is expected. -/
theorem tr_clear_base :
    bitTreeScanner.tr stClear inSym ![none, some 3] = stay stMain (none, -1) idle := rfl

/-- A bit after completion fails. -/
theorem tr_done_bit (b : Bool) :
    bitTreeScanner.tr stDone (some (boolEmb b)) work = advance stDead idle idle := by
  cases b <;> rfl

/-- Completion at the input's end accepts. -/
theorem tr_done_end : bitTreeScanner.tr stDone none work = halt 1 := rfl

/-- Failure absorbs a bit. -/
theorem tr_dead_bit (b : Bool) :
    bitTreeScanner.tr stDead (some (boolEmb b)) work = advance stDead idle idle := by
  cases b <;> rfl

/-- Failure at the input's end rejects. -/
theorem tr_dead_end : bitTreeScanner.tr stDead none work = halt 0 := rfl

end Transition

section Step

variable {input : List (Fin 4)}

/-- A work tape's action applied to its content at its head: the write, if
any. -/
def applyAct (a : Act) (t : ℤ → Option (Fin 4)) (p : ℤ) : ℤ → Option (Fin 4) :=
  match a.1 with
  | none => t
  | some x => Function.update t p x

/-- A step whose transition reads a bit: the input head advances, each tape
takes its action, nothing is emitted. -/
theorem step_advance (cfg : Cfg 2 (Fin 4) (Fin 11) input) (q q' : Fin 11) (a₀ a₁ : Act)
    (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = advance q' a₀ a₁) :
    bitTreeScanner.step cfg =
      { state := some q', inputPos := moveInputPos cfg.inputPos 1,
        workTapes := ![applyAct a₀ (cfg.workTapes 0) (cfg.workTapePos 0),
          applyAct a₁ (cfg.workTapes 1) (cfg.workTapePos 1)],
        workTapePos := ![cfg.workTapePos 0 + (a₀.2 : ℤ), cfg.workTapePos 1 + (a₁.2 : ℤ)] } ∧
      bitTreeScanner.outputSymbol cfg = none := by
  obtain ⟨o₀, m₀⟩ := a₀
  obtain ⟨o₁, m₁⟩ := a₁
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    refine Cfg.ext rfl rfl ?_ ?_
    · funext i
      match i with
      | 0 => cases o₀ <;> rfl
      | 1 => cases o₁ <;> rfl
    · funext i
      match i with
      | 0 => rfl
      | 1 => rfl
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = none
    rw [htr]
    rfl

/-- A step whose transition works without reading: the input head stays, each
tape takes its action, nothing is emitted. -/
theorem step_stay (cfg : Cfg 2 (Fin 4) (Fin 11) input) (q q' : Fin 11) (a₀ a₁ : Act)
    (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = stay q' a₀ a₁) :
    bitTreeScanner.step cfg =
      { state := some q', inputPos := cfg.inputPos,
        workTapes := ![applyAct a₀ (cfg.workTapes 0) (cfg.workTapePos 0),
          applyAct a₁ (cfg.workTapes 1) (cfg.workTapePos 1)],
        workTapePos := ![cfg.workTapePos 0 + (a₀.2 : ℤ), cfg.workTapePos 1 + (a₁.2 : ℤ)] } ∧
      bitTreeScanner.outputSymbol cfg = none := by
  obtain ⟨o₀, m₀⟩ := a₀
  obtain ⟨o₁, m₁⟩ := a₁
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
    · funext i
      match i with
      | 0 => cases o₀ <;> rfl
      | 1 => cases o₁ <;> rfl
    · funext i
      match i with
      | 0 => rfl
      | 1 => rfl
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = none
    rw [htr]
    rfl

/-- A step whose transition resolves to a halting step halts the machine and
emits the halting step's symbol. -/
theorem step_halt (cfg : Cfg 2 (Fin 4) (Fin 11) input) (q : Fin 11) (hq : cfg.state = some q)
    (b : Fin 4) (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = halt b) :
    (bitTreeScanner.step cfg).state = none ∧ bitTreeScanner.outputSymbol cfg = some b := by
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    rfl
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = some b
    rw [htr]
    rfl

/-- A run of one step: the step's configuration, and nothing emitted. -/
theorem run_step (cfg₁ cfg₂ : Cfg 2 (Fin 4) (Fin 11) input)
    (h : bitTreeScanner.step cfg₁ = cfg₂ ∧ bitTreeScanner.outputSymbol cfg₁ = none) :
    bitTreeScanner.configs cfg₁ 1 = cfg₂ ∧ bitTreeScanner.outputString cfg₁ 1 = [] := by
  refine ⟨h.1, ?_⟩
  change bitTreeScanner.outputString cfg₁ (0 + 1) = []
  rw [outputString_succ, configs_zero, h.2]
  rfl

/-- Two runs in sequence: the second's configuration, and nothing emitted. -/
theorem run_seq (cfg₁ cfg₂ cfg₃ : Cfg 2 (Fin 4) (Fin 11) input) (m n : ℕ)
    (h₁ : bitTreeScanner.configs cfg₁ m = cfg₂ ∧ bitTreeScanner.outputString cfg₁ m = [])
    (h₂ : bitTreeScanner.configs cfg₂ n = cfg₃ ∧ bitTreeScanner.outputString cfg₂ n = []) :
    bitTreeScanner.configs cfg₁ (m + n) = cfg₃ ∧
      bitTreeScanner.outputString cfg₁ (m + n) = [] := by
  refine ⟨by rw [configs_add, h₁.1, h₂.1], ?_⟩
  rw [outputString_add_eq_append, h₁.2, h₁.1, h₂.2]
  rfl

end Step

section Borrow

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length)

/-- The borrowing state of a decrement: the first decrement's or a payload
bit's. -/
def borrowState (first : Bool) : Fin 11 := cond first stBorrowInit stBorrow

/-- The returning state of a decrement: the first decrement's or a payload
bit's. -/
def returnState (first : Bool) : Fin 11 := cond first stReturnInit stReturn

/-- A decrement borrows through a zero, in either phase. -/
theorem tr_borrowState_zero (first : Bool) (t₀ : Option (Fin 4)) (inSym : Option (Fin 4)) :
    bitTreeScanner.tr (borrowState first) inSym ![t₀, some 0] =
      stay (borrowState first) idle (some (some 1), 1) := by
  cases first <;> rfl

/-- A decrement absorbs the borrow at a one and turns back, in either phase. -/
theorem tr_borrowState_one (first : Bool) (t₀ : Option (Fin 4)) (inSym : Option (Fin 4)) :
    bitTreeScanner.tr (borrowState first) inSym ![t₀, some 1] =
      stay (returnState first) idle (some (some 0), -1) := by
  cases first <;> rfl

/-- A decrement's return passes a digit, in either phase. -/
theorem tr_returnState_digit (first : Bool) (t₀ : Option (Fin 4)) (inSym : Option (Fin 4))
    (b : Bool) :
    bitTreeScanner.tr (returnState first) inSym ![t₀, some (boolEmb b)] =
      stay (returnState first) idle (none, -1) := by
  cases first <;> cases b <;> rfl

/-- The configuration {lit}`i` cells into a borrow over the digits {lit}`d`: the
digits below cell {lit}`i` turned to ones, the head at cell {lit}`i + 1`. At
{lit}`i = 0`, the configuration at the lowest digit that begins the
decrement. -/
def borrowCfg (c : ℕ) (first : Bool) (d : List Bool) (i : ℕ) :
    Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb) where
  state := some (borrowState first)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tape1 k, fun z ↦ if 1 ≤ z ∧ z ≤ i then some 1 else tapeDigits d z]
  workTapePos := ![(c : ℤ), (i : ℤ) + 1]

/-- The configuration returning from a borrow over the digits {lit}`d`, at
cell {lit}`i`: the digits decremented, the head at cell {lit}`i`. -/
def returnCfg (c : ℕ) (first : Bool) (d : List Bool) (i : ℕ) :
    Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb) where
  state := some (returnState first)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tape1 k, tapeDigits (decList d)]
  workTapePos := ![(c : ℤ), (i : ℤ)]

/-- The digit tape at a cell holding a digit. -/
theorem tapeDigits_of_lt (d : List Bool) (i : ℕ) (hi : i < d.length) :
    tapeDigits d (i + 1) = some (boolEmb (d.getD i false)) := by
  rw [tapeDigits, ite_eq_right (by omega), digitsAt, ite_eq_left (by omega)]
  congr 3
  omega

/-- The digit tape above the digits. -/
theorem tapeDigits_of_ge (d : List Bool) (z : ℤ) (hz : (d.length : ℤ) < z) :
    tapeDigits d z = none := by
  rw [tapeDigits, ite_eq_right (by omega), digitsAt, ite_eq_right (by omega)]

/-- The decremented digit tape, cell by cell: ones below the borrow's length,
a zero at it, the original digits above. -/
theorem tapeDigits_decList (d : List Bool) (hd : allFalse d = false) (z : ℤ) :
    tapeDigits (decList d) z =
      if 1 ≤ z ∧ z ≤ borrowLength d then some 1
      else if z = borrowLength d + 1 then some 0 else tapeDigits d z := by
  have htz := borrowLength_lt_length d hd
  by_cases h1 : 1 ≤ z ∧ z ≤ borrowLength d
  · rw [ite_eq_left h1]
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, z = i + 1 := ⟨(z - 1).toNat, by omega⟩
    rw [tapeDigits_of_lt (decList d) i (by rw [length_decList]; omega),
      getD_decList_of_lt d i (by omega)]
    rfl
  · rw [ite_eq_right h1]
    by_cases h2 : z = borrowLength d + 1
    · rw [ite_eq_left h2, h2]
      rw [show (borrowLength d : ℤ) + 1 = ((borrowLength d : ℕ) : ℤ) + 1 from rfl,
        tapeDigits_of_lt (decList d) (borrowLength d) (by rw [length_decList]; omega),
        getD_decList_borrowLength d hd]
      rfl
    · rw [ite_eq_right h2]
      by_cases hz : z ≤ 0
      · rw [tapeDigits, tapeDigits]
        by_cases hz0 : z = 0
        · rw [ite_eq_left hz0, ite_eq_left hz0]
        · rw [ite_eq_right hz0, ite_eq_right hz0, digitsAt, digitsAt, ite_eq_right (by omega),
            ite_eq_right (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i : ℕ, z = i + 1 := ⟨(z - 1).toNat, by omega⟩
        by_cases hi : i < d.length
        · rw [tapeDigits_of_lt _ _ (by rw [length_decList]; exact hi), tapeDigits_of_lt _ _ hi,
            getD_decList_of_gt d i (by omega)]
        · rw [tapeDigits_of_ge (decList d) ((i : ℤ) + 1) (by rw [length_decList]; omega),
            tapeDigits_of_ge d ((i : ℤ) + 1) (by omega)]

/-- One step of the borrow over a zero. -/
theorem borrowCfg_step (c : ℕ) (first : Bool) (d : List Bool) (i : ℕ) (hi : i < borrowLength d) :
    bitTreeScanner.step (borrowCfg w k hk c first d i) = borrowCfg w k hk c first d (i + 1) ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk c first d i) = none := by
  have htz := borrowLength_le_length d
  have hsym : (borrowCfg w k hk c first d i).workTapeSymbols = ![tape1 k (c : ℤ), some 0] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ ((i : ℤ) + 1) ∧ ((i : ℤ) + 1) ≤ i then some 1
        else tapeDigits d ((i : ℤ) + 1)) = some 0
      rw [ite_eq_right (by omega), tapeDigits_of_lt _ _ (by omega), getD_of_lt_borrowLength d i hi]
      rfl
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk c first d i) (borrowState first)
    (borrowState first) idle (some (some 1), 1) rfl (by rw [hsym]; exact tr_borrowState_zero _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update (fun z ↦ if 1 ≤ z ∧ z ≤ (i : ℤ) then some 1 else tapeDigits d z)
        ((i : ℤ) + 1) (some 1) z =
        if 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) then some 1 else tapeDigits d z
      rw [Function.update_apply]
      by_cases hz : z = (i : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_left (by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (i : ℤ)
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (i : ℤ) + 1 + ((1 : SignType) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega

/-- The borrow's steps up to any cell short of the one it absorbs at. -/
theorem configs_borrowCfg (c : ℕ) (first : Bool) (d : List Bool) :
    ∀ i, i ≤ borrowLength d →
      bitTreeScanner.configs (borrowCfg w k hk c first d 0) i = borrowCfg w k hk c first d i ∧
        bitTreeScanner.outputString (borrowCfg w k hk c first d 0) i = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨configs_zero, rfl⟩
  · intro i ih hi
    obtain ⟨hc, ho⟩ := ih (by omega)
    obtain ⟨hstep, hout⟩ := borrowCfg_step w k hk c first d i (by omega)
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact hstep
    · rw [outputString_succ, ho, hc, hout]
      rfl

/-- The step absorbing the borrow: at the lowest one, the digit becomes a zero
and the return begins. -/
theorem borrowCfg_flip (c : ℕ) (first : Bool) (d : List Bool) (hd : allFalse d = false) :
    bitTreeScanner.step (borrowCfg w k hk c first d (borrowLength d)) =
        returnCfg w k hk c first d (borrowLength d) ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk c first d (borrowLength d)) = none := by
  have htz := borrowLength_lt_length d hd
  have hsym : (borrowCfg w k hk c first d (borrowLength d)).workTapeSymbols =
      ![tape1 k (c : ℤ), some 1] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ ((borrowLength d : ℤ) + 1) ∧ ((borrowLength d : ℤ) + 1) ≤ borrowLength d
        then some 1
        else tapeDigits d ((borrowLength d : ℤ) + 1)) = some 1
      rw [ite_eq_right (by omega), tapeDigits_of_lt _ _ htz, getD_borrowLength d hd]
      rfl
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk c first d (borrowLength d))
    (borrowState first)
    (returnState first) idle (some (some 0), -1) rfl
    (by rw [hsym]; exact tr_borrowState_one _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (borrowLength d : ℤ) then some 1 else tapeDigits d z)
        ((borrowLength d : ℤ) + 1) (some 0) z = tapeDigits (decList d) z
      rw [Function.update_apply, tapeDigits_decList d hd]
      by_cases hz : z = (borrowLength d : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (borrowLength d : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (borrowLength d : ℤ) + 1 + ((-1 : SignType) : ℤ) = (borrowLength d : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- One step of the return over a digit. -/
theorem returnCfg_step (c : ℕ) (first : Bool) (d : List Bool) (i : ℕ) (hi : i < d.length) :
    bitTreeScanner.step (returnCfg w k hk c first d (i + 1)) = returnCfg w k hk c first d i ∧
      bitTreeScanner.outputSymbol (returnCfg w k hk c first d (i + 1)) = none := by
  have hsym : (returnCfg w k hk c first d (i + 1)).workTapeSymbols =
      ![tape1 k (c : ℤ), some (boolEmb ((decList d).getD i false))] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change tapeDigits (decList d) ((i + 1 : ℕ) : ℤ) = _
      rw [Nat.cast_succ]
      exact tapeDigits_of_lt (decList d) i (by rw [length_decList]; exact hi)
  obtain ⟨hstep, hout⟩ := step_stay (returnCfg w k hk c first d (i + 1)) (returnState first)
    (returnState first) idle (none, -1) rfl
    (by rw [hsym]; exact tr_returnState_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change ((i + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (i : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- The return's steps down to any cell. -/
theorem configs_returnCfg (c : ℕ) (first : Bool) (d : List Bool) (t : ℕ) (ht : t < d.length) :
    ∀ j, j ≤ t →
      bitTreeScanner.configs (returnCfg w k hk c first d t) j = returnCfg w k hk c first d (t - j) ∧
        bitTreeScanner.outputString (returnCfg w k hk c first d t) j = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨configs_zero, rfl⟩
  · intro j ih hj
    obtain ⟨hc, ho⟩ := ih (by omega)
    obtain ⟨hstep, hout⟩ := returnCfg_step w k hk c first d (t - (j + 1)) (by omega)
    rw [show t - (j + 1) + 1 = t - j by omega] at hstep hout
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact hstep
    · rw [outputString_succ, ho, hc, hout]
      rfl

/-- A decrement's borrow and return: from the lowest digit, out through the
zeros, the absorbing step, and back to the base cell, in {lit}`2 * borrowLength d + 1`
steps, emitting nothing. -/
theorem configs_decrement (c : ℕ) (first : Bool) (d : List Bool) (hd : allFalse d = false) :
    bitTreeScanner.configs (borrowCfg w k hk c first d 0) (2 * borrowLength d + 1) =
        returnCfg w k hk c first d 0 ∧
      bitTreeScanner.outputString (borrowCfg w k hk c first d 0) (2 * borrowLength d + 1) = [] := by
  have htz := borrowLength_lt_length d hd
  have h₃ := configs_returnCfg w k hk c first d (borrowLength d) htz (borrowLength d) le_rfl
  rw [Nat.sub_self] at h₃
  rw [show 2 * borrowLength d + 1 = borrowLength d + 1 + borrowLength d by omega]
  exact run_seq _ _ _ _ _
    (run_seq _ _ _ _ _ (configs_borrowCfg w k hk c first d (borrowLength d) le_rfl)
    (run_step _ _ (borrowCfg_flip w k hk c first d hd))) h₃

end Borrow

section Fail

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length)

/-- The configuration erasing the digits after a decrement found the count at
zero, at cell {lit}`i`: the digits below it still ones, those above it blank,
the head at cell {lit}`i`. -/
def clearCfg (c : ℕ) (i : ℕ) : Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb) where
  state := some stClear
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tape1 k, fun z ↦ if 1 ≤ z ∧ z ≤ i then some 1 else if z = 0 then some 3 else none]
  workTapePos := ![(c : ℤ), (i : ℤ)]

/-- The step past the digits' end: the borrow ran into blank, so the count was
zero, and the erasure begins. -/
theorem borrowCfg_blank (c : ℕ) (d : List Bool) :
    bitTreeScanner.step (borrowCfg w k hk c false d d.length) = clearCfg w k hk c d.length ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk c false d d.length) = none := by
  have hsym : (borrowCfg w k hk c false d d.length).workTapeSymbols =
      ![tape1 k (c : ℤ), none] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ ((d.length : ℤ) + 1) ∧ ((d.length : ℤ) + 1) ≤ d.length then some 1
        else tapeDigits d ((d.length : ℤ) + 1)) = none
      rw [ite_eq_right (by omega), tapeDigits_of_ge d _ (by omega)]
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk c false d d.length) stBorrow stClear idle
    (none, -1) rfl (by rw [hsym]; exact tr_borrow_blank _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ z ∧ z ≤ (d.length : ℤ) then some 1 else tapeDigits d z) =
        if 1 ≤ z ∧ z ≤ (d.length : ℤ) then some 1 else if z = 0 then some 3 else none
      by_cases h1 : 1 ≤ z ∧ z ≤ (d.length : ℤ)
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1, tapeDigits]
        by_cases hz : z = 0
        · rw [ite_eq_left hz, ite_eq_left hz]
        · rw [ite_eq_right hz, ite_eq_right hz, digitsAt, ite_eq_right (by omega)]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (d.length : ℤ) + 1 + ((-1 : SignType) : ℤ) = (d.length : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- One step of the erasure. -/
theorem clearCfg_step (c : ℕ) (i : ℕ) :
    bitTreeScanner.step (clearCfg w k hk c (i + 1)) = clearCfg w k hk c i ∧
      bitTreeScanner.outputSymbol (clearCfg w k hk c (i + 1)) = none := by
  have hsym : (clearCfg w k hk c (i + 1)).workTapeSymbols =
      ![tape1 k (c : ℤ), some (boolEmb true)] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ ((i + 1 : ℕ) : ℤ) ∧ ((i + 1 : ℕ) : ℤ) ≤ ((i + 1 : ℕ) : ℤ) then some 1
        else if ((i + 1 : ℕ) : ℤ) = 0 then some 3 else none) = some (boolEmb true)
      rw [ite_eq_left ⟨by omega, le_rfl⟩]
      rfl
  obtain ⟨hstep, hout⟩ := step_stay (clearCfg w k hk c (i + 1)) stClear stClear idle
    (some none, -1) rfl (by rw [hsym]; exact tr_clear_digit _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) then some 1 else if z = 0 then some 3 else none)
        ((i + 1 : ℕ) : ℤ) none z =
        if 1 ≤ z ∧ z ≤ (i : ℤ) then some 1 else if z = 0 then some 3 else none
      rw [Function.update_apply]
      by_cases hz : z = ((i + 1 : ℕ) : ℤ)
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (i : ℤ)
        · rw [ite_eq_left (by omega), ite_eq_left h1]
        · rw [ite_eq_right (by omega), ite_eq_right h1]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change ((i + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (i : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- The erasure's steps down to any cell. -/
theorem configs_clearCfg (c : ℕ) (n : ℕ) :
    ∀ j, j ≤ n →
      bitTreeScanner.configs (clearCfg w k hk c n) j = clearCfg w k hk c (n - j) ∧
        bitTreeScanner.outputString (clearCfg w k hk c n) j = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨configs_zero, rfl⟩
  · intro j ih hj
    obtain ⟨hc, ho⟩ := ih (by omega)
    obtain ⟨hstep, hout⟩ := clearCfg_step w k hk c (n - (j + 1))
    rw [show n - (j + 1) + 1 = n - j by omega] at hstep hout
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact hstep
    · rw [outputString_succ, ho, hc, hout]
      rfl

/-- The step leaving the leaf: at the base marker after the erasure, the count
marker under the first head closes the last pending tree, and a blank there
closes the leaf and moves that head left. -/
theorem clearCfg_exit (c : ℕ) (hk0 : k ≠ 0) :
    bitTreeScanner.step (clearCfg w k hk c 0) = cfgAt w k hk (close c) ∧
      bitTreeScanner.outputSymbol (clearCfg w k hk c 0) = none := by
  cases c with
  | zero =>
    have hsym : (clearCfg w k hk 0 0).workTapeSymbols = ![some 0, some 3] := by
      funext j
      match j with
      | 0 =>
        change tape1 k 0 = some 0
        rw [tape1, ite_eq_left ⟨hk0, rfl⟩]
      | 1 => rfl
    obtain ⟨hstep, hout⟩ := step_stay (clearCfg w k hk 0 0) stClear stDone idle idle rfl
      (by rw [hsym]; exact tr_clear_base_last _)
    refine ⟨?_, hout⟩
    rw [hstep]
    refine Cfg.ext rfl rfl ?_ ?_
    · funext j z
      match j with
      | 0 => rfl
      | 1 =>
        change (if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else if z = 0 then some 3 else none) =
          tape2 k (close 0) z
        rw [ite_eq_right (by omega), close_zero, tape2]
        by_cases hz : z = 0
        · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left hk0]
        · rw [ite_eq_right hz, ite_eq_right hz]
    · funext j
      match j with
      | 0 => rfl
      | 1 => rfl
  | succ c =>
    have hsym : (clearCfg w k hk (c + 1) 0).workTapeSymbols = ![none, some 3] := by
      funext j
      match j with
      | 0 =>
        change tape1 k ((c + 1 : ℕ) : ℤ) = none
        rw [tape1, ite_eq_right (by omega)]
      | 1 => rfl
    obtain ⟨hstep, hout⟩ := step_stay (clearCfg w k hk (c + 1) 0) stClear stMain (none, -1) idle
      rfl (by rw [hsym]; exact tr_clear_base _)
    refine ⟨?_, hout⟩
    rw [hstep]
    refine Cfg.ext ?_ rfl ?_ ?_
    · change some stMain = some (stateOf k (close (c + 1)).mode)
      rw [close_succ, stateOf, ite_eq_right hk0]
    · funext j z
      match j with
      | 0 => rfl
      | 1 =>
        change (if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else if z = 0 then some 3 else none) =
          tape2 k (close (c + 1)) z
        rw [ite_eq_right (by omega), close_succ, tape2]
        by_cases hz : z = 0
        · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left hk0]
        · rw [ite_eq_right hz, ite_eq_right hz]
    · funext j
      match j with
      | 0 =>
        change ((c + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (((close (c + 1)).count : ℕ) : ℤ)
        rw [SignType.coe_neg_one, close_succ]
        change ((c + 1 : ℕ) : ℤ) + -1 = (c : ℤ)
        omega
      | 1 => rfl

/-- A decrement finding the count at zero: out across the digits, back erasing
them, and the step leaving the leaf, in {lit}`2 * d.length + 2` steps,
emitting nothing. -/
theorem configs_fail (c : ℕ) (d : List Bool) (hd : allFalse d = true) (hk0 : k ≠ 0) :
    bitTreeScanner.configs (borrowCfg w k hk c false d 0) (2 * d.length + 2) =
        cfgAt w k hk (close c) ∧
      bitTreeScanner.outputString (borrowCfg w k hk c false d 0) (2 * d.length + 2) = [] := by
  have htz := borrowLength_of_allFalse d hd
  have h₃ := configs_clearCfg w k hk c d.length d.length le_rfl
  rw [Nat.sub_self] at h₃
  rw [show 2 * d.length + 2 = d.length + 1 + d.length + 1 by omega]
  exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
    (configs_borrowCfg w k hk c false d d.length (by rw [htz]))
    (run_step _ _ (borrowCfg_blank w k hk c d))) h₃) (run_step _ _ (clearCfg_exit w k hk c hk0))

end Fail

section Settle

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length)

/-- The closed form in the countdown is the configuration at the lowest digit
that begins a decrement. -/
theorem cfgAt_count (c wd : ℕ) (d : List Bool) (hk0 : k ≠ 0) :
    cfgAt w k hk ⟨.count, c, wd, d⟩ = borrowCfg w k hk c false d 0 := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext j z
  match j with
  | 0 => rfl
  | 1 =>
    change tape2 k ⟨.count, c, wd, d⟩ z =
      if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits d z
    rw [ite_eq_right (by omega), tape2, tapeDigits]
    by_cases hz : z = 0
    · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left hk0]
    · rw [ite_eq_right hz, ite_eq_right hz]

/-- The closed form at complete digits: the digit head at the base marker over
the digits, which the first decrement starts from. -/
theorem cfgAt_bits_full (c : ℕ) (d : List Bool) (hk0 : k ≠ 0) (z : ℤ) :
    tape2 k ⟨.bits, c, d.length, d⟩ z = tapeDigits d z := by
  rw [tape2, tapeDigits]
  by_cases hz : z = 0
  · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left hk0]
  · rw [ite_eq_right hz, ite_eq_right hz]
    change (if 1 ≤ z ∧ z ≤ ((d.length - d.length : ℕ) : ℤ) then some 2
      else digitsAt ((d.length - d.length : ℕ) : ℤ) d z) = digitsAt 0 d z
    rw [Nat.sub_self, ite_eq_right (by omega)]
    rfl

/-- The step from complete digits to the first decrement. -/
theorem cfgAt_bits_full_step (c : ℕ) (d : List Bool) (hk0 : k ≠ 0) :
    bitTreeScanner.step (cfgAt w k hk ⟨.bits, c, d.length, d⟩) = borrowCfg w k hk c true d 0 ∧
      bitTreeScanner.outputSymbol (cfgAt w k hk ⟨.bits, c, d.length, d⟩) = none := by
  have hsym : (cfgAt w k hk ⟨.bits, c, d.length, d⟩).workTapeSymbols =
      ![tape1 k (c : ℤ), some 3] := by
    funext j
    match j with
    | 0 => rfl
    | 1 =>
      change tape2 k ⟨.bits, c, d.length, d⟩ (head2 ⟨.bits, c, d.length, d⟩) = some 3
      rw [cfgAt_bits_full k c d hk0, head2]
      change tapeDigits d ((d.length - d.length : ℕ) : ℤ) = some 3
      rw [Nat.sub_self]
      rfl
  obtain ⟨hstep, hout⟩ := step_stay (cfgAt w k hk ⟨.bits, c, d.length, d⟩) stBits stBorrowInit
    idle (none, 1) rfl (by rw [hsym]; exact tr_bits_base _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change tape2 k ⟨.bits, c, d.length, d⟩ z =
        if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits d z
      rw [ite_eq_right (by omega), cfgAt_bits_full k c d hk0]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change head2 ⟨.bits, c, d.length, d⟩ + ((1 : SignType) : ℤ) = ((0 : ℕ) : ℤ) + 1
      rw [SignType.coe_one, head2]
      change ((d.length - d.length : ℕ) : ℤ) + 1 = ((0 : ℕ) : ℤ) + 1
      rw [Nat.sub_self]

/-- The first decrement's return reaching the base marker steps to the lowest
digit, where the countdown begins. -/
theorem returnCfg_init_exit (c : ℕ) (d : List Bool) :
    bitTreeScanner.step (returnCfg w k hk c true d 0) = borrowCfg w k hk c false (decList d) 0 ∧
      bitTreeScanner.outputSymbol (returnCfg w k hk c true d 0) = none := by
  have hsym : (returnCfg w k hk c true d 0).workTapeSymbols = ![tape1 k (c : ℤ), some 3] := by
    funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  obtain ⟨hstep, hout⟩ := step_stay (returnCfg w k hk c true d 0) stReturnInit stBorrow idle
    (none, 1) rfl (by rw [hsym]; exact tr_returnInit_base _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change tapeDigits (decList d) z =
        if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits (decList d) z
      rw [ite_eq_right (by omega)]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = ((0 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]

/-- The work after a payload bit: the failed decrement that detects the
payload's end, when no payload remains, in {name}`Geb.BitTreeScanner.pendingCount`
steps, to the closed form at the state the bit settles in. -/
theorem configs_pendingCount (c wd : ℕ) (d : List Bool) (hlen : d.length = wd) (hk0 : k ≠ 0) :
    bitTreeScanner.configs (cfgAt w k hk ⟨.count, c, wd, d⟩) (pendingCount wd d) =
        cfgAt w k hk (settleCount c wd d) ∧
      bitTreeScanner.outputString (cfgAt w k hk ⟨.count, c, wd, d⟩) (pendingCount wd d) = [] := by
  subst hlen
  cases hd : allFalse d with
  | true =>
    rw [settleCount_of_allFalse _ _ _ hd, pendingCount, hd, Bool.cond_true, failCost,
      cfgAt_count w k hk c d.length d hk0]
    exact configs_fail w k hk c d hd hk0
  | false =>
    rw [settleCount_of_not_allFalse _ _ _ hd, pendingCount, hd, Bool.cond_false]
    exact ⟨configs_zero, rfl⟩

/-- The work after a length digit: when the digits are complete, the step to
the lowest digit, the first decrement, and what follows a payload bit, in
{name}`Geb.BitTreeScanner.pendingDigits` steps, to the closed form at the state the
digit settles in. -/
theorem configs_pendingDigits (c wd : ℕ) (d : List Bool) (hd : allFalse d = false)
    (hle : d.length ≤ wd) (hk0 : k ≠ 0) :
    bitTreeScanner.configs (cfgAt w k hk ⟨.bits, c, wd, d⟩) (pendingDigits wd d) =
        cfgAt w k hk (settleDigits c wd d) ∧
      bitTreeScanner.outputString (cfgAt w k hk ⟨.bits, c, wd, d⟩) (pendingDigits wd d) = [] := by
  by_cases hfull : d.length = wd
  · subst hfull
    rw [settleDigits_of_length_eq _ _ _ rfl, pendingDigits, ite_eq_left rfl, chainCost]
    have h₄ := configs_pendingCount w k hk c d.length (decList d) (length_decList d) hk0
    rw [cfgAt_count w k hk c d.length (decList d) hk0] at h₄
    rw [show 1 + (2 * borrowLength d + 2) + pendingCount d.length (decList d) =
      1 + (2 * borrowLength d + 1) + 1 + pendingCount d.length (decList d) by omega]
    exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
      (run_step _ _ (cfgAt_bits_full_step w k hk c d hk0)) (configs_decrement w k hk c true d hd))
      (run_step _ _ (returnCfg_init_exit w k hk c d))) h₄
  · rw [settleDigits_of_length_ne _ _ _ hfull, pendingDigits, ite_eq_right hfull]
    exact ⟨configs_zero, rfl⟩

end Settle

section Bit

variable (w : List Bool) (k : ℕ)

/-- The first tape does not change once its marker is written. -/
theorem tape1_succ (hk : k ≠ 0) : tape1 k = tape1 (k + 1) := by
  funext z
  rw [tape1, tape1]
  by_cases hz : z = 0
  · rw [ite_eq_left ⟨hk, hz⟩, ite_eq_left ⟨Nat.succ_ne_zero k, hz⟩]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The second tape outside a leaf: the base marker alone. -/
theorem tape2_blank (hk : k ≠ 0) (s : Scan)
    (hs : s.mode = .term ∨ s.mode = .done ∨ s.mode = .dead) (z : ℤ) :
    tape2 k s z = if z = 0 then some 3 else none := by
  rw [tape2]
  by_cases hz : z = 0
  · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left hk]
  · rw [ite_eq_right hz, ite_eq_right hz]
    rcases hs with h | h | h <;> rw [h]

/-- Digits laid out above a base cell, at the cell above the base and above
it. -/
theorem digitsAt_cons (base : ℤ) (b : Bool) (d : List Bool) (z : ℤ) :
    digitsAt base (b :: d) z =
      if z = base + 1 then some (boolEmb b) else digitsAt (base + 1) d z := by
  rw [digitsAt, digitsAt, List.length_cons]
  by_cases hz : z = base + 1
  · rw [ite_eq_left hz, ite_eq_left ⟨by omega, by omega⟩, hz]
    simp
  · rw [ite_eq_right hz]
    by_cases h1 : base < z ∧ z ≤ base + ((d.length + 1 : ℕ) : ℤ)
    · rw [ite_eq_left h1, ite_eq_left ⟨by omega, by omega⟩]
      congr 2
      rw [show (z - base - 1).toNat = (z - (base + 1) - 1).toNat + 1 by omega, List.getD_cons_succ]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- A step reading a bit from the closed form lands on the closed form at a
state, given the resolved transition and the five field equalities. -/
theorem advance_cfgAt (h : k + 1 ≤ w.length) (s s' : Scan) (q' : Fin 11) (a₀ a₁ : Act)
    (htr : bitTreeScanner.tr (stateOf k s.mode) (some (boolEmb w[k]))
      ![tape1 k (s.count : ℤ), tape2 k s (head2 s)] = advance q' a₀ a₁)
    (hq : stateOf (k + 1) s'.mode = q')
    (h0 : applyAct a₀ (tape1 k) (s.count : ℤ) = tape1 (k + 1))
    (h1 : applyAct a₁ (tape2 k s) (head2 s) = tape2 (k + 1) s')
    (hc : (s.count : ℤ) + (a₀.2 : ℤ) = (s'.count : ℤ))
    (hh : head2 s + (a₁.2 : ℤ) = head2 s') :
    bitTreeScanner.step (cfgAt w k (by omega) s) = cfgAt w (k + 1) h s' ∧
      bitTreeScanner.outputSymbol (cfgAt w k (by omega) s) = none := by
  obtain ⟨hstep, hout⟩ := step_advance (cfgAt w k (by omega) s) (stateOf k s.mode) q' a₀ a₁ rfl
    (by
      rw [workTapeSymbols_eq, inputSymbol_of_inputPos w k (by omega) _ (cfgAt_inputPos_val _ _ _ _)]
      exact htr)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext ?_ ?_ ?_ ?_
  · change some q' = some (stateOf (k + 1) s'.mode)
    rw [hq]
  · change moveInputPos (cfgAt w k (by omega) s).inputPos SignType.pos =
      (cfgAt w (k + 1) h s').inputPos
    rw [moveInputPos_pos_of_ne_right _
      (by rw [cfgAt_inputPos_val, List.length_map]; omega)]
    exact Fin.ext rfl
  · funext i
    match i with
    | 0 => exact h0
    | 1 => exact h1
  · funext i
    match i with
    | 0 => exact hc
    | 1 => exact hh

/-- The first bit: from the initial configuration, which writes both markers. -/
theorem cfgAt_step_zero (h : 1 ≤ w.length) :
    bitTreeScanner.configs (cfgAt w 0 (Nat.zero_le _) init) (cost init w[0]) =
        cfgAt w 1 h (scanStep init w[0]) ∧
      bitTreeScanner.outputString (cfgAt w 0 (Nat.zero_le _) init) (cost init w[0]) = [] := by
  cases hb : w[0] with
  | true =>
    refine run_step _ _ (advance_cfgAt w 0 h init ⟨.term, 1, 0, []⟩ stMain (some (some 0), 1)
      (some (some 3), 0) (by rw [hb]; exact tr_first_pair _) rfl ?_ ?_ rfl rfl)
    · funext z
      change Function.update (tape1 0) 0 (some 0) z = tape1 1 z
      rw [Function.update_apply, tape1, tape1]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left ⟨Nat.one_ne_zero, hz⟩]
      · rw [ite_eq_right hz, ite_eq_right (by omega), ite_eq_right (by omega)]
    · funext z
      change Function.update (tape2 0 init) 0 (some 3) z = tape2 1 ⟨.term, 1, 0, []⟩ z
      rw [Function.update_apply, tape2, tape2]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left Nat.one_ne_zero]
      · rw [ite_eq_right hz, ite_eq_right hz, ite_eq_right hz]
        rfl
  | false =>
    refine run_step _ _ (advance_cfgAt w 0 h init ⟨.zeros, 0, 0, []⟩ stZeros (some (some 0), 0)
      (some (some 3), 1) (by rw [hb]; exact tr_first_leaf _) rfl ?_ ?_ rfl ?_)
    · funext z
      change Function.update (tape1 0) 0 (some 0) z = tape1 1 z
      rw [Function.update_apply, tape1, tape1]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left ⟨Nat.one_ne_zero, hz⟩]
      · rw [ite_eq_right hz, ite_eq_right (by omega), ite_eq_right (by omega)]
    · funext z
      change Function.update (tape2 0 init) 0 (some 3) z = tape2 1 ⟨.zeros, 0, 0, []⟩ z
      rw [Function.update_apply, tape2, tape2]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left Nat.one_ne_zero]
      · rw [ite_eq_right hz, ite_eq_right hz, ite_eq_right hz]
        change none = if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 2 else none
        rw [ite_eq_right (by omega)]
    · change head2 init + ((1 : SignType) : ℤ) = head2 ⟨.zeros, 0, 0, []⟩
      rw [SignType.coe_one]
      rfl

/-- A bit in the expecting mode after the first step. -/
theorem cfgAt_step_term (h : k + 2 ≤ w.length) (c : ℕ) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) ⟨.term, c, 0, []⟩)
          (cost ⟨.term, c, 0, []⟩ w[k + 1]) =
        cfgAt w (k + 2) h (scanStep ⟨.term, c, 0, []⟩ w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) ⟨.term, c, 0, []⟩)
        (cost ⟨.term, c, 0, []⟩ w[k + 1]) = [] := by
  have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
  cases hb : w[k + 1] with
  | true =>
    refine run_step _ _ (advance_cfgAt w (k + 1) h _ ⟨.term, c + 1, 0, []⟩ stMain (none, 1) idle
      (by rw [hb]; exact tr_main_pair _) (by rw [stateOf, ite_eq_right (Nat.succ_ne_zero _)])
      (tape1_succ _ hk) ?_ ?_ rfl)
    · funext z
      change tape2 (k + 1) ⟨.term, c, 0, []⟩ z = tape2 (k + 2) ⟨.term, c + 1, 0, []⟩ z
      rw [tape2_blank _ hk _ (Or.inl rfl), tape2_blank _ (Nat.succ_ne_zero _) _ (Or.inl rfl)]
    · change (c : ℤ) + ((1 : SignType) : ℤ) = ((c + 1 : ℕ) : ℤ)
      rw [SignType.coe_one]
      omega
  | false =>
    refine run_step _ _ (advance_cfgAt w (k + 1) h _ ⟨.zeros, c, 0, []⟩ stZeros idle (none, 1)
      (by rw [hb]; exact tr_main_leaf _) rfl (tape1_succ _ hk) ?_ rfl ?_)
    · funext z
      change tape2 (k + 1) ⟨.term, c, 0, []⟩ z = tape2 (k + 2) ⟨.zeros, c, 0, []⟩ z
      rw [tape2_blank _ hk _ (Or.inl rfl) z, tape2]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz, ite_eq_left (Nat.succ_ne_zero _)]
      · rw [ite_eq_right hz, ite_eq_right hz]
        change none = if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 2 else none
        rw [ite_eq_right (by omega)]
    · change head2 ⟨.term, c, 0, []⟩ + ((1 : SignType) : ℤ) = head2 ⟨.zeros, c, 0, []⟩
      rw [SignType.coe_one]
      rfl

/-- A bit while reading a gamma code's zeros. -/
theorem cfgAt_step_zeros (h : k + 2 ≤ w.length) (c wd : ℕ) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) ⟨.zeros, c, wd, []⟩)
          (cost ⟨.zeros, c, wd, []⟩ w[k + 1]) =
        cfgAt w (k + 2) h (scanStep ⟨.zeros, c, wd, []⟩ w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) ⟨.zeros, c, wd, []⟩)
        (cost ⟨.zeros, c, wd, []⟩ w[k + 1]) = [] := by
  have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
  cases hb : w[k + 1] with
  | false =>
    refine run_step _ _ (advance_cfgAt w (k + 1) h _ ⟨.zeros, c, wd + 1, []⟩ stZeros idle
      (some (some 2), 1) (by rw [hb]; exact tr_zeros_zero _) rfl (tape1_succ _ hk) ?_ rfl ?_)
    · funext z
      change Function.update (tape2 (k + 1) ⟨.zeros, c, wd, []⟩) (head2 ⟨.zeros, c, wd, []⟩)
        (some 2) z = tape2 (k + 2) ⟨.zeros, c, wd + 1, []⟩ z
      rw [Function.update_apply, tape2, tape2, head2]
      change (if z = (wd : ℤ) + 1 then some 2
        else if z = 0 then (if k + 1 ≠ 0 then some 3 else none)
        else if 1 ≤ z ∧ z ≤ (wd : ℤ) then some 2 else none) =
        if z = 0 then (if k + 2 ≠ 0 then some 3 else none)
        else if 1 ≤ z ∧ z ≤ ((wd + 1 : ℕ) : ℤ) then some 2 else none
      by_cases hz : z = (wd : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
      · rw [ite_eq_right hz]
        by_cases hz0 : z = 0
        · rw [ite_eq_left hz0, ite_eq_left hz0, ite_eq_left hk, ite_eq_left (Nat.succ_ne_zero _)]
        · rw [ite_eq_right hz0, ite_eq_right hz0]
          by_cases h1 : 1 ≤ z ∧ z ≤ (wd : ℤ)
          · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
          · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · change (wd : ℤ) + 1 + ((1 : SignType) : ℤ) = ((wd + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega
  | true =>
    have hstep := advance_cfgAt w (k + 1) h ⟨.zeros, c, wd, []⟩ ⟨.bits, c, wd + 1, [true]⟩ stBits
      idle (some (some 1), -1) (by rw [hb]; exact tr_zeros_one _) rfl (tape1_succ _ hk) ?_ rfl ?_
    · rw [show cost ⟨.zeros, c, wd, []⟩ true = 1 + pendingDigits (wd + 1) [true] from rfl,
        scanStep_zeros_true]
      exact run_seq _ _ _ _ _ (run_step _ _ hstep)
        (configs_pendingDigits w (k + 2) h c (wd + 1) [true] rfl
          (by rw [List.length_singleton]; omega) (Nat.succ_ne_zero _))
    · funext z
      change Function.update (tape2 (k + 1) ⟨.zeros, c, wd, []⟩) (head2 ⟨.zeros, c, wd, []⟩)
        (some 1) z = tape2 (k + 2) ⟨.bits, c, wd + 1, [true]⟩ z
      rw [Function.update_apply, tape2, tape2, head2]
      change (if z = (wd : ℤ) + 1 then some 1
        else if z = 0 then (if k + 1 ≠ 0 then some 3 else none)
        else if 1 ≤ z ∧ z ≤ (wd : ℤ) then some 2 else none) =
        if z = 0 then (if k + 2 ≠ 0 then some 3 else none)
        else if 1 ≤ z ∧ z ≤ ((wd + 1 - 1 : ℕ) : ℤ) then some 2
        else digitsAt ((wd + 1 - 1 : ℕ) : ℤ) [true] z
      rw [Nat.add_sub_cancel]
      by_cases hz : z = (wd : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_right (by omega), digitsAt,
          ite_eq_left ⟨by omega, by rw [List.length_singleton]; omega⟩, hz,
          show ((wd : ℤ) + 1 - wd - 1).toNat = 0 by omega]
        rfl
      · rw [ite_eq_right hz]
        by_cases hz0 : z = 0
        · rw [ite_eq_left hz0, ite_eq_left hz0, ite_eq_left hk, ite_eq_left (Nat.succ_ne_zero _)]
        · rw [ite_eq_right hz0, ite_eq_right hz0]
          by_cases h1 : 1 ≤ z ∧ z ≤ (wd : ℤ)
          · rw [ite_eq_left h1, ite_eq_left h1]
          · rw [ite_eq_right h1, ite_eq_right h1, digitsAt,
              ite_eq_right (by rw [List.length_singleton]; omega)]
    · change (wd : ℤ) + 1 + ((-1 : SignType) : ℤ) = ((wd + 1 - [true].length : ℕ) : ℤ)
      rw [SignType.coe_neg_one, List.length_singleton, Nat.add_sub_cancel]
      omega

/-- A bit while reading a gamma code's digits. -/
theorem cfgAt_step_bits (h : k + 2 ≤ w.length) (c wd : ℕ) (d : List Bool)
    (hs : Good ⟨.bits, c, wd, d⟩) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) ⟨.bits, c, wd, d⟩)
          (cost ⟨.bits, c, wd, d⟩ w[k + 1]) =
        cfgAt w (k + 2) h (scanStep ⟨.bits, c, wd, d⟩ w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) ⟨.bits, c, wd, d⟩)
        (cost ⟨.bits, c, wd, d⟩ w[k + 1]) = [] := by
  have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
  dsimp only [Good] at hs
  obtain ⟨hlt, r, hr⟩ := hs
  have hf : allFalse (w[k + 1] :: d) = false := by
    rw [hr, ← List.cons_append, ← Bool.not_eq_true, allFalse_iff]
    exact Nat.ne_of_gt (ofBits_append_true_pos _)
  have hstep := advance_cfgAt w (k + 1) h ⟨.bits, c, wd, d⟩ ⟨.bits, c, wd, w[k + 1] :: d⟩ stBits
    idle (some (some (boolEmb w[k + 1])), -1) ?_ rfl (tape1_succ _ hk) ?_ rfl ?_
  · rw [show cost ⟨.bits, c, wd, d⟩ w[k + 1] = 1 + pendingDigits wd (w[k + 1] :: d) by
        cases w[k + 1] <;> rfl,
      scanStep_bits]
    exact run_seq _ _ _ _ _ (run_step _ _ hstep)
      (configs_pendingDigits w (k + 2) h c wd (w[k + 1] :: d) hf
        (by rw [List.length_cons]; exact hlt) (Nat.succ_ne_zero _))
  · have hsym : tape2 (k + 1) ⟨.bits, c, wd, d⟩ (head2 ⟨.bits, c, wd, d⟩) = some 2 := by
      rw [tape2, head2]
      change (if ((wd - d.length : ℕ) : ℤ) = 0 then (if k + 1 ≠ 0 then some 3 else none)
        else if 1 ≤ ((wd - d.length : ℕ) : ℤ) ∧
            ((wd - d.length : ℕ) : ℤ) ≤ ((wd - d.length : ℕ) : ℤ) then some 2
        else digitsAt ((wd - d.length : ℕ) : ℤ) d ((wd - d.length : ℕ) : ℤ)) = some 2
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, le_rfl⟩]
    rw [hsym]
    exact tr_bits_mark _ _
  · funext z
    change Function.update (tape2 (k + 1) ⟨.bits, c, wd, d⟩) (head2 ⟨.bits, c, wd, d⟩)
      (some (boolEmb w[k + 1])) z = tape2 (k + 2) ⟨.bits, c, wd, w[k + 1] :: d⟩ z
    rw [Function.update_apply, tape2, tape2, head2]
    change (if z = ((wd - d.length : ℕ) : ℤ) then some (boolEmb w[k + 1])
      else if z = 0 then (if k + 1 ≠ 0 then some 3 else none)
      else if 1 ≤ z ∧ z ≤ ((wd - d.length : ℕ) : ℤ) then some 2
      else digitsAt ((wd - d.length : ℕ) : ℤ) d z) =
      if z = 0 then (if k + 2 ≠ 0 then some 3 else none)
      else if 1 ≤ z ∧ z ≤ ((wd - (w[k + 1] :: d).length : ℕ) : ℤ) then some 2
      else digitsAt ((wd - (w[k + 1] :: d).length : ℕ) : ℤ) (w[k + 1] :: d) z
    rw [List.length_cons, digitsAt_cons,
      show ((wd - (d.length + 1) : ℕ) : ℤ) + 1 = ((wd - d.length : ℕ) : ℤ) by omega]
    by_cases hz : z = ((wd - d.length : ℕ) : ℤ)
    · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hz]
    · rw [ite_eq_right hz]
      by_cases hz0 : z = 0
      · rw [ite_eq_left hz0, ite_eq_left hz0, ite_eq_left hk, ite_eq_left (Nat.succ_ne_zero _)]
      · rw [ite_eq_right hz0, ite_eq_right hz0]
        by_cases h1 : 1 ≤ z ∧ z ≤ ((wd - d.length : ℕ) : ℤ)
        · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
        · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_right hz]
  · change ((wd - d.length : ℕ) : ℤ) + ((-1 : SignType) : ℤ) =
      ((wd - (w[k + 1] :: d).length : ℕ) : ℤ)
    rw [SignType.coe_neg_one, List.length_cons]
    omega

/-- The step consuming a payload bit: the decrement's return has reached the
base marker, and the machine steps to the lowest digit of the decremented
count. -/
theorem returnCfg_consume (h : k + 2 ≤ w.length) (c : ℕ) (d : List Bool) :
    bitTreeScanner.step (returnCfg w (k + 1) (by omega) c false d 0) =
        borrowCfg w (k + 2) h c false (decList d) 0 ∧
      bitTreeScanner.outputSymbol (returnCfg w (k + 1) (by omega) c false d 0) = none := by
  have hsym : (returnCfg w (k + 1) (by omega) c false d 0).workTapeSymbols =
      ![tape1 (k + 1) (c : ℤ), some 3] := by
    funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  obtain ⟨hstep, hout⟩ := step_advance (returnCfg w (k + 1) (by omega) c false d 0) stReturn
    stBorrow idle (none, 1) rfl (by
      rw [hsym, inputSymbol_of_inputPos w (k + 1) (by omega) _ rfl]
      exact tr_return_base_bit _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (returnCfg w (k + 1) (by omega) c false d 0).inputPos SignType.pos =
      (borrowCfg w (k + 2) h c false (decList d) 0).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change k + 1 + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j z
    match j with
    | 0 =>
      change tape1 (k + 1) z = tape1 (k + 2) z
      rw [← tape1_succ _ (Nat.succ_ne_zero k)]
    | 1 =>
      change tapeDigits (decList d) z =
        if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits (decList d) z
      rw [ite_eq_right (by omega)]
  · funext j
    match j with
    | 0 => rfl
    | 1 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = ((0 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]

/-- A payload bit in the countdown. -/
theorem cfgAt_step_count (h : k + 2 ≤ w.length) (c wd : ℕ) (d : List Bool)
    (hs : Good ⟨.count, c, wd, d⟩) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) ⟨.count, c, wd, d⟩)
          (cost ⟨.count, c, wd, d⟩ w[k + 1]) =
        cfgAt w (k + 2) h (scanStep ⟨.count, c, wd, d⟩ w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) ⟨.count, c, wd, d⟩)
        (cost ⟨.count, c, wd, d⟩ w[k + 1]) = [] := by
  dsimp only [Good] at hs
  obtain ⟨hd, hlen⟩ := hs
  rw [show cost ⟨.count, c, wd, d⟩ w[k + 1] =
      2 * borrowLength d + 1 + 1 + pendingCount wd (decList d) by
      cases w[k + 1] <;> rfl,
    scanStep_count, cfgAt_count w (k + 1) (by omega) c wd d (Nat.succ_ne_zero k)]
  have h₄ := configs_pendingCount w (k + 2) h c wd (decList d) (by rw [length_decList, hlen])
    (Nat.succ_ne_zero _)
  rw [cfgAt_count w (k + 2) h c wd (decList d) (Nat.succ_ne_zero _)] at h₄
  exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (configs_decrement w (k + 1) (by omega) c false d hd)
    (run_step _ _ (returnCfg_consume w k h c d))) h₄

/-- A bit after completion, and a bit after failure. -/
theorem cfgAt_step_end (h : k + 2 ≤ w.length) (c : ℕ) (m : Mode) (hm : m = .done ∨ m = .dead) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) ⟨m, c, 0, []⟩)
          (cost ⟨m, c, 0, []⟩ w[k + 1]) =
        cfgAt w (k + 2) h (scanStep ⟨m, c, 0, []⟩ w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) ⟨m, c, 0, []⟩)
        (cost ⟨m, c, 0, []⟩ w[k + 1]) = [] := by
  have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
  rcases hm with rfl | rfl
  · rw [show cost ⟨.done, c, 0, []⟩ w[k + 1] = 1 by cases w[k + 1] <;> rfl, scanStep_done]
    refine run_step _ _ (advance_cfgAt w (k + 1) h _ ⟨.dead, c, 0, []⟩ stDead idle idle
      (tr_done_bit _ _) rfl (tape1_succ _ hk) ?_ rfl rfl)
    funext z
    change tape2 (k + 1) ⟨.done, c, 0, []⟩ z = tape2 (k + 2) ⟨.dead, c, 0, []⟩ z
    rw [tape2_blank _ hk _ (Or.inr (Or.inl rfl)),
      tape2_blank _ (Nat.succ_ne_zero _) _ (Or.inr (Or.inr rfl))]
  · rw [show cost ⟨.dead, c, 0, []⟩ w[k + 1] = 1 by cases w[k + 1] <;> rfl, scanStep_dead]
    refine run_step _ _ (advance_cfgAt w (k + 1) h _ ⟨.dead, c, 0, []⟩ stDead idle idle
      (tr_dead_bit _ _) rfl (tape1_succ _ hk) ?_ rfl rfl)
    funext z
    change tape2 (k + 1) ⟨.dead, c, 0, []⟩ z = tape2 (k + 2) ⟨.dead, c, 0, []⟩ z
    rw [tape2_blank _ hk _ (Or.inr (Or.inr rfl)),
      tape2_blank _ (Nat.succ_ne_zero _) _ (Or.inr (Or.inr rfl))]

/-- A bit after the first, at any state satisfying the invariant: the closed
form at the scan's next state, after the bit's cost, emitting nothing. -/
theorem cfgAt_step_succ (h : k + 2 ≤ w.length) (s : Scan) (hs : Good s) :
    bitTreeScanner.configs (cfgAt w (k + 1) (by omega) s) (cost s w[k + 1]) =
        cfgAt w (k + 2) h (scanStep s w[k + 1]) ∧
      bitTreeScanner.outputString (cfgAt w (k + 1) (by omega) s) (cost s w[k + 1]) = [] := by
  obtain ⟨m, c, wd, d⟩ := s
  cases m with
  | term =>
    obtain ⟨rfl, rfl⟩ := hs
    exact cfgAt_step_term w k h c
  | zeros =>
    obtain rfl := hs
    exact cfgAt_step_zeros w k h c wd
  | bits => exact cfgAt_step_bits w k h c wd d hs
  | count => exact cfgAt_step_count w k h c wd d hs
  | done =>
    obtain ⟨rfl, rfl⟩ := hs
    exact cfgAt_step_end w k h c .done (Or.inl rfl)
  | dead =>
    obtain ⟨rfl, rfl⟩ := hs
    exact cfgAt_step_end w k h c .dead (Or.inr rfl)

end Bit

section Run

variable (w : List Bool)

/-- The configuration and the output at the time each prefix is consumed: the
closed form at the scan's state after the prefix, and nothing emitted. -/
theorem configs_cfgOf :
    ∀ k, ∀ h : k ≤ w.length,
      bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb)) (time (w.take k)) =
          cfgOf w k h ∧
        bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) (time (w.take k)) =
          [] := by
  refine Nat.rec ?_ ?_
  · intro _
    rw [List.take_zero, cfgOf_zero]
    exact ⟨configs_zero, rfl⟩
  · intro k ih h
    rw [time_take_succ w k (by omega), cfgOf_eq, scanFinal_take_succ w k (by omega)]
    refine run_seq _ _ _ _ _ (ih (by omega)) ?_
    rw [cfgOf_eq]
    cases k with
    | zero =>
      rw [List.take_zero, scanFinal_nil]
      exact cfgAt_step_zero w h
    | succ k => exact cfgAt_step_succ w k h _ (good_scanFinal _)

/-- At the input's end, from the closed form at the whole input: the machine
halts after {name}`Geb.BitTreeScanner.endCost` steps, and the symbol it emits is the
decision function's value. -/
theorem cfgOf_end :
    (bitTreeScanner.configs (cfgOf w w.length (Nat.le_refl _)) (endCost (scanFinal w))).state =
        none ∧
      bitTreeScanner.outputString (cfgOf w w.length (Nat.le_refl _)) (endCost (scanFinal w)) =
        [boolEmb (validBool w)] := by
  have hgood := good_scanFinal w
  rw [cfgOf_eq, List.take_length]
  rcases hs : scanFinal w with ⟨m, c, wd, d⟩
  rw [hs] at hgood
  have hval : validBool w = decide (m = .done) := by rw [validBool, hs]
  rw [hval]
  have hin := inputSymbol_end w (cfgAt w w.length (Nat.le_refl _) ⟨m, c, wd, d⟩)
    (cfgAt_inputPos_val _ _ _ _)
  have hone : ∀ (q : Fin 11) (b : Fin 4), (cfgAt w w.length (Nat.le_refl _) ⟨m, c, wd, d⟩).state =
      some q →
      bitTreeScanner.tr q none (cfgAt w w.length (Nat.le_refl _) ⟨m, c, wd, d⟩).workTapeSymbols =
        halt b →
      (bitTreeScanner.configs (cfgAt w w.length (Nat.le_refl _) ⟨m, c, wd, d⟩) 1).state = none ∧
        bitTreeScanner.outputString (cfgAt w w.length (Nat.le_refl _) ⟨m, c, wd, d⟩) 1 = [b] := by
    intro q b hq htr
    obtain ⟨h1, h2⟩ := step_halt _ q hq b (by rw [hin]; exact htr)
    refine ⟨h1, ?_⟩
    change bitTreeScanner.outputString _ (0 + 1) = [b]
    rw [outputString_succ, configs_zero, h2]
    rfl
  cases m with
  | term =>
    obtain ⟨rfl, rfl⟩ := hgood
    by_cases hn : w.length = 0
    · exact hone stFirst 0 (by rw [cfgAt_state, stateOf, ite_eq_left hn]) (tr_first_end _)
    · exact hone stMain 0 (by rw [cfgAt_state, stateOf, ite_eq_right hn]) (tr_main_end _)
  | zeros => exact hone stZeros 0 rfl (tr_zeros_end _)
  | bits =>
    dsimp only [Good] at hgood
    obtain ⟨hlt, r, hr⟩ := hgood
    refine hone stBits 0 rfl ?_
    rw [workTapeSymbols_eq]
    have hsym : tape2 w.length ⟨.bits, c, wd, d⟩ (head2 ⟨.bits, c, wd, d⟩) = some 2 := by
      rw [tape2, head2]
      change (if ((wd - d.length : ℕ) : ℤ) = 0 then (if w.length ≠ 0 then some 3 else none)
        else if 1 ≤ ((wd - d.length : ℕ) : ℤ) ∧
            ((wd - d.length : ℕ) : ℤ) ≤ ((wd - d.length : ℕ) : ℤ) then some 2
        else digitsAt ((wd - d.length : ℕ) : ℤ) d ((wd - d.length : ℕ) : ℤ)) = some 2
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, le_rfl⟩]
    change bitTreeScanner.tr stBits none
      ![tape1 w.length (c : ℤ), tape2 w.length ⟨.bits, c, wd, d⟩ (head2 ⟨.bits, c, wd, d⟩)] = halt 0
    rw [hsym]
    exact tr_bits_mark_end _
  | count =>
    dsimp only [Good] at hgood
    obtain ⟨hd, hlen⟩ := hgood
    have hn : w.length ≠ 0 := by
      intro h0
      rw [List.length_eq_zero_iff] at h0
      subst h0
      have := congrArg Scan.mode hs
      exact nomatch this
    rw [show endCost ⟨.count, c, wd, d⟩ = 2 * borrowLength d + 1 + 1 from rfl,
      cfgAt_count w w.length (Nat.le_refl _) c wd d hn]
    obtain ⟨hc, ho⟩ := configs_decrement w w.length (Nat.le_refl _) c false d hd
    rw [configs_add, hc, outputString_add_eq_append, ho, hc]
    obtain ⟨h1, h2⟩ := step_halt (returnCfg w w.length (Nat.le_refl _) c false d 0) stReturn rfl 0
      (by
        rw [inputSymbol_end w _ rfl, workTapeSymbols_eq]
        exact tr_return_base_end _)
    refine ⟨h1, ?_⟩
    change [] ++ bitTreeScanner.outputString _ (0 + 1) = _
    rw [outputString_succ, configs_zero, h2]
    rfl
  | done =>
    obtain ⟨rfl, rfl⟩ := hgood
    exact hone stDone 1 rfl (tr_done_end _)
  | dead =>
    obtain ⟨rfl, rfl⟩ := hgood
    exact hone stDead 0 rfl (tr_dead_end _)

/-- The machine halts after {lit}`time w + endCost (scanFinal w)` steps: the
bits' costs, and the steps from the input's end to the halt. -/
theorem halts_at :
    (bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb))
      (time w + endCost (scanFinal w))).state = none := by
  have h := (configs_cfgOf w w.length (Nat.le_refl _)).1
  rw [List.take_length] at h
  rw [configs_add, h]
  exact (cfgOf_end w).1

/-- Over the same steps the machine emits one symbol, the decision function's
value at the input. -/
theorem outputString_eq :
    bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb))
      (time w + endCost (scanFinal w)) = [boolEmb (validBool w)] := by
  have h := configs_cfgOf w w.length (Nat.le_refl _)
  rw [List.take_length] at h
  rw [outputString_add_eq_append, h.2, h.1, (cfgOf_end w).2]
  rfl

end Run

end Geb.BitTreeScanner
