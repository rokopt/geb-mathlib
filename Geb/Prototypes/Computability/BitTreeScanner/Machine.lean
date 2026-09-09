/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fin.VecNotation
public import Geb.Prototypes.Computability.BitTreeScanner.Counter

set_option doc.verso true

/-!
# A two-pass tree scanner in logarithmic space

A deterministic three-tape Turing machine deciding {name}`Geb.BitTreeScanner.validBool`
in two passes over the input. The first pass counts the input's length in
binary on the third tape; the second is {name}`Geb.BitTreeScanner.scanStep` at the
bound that count's digits give, on the first two tapes: the first keeps the
pending count as a redundant binary counter ({name}`Geb.BitTreeScanner.Redundant.inc`,
{name}`Geb.BitTreeScanner.Redundant.dec`), the second a leaf's length in binary,
least significant digit at cell {lit}`1` beside a base marker at cell
{lit}`0`, written as the gamma code's digits arrive and counted down as the
payload's bits are read; the third's digits bound the zeros of a gamma code,
its head moving up one cell per zero and finding blank exactly when the code
is longer than any the input can hold.

Each counter's chain, a carry or a borrow, runs outward from the lowest digit
to the absorbing digit and back to the base marker, where the next step is
taken; the leaf counter's decrement that runs off the digits' end into blank
finds the count at zero, erases the digits on its way back and closes the
leaf, which decrements the pending count.

## Main definitions

* {lit}`Geb.BitTreeScanner.boolEmb` — the input alphabet's embedding into the
  four-symbol machine alphabet.
* {lit}`Geb.BitTreeScanner.stInit` through {lit}`Geb.BitTreeScanner.stDead` —
  the states.
* {lit}`Geb.BitTreeScanner.advance`, {lit}`Geb.BitTreeScanner.stay`,
  {lit}`Geb.BitTreeScanner.retreat`, {lit}`Geb.BitTreeScanner.halt` — the
  shapes of transition: read a bit and continue, work without reading, move
  back over the input, or read the end and emit.
* {lit}`Geb.BitTreeScanner.bitTreeScanner` — the machine.
* {lit}`Geb.BitTreeScanner.digitsAt`, {lit}`Geb.BitTreeScanner.tapeDigits`,
  {lit}`Geb.BitTreeScanner.tapeCount`, {lit}`Geb.BitTreeScanner.tapeLeaf`,
  {lit}`Geb.BitTreeScanner.headLeaf`, {lit}`Geb.BitTreeScanner.headRuler`,
  {lit}`Geb.BitTreeScanner.stateOf` — the tapes' contents, the heads and the
  state, as functions of the scan's state and the counter.
* {lit}`Geb.BitTreeScanner.seekCfg`, {lit}`Geb.BitTreeScanner.backCfg` — the
  closed-form configurations of the counting pass and of the return over the
  input.
* {lit}`Geb.BitTreeScanner.cfgAt` — the closed-form configuration of the scan
  at a scan state and a counter after a prefix, which the runs between bits
  pass through at states the scan does not settle in.
* {lit}`Geb.BitTreeScanner.cfgOf` — the closed-form configuration after
  reading a prefix, at the scan's state and counter after it and the work
  that state's last bit carries done.

## Main statements

* {lit}`Geb.BitTreeScanner.cfgAt_state`,
  {lit}`Geb.BitTreeScanner.cfgAt_inputPos_val`,
  {lit}`Geb.BitTreeScanner.cfgOf_eq` — the field projections of the closed
  form.
* {lit}`Geb.BitTreeScanner.workTapeSymbols_eq` — a configuration's
  work-symbol function as a triple, the form the transition consumes.
* {lit}`Geb.BitTreeScanner.tapeDigits_of_lt`,
  {lit}`Geb.BitTreeScanner.tapeDigits_of_ge`,
  {lit}`Geb.BitTreeScanner.tapeCount_of_lt`,
  {lit}`Geb.BitTreeScanner.tapeCount_of_ge` — the digit tapes cell by cell.

## Implementation notes

The machine alphabet is {lit}`Fin 4`: the digits {lit}`0` and {lit}`1`, which
are also the input bits' images, the digit {lit}`2` of the redundant counter,
which on the leaf's tape is the mark counting a gamma code's zeros, and the
base marker {lit}`3`.

{lit}`cfgOf` is indexed by the prefix's length and reads the scan's state and
the counter off {name}`Geb.BitTreeScanner.scanAt` and {name}`Geb.BitTreeScanner.treeAt` at
that prefix, so no proof over it inducts on the input. It is the
configuration after the prefix's last bit and the work that bit carries
before the next, {lit}`Geb.BitTreeScanner.cost`, so that between two consecutive
closed forms the machine runs exactly that bit's cost.

## Tags

Turing machine, tree, prefix code, Elias gamma code, binary counter,
logarithmic space
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

/-- The input alphabet's embedding into the machine alphabet: {lit}`false` to
{lit}`0` and {lit}`true` to {lit}`1`, the two digits. -/
def boolEmb : Bool ↪ Fin 4 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- A counter digit as a machine symbol. -/
def digitEmb (d : Redundant.Digit) : Fin 4 := ⟨d.val, by omega⟩

/-- The number of states. -/
abbrev stateCount : ℕ := 21

/-- The state of the first step, which writes the base markers. -/
def stInit : Fin stateCount := ⟨0, by decide⟩

/-- The state of the counting pass, at the lowest digit of the input's
length. -/
def stSeek : Fin stateCount := ⟨1, by decide⟩

/-- The state carrying outward in the counting pass. -/
def stSeekCarry : Fin stateCount := ⟨2, by decide⟩

/-- The state returning to the base marker in the counting pass. -/
def stSeekBack : Fin stateCount := ⟨3, by decide⟩

/-- The state returning over the input to its start. -/
def stBack : Fin stateCount := ⟨4, by decide⟩

/-- The state expecting a tree. -/
def stMain : Fin stateCount := ⟨5, by decide⟩

/-- The state carrying outward in the pending count's increment. -/
def stIncCarry : Fin stateCount := ⟨6, by decide⟩

/-- The state returning to the base marker in the pending count's
increment. -/
def stIncBack : Fin stateCount := ⟨7, by decide⟩

/-- The state reading a gamma code's zeros. -/
def stZeros : Fin stateCount := ⟨8, by decide⟩

/-- The state reading a gamma code's digits. -/
def stBits : Fin stateCount := ⟨9, by decide⟩

/-- The state borrowing outward in the decrement that turns the length read
into the payload remaining. -/
def stBorrowInit : Fin stateCount := ⟨10, by decide⟩

/-- The state returning to the base marker in that decrement. -/
def stReturnInit : Fin stateCount := ⟨11, by decide⟩

/-- The state borrowing outward in a payload bit's decrement, and the state at
the lowest digit between payload bits. -/
def stBorrow : Fin stateCount := ⟨12, by decide⟩

/-- The state returning to the base marker in a payload bit's decrement, whose
step at the marker consumes the bit. -/
def stReturn : Fin stateCount := ⟨13, by decide⟩

/-- The state erasing the leaf's digits after a decrement found the count at
zero, whose step at the marker begins the pending count's decrement. -/
def stClear : Fin stateCount := ⟨14, by decide⟩

/-- The state borrowing outward in the pending count's decrement. -/
def stDecBorrow : Fin stateCount := ⟨15, by decide⟩

/-- The state testing whether the digit a borrow lowered to zero was the
top. -/
def stDecTop : Fin stateCount := ⟨16, by decide⟩

/-- The state erasing a top digit lowered to zero. -/
def stDecErase : Fin stateCount := ⟨17, by decide⟩

/-- The state returning to the base marker in the pending count's
decrement. -/
def stDecBack : Fin stateCount := ⟨18, by decide⟩

/-- The state after the one expected tree completes. -/
def stDone : Fin stateCount := ⟨19, by decide⟩

/-- The state of a failed scan. -/
def stDead : Fin stateCount := ⟨20, by decide⟩

/-- A work tape's action: what to write, if anything, and how to move. -/
abbrev Act : Type := Option (Option (Fin 4)) × SignType

/-- The action that neither writes nor moves. -/
def idle : Act := (none, 0)

/-- The transition that reads a bit: the input head advances, the work tapes
take their actions, nothing is emitted. -/
def advance (q : Fin stateCount) (a₀ a₁ a₂ : Act) :
    TransitionOut 3 (Fin 4) (Fin stateCount) :=
  { inputMove := 1, workActions := ![a₀, a₁, a₂], outS := none, q' := some q }

/-- The transition that works without reading: the input head stays, the work
tapes take their actions, nothing is emitted. -/
def stay (q : Fin stateCount) (a₀ a₁ a₂ : Act) : TransitionOut 3 (Fin 4) (Fin stateCount) :=
  { inputMove := 0, workActions := ![a₀, a₁, a₂], outS := none, q' := some q }

/-- The transition that moves back over the input: the input head retreats,
the work tapes take their actions, nothing is emitted. -/
def retreat (q : Fin stateCount) (a₀ a₁ a₂ : Act) :
    TransitionOut 3 (Fin 4) (Fin stateCount) :=
  { inputMove := -1, workActions := ![a₀, a₁, a₂], outS := none, q' := some q }

/-- The transition that reads the end: nothing moves, the given symbol is
emitted, the machine halts. -/
def halt (b : Fin 4) : TransitionOut 3 (Fin 4) (Fin stateCount) :=
  { inputMove := 0, workActions := ![idle, idle, idle], outS := some b, q' := none }

/-- The machine. Three work tapes, each with a base marker at cell {lit}`0`
from the first step on: the first holds the pending count as a redundant
counter, least significant digit at cell {lit}`1`, its head resting there;
the second a leaf's length, least significant digit at cell {lit}`1`; the
third the input's length in binary, least significant digit at cell
{lit}`1`, its head resting at the base outside a gamma code. -/
def bitTreeScanner : MultiTapeTM 3 (Fin 4) (Fin stateCount) where
  q₀ := stInit
  tr q inSym work :=
    if q = stInit then
      stay stSeek (some (some 3), 1) (some (some 3), 0) (some (some 3), 1)
    else if q = stSeek then
      match inSym with
      | some _ =>
        match work 2 with
        | some 1 => stay stSeekCarry idle idle (some (some 0), 1)
        | _ => advance stSeek idle idle (some (some 1), 0)
      | none => retreat stBack idle idle (none, -1)
    else if q = stSeekCarry then
      match work 2 with
      | some 1 => stay stSeekCarry idle idle (some (some 0), 1)
      | _ => stay stSeekBack idle idle (some (some 1), -1)
    else if q = stSeekBack then
      match work 2 with
      | some 3 => advance stSeek idle idle (none, 1)
      | _ => stay stSeekBack idle idle (none, -1)
    else if q = stBack then
      match inSym with
      | some _ => retreat stBack idle idle idle
      | none => advance stMain idle idle idle
    else if q = stMain then
      match inSym with
      | some 1 =>
        match work 0 with
        | some 2 => stay stIncCarry (some (some 1), 1) idle idle
        | some 1 => advance stMain (some (some 2), 0) idle idle
        | _ => advance stMain (some (some 1), 0) idle idle
      | some _ => advance stZeros idle (none, 1) idle
      | none => halt 0
    else if q = stIncCarry then
      match work 0 with
      | some 2 => stay stIncCarry (some (some 1), 1) idle idle
      | some 1 => stay stIncBack (some (some 2), -1) idle idle
      | _ => stay stIncBack (some (some 1), -1) idle idle
    else if q = stIncBack then
      match work 0 with
      | some 3 =>
        match inSym with
        | some _ => advance stMain (none, 1) idle idle
        | none => halt 0
      | _ => stay stIncBack (none, -1) idle idle
    else if q = stZeros then
      match inSym with
      | some 1 => advance stBits idle (some (some 1), -1) idle
      | some _ =>
        match work 2 with
        | some _ => advance stZeros idle (some (some 2), 1) (none, 1)
        | none => advance stDead idle idle idle
      | none => halt 0
    else if q = stBits then
      match work 1 with
      | some 3 => stay stBorrowInit idle (none, 1) idle
      | _ =>
        match inSym with
        | some b => advance stBits idle (some (some b), -1) (none, -1)
        | none => halt 0
    else if q = stBorrowInit then
      match work 1 with
      | some 0 => stay stBorrowInit idle (some (some 1), 1) idle
      | some 1 => stay stReturnInit idle (some (some 0), -1) idle
      | _ => stay stClear idle (none, -1) idle
    else if q = stReturnInit then
      match work 1 with
      | some 3 => stay stBorrow idle (none, 1) idle
      | _ => stay stReturnInit idle (none, -1) idle
    else if q = stBorrow then
      match work 1 with
      | some 0 => stay stBorrow idle (some (some 1), 1) idle
      | some 1 => stay stReturn idle (some (some 0), -1) idle
      | _ => stay stClear idle (none, -1) idle
    else if q = stReturn then
      match work 1 with
      | some 3 =>
        match inSym with
        | some _ => advance stBorrow idle (none, 1) idle
        | none => halt 0
      | _ => stay stReturn idle (none, -1) idle
    else if q = stClear then
      match work 1 with
      | some 3 =>
        match work 0 with
        | none => stay stDone idle idle idle
        | some 2 => stay stMain (some (some 1), 0) idle idle
        | some 1 => stay stDecTop (some (some 0), 1) idle idle
        | _ => stay stDecBorrow (some (some 1), 1) idle idle
      | _ => stay stClear idle (some none, -1) idle
    else if q = stDecBorrow then
      match work 0 with
      | some 0 => stay stDecBorrow (some (some 1), 1) idle idle
      | some 1 => stay stDecTop (some (some 0), 1) idle idle
      | some 2 => stay stDecBack (some (some 1), -1) idle idle
      | _ => stay stDecBack (none, -1) idle idle
    else if q = stDecTop then
      match work 0 with
      | none => stay stDecErase (none, -1) idle idle
      | some _ => stay stDecBack (none, -1) idle idle
    else if q = stDecErase then
      stay stDecBack (some none, -1) idle idle
    else if q = stDecBack then
      match work 0 with
      | some 3 => stay stMain (none, 1) idle idle
      | _ => stay stDecBack (none, -1) idle idle
    else if q = stDone then
      match inSym with
      | some _ => advance stDead idle (none, 1) idle
      | none => halt 1
    else
      match inSym with
      | some _ => advance stDead idle idle idle
      | none => halt 0

section Tapes

/-- Digits laid out above a base cell, least significant first: the digit at
cell {lit}`base + i + 1` is the list's {lit}`i`-th, and cells outside are
blank. -/
def digitsAt (base : ℤ) (d : List Bool) (z : ℤ) : Option (Fin 4) :=
  if base < z ∧ z ≤ base + d.length then some (boolEmb (d.getD (z - base - 1).toNat false))
  else none

/-- A tape holding binary digits: the base marker at cell {lit}`0` and the
digits from cell {lit}`1`. -/
def tapeDigits (d : List Bool) (z : ℤ) : Option (Fin 4) :=
  if z = 0 then some 3 else digitsAt 0 d z

/-- The digit tape at a cell holding a digit. -/
theorem tapeDigits_of_lt (d : List Bool) (i : ℕ) (hi : i < d.length) :
    tapeDigits d (i + 1) = some (boolEmb (d.getD i false)) := by
  rw [tapeDigits, ite_eq_right (by omega), digitsAt, ite_eq_left ⟨by omega, by omega⟩,
    show ((i : ℤ) + 1 - 0 - 1).toNat = i by omega]

/-- The digit tape above the digits. -/
theorem tapeDigits_of_ge (d : List Bool) (z : ℤ) (hz : (d.length : ℤ) < z) :
    tapeDigits d z = none := by
  rw [tapeDigits, ite_eq_right (by omega), digitsAt, ite_eq_right (by omega)]

/-- The digit tape at the base marker. -/
@[simp] theorem tapeDigits_zero (d : List Bool) : tapeDigits d 0 = some 3 := rfl

/-- The digit tape below the base marker. -/
theorem tapeDigits_of_neg (d : List Bool) (z : ℤ) (hz : z < 0) : tapeDigits d z = none := by
  rw [tapeDigits, ite_eq_right (by omega), digitsAt, ite_eq_right (by omega)]

/-- The ruler tape's cells hold a digit or the base marker up to the digits'
length. -/
theorem tapeDigits_eq_some (d : List Bool) (z : ℤ) (h0 : 0 ≤ z) (hz : z ≤ d.length) :
    ∃ x, tapeDigits d z = some x := by
  by_cases hz0 : z = 0
  · exact ⟨3, by rw [hz0, tapeDigits_zero]⟩
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, z = i + 1 := ⟨(z - 1).toNat, by omega⟩
    exact ⟨_, tapeDigits_of_lt d i (by omega)⟩

/-- The tape holding the pending count: the base marker at cell {lit}`0` and
the counter's digits from cell {lit}`1`. -/
def tapeCount (l : List Redundant.Digit) (z : ℤ) : Option (Fin 4) :=
  if z = 0 then some 3
  else if 1 ≤ z ∧ z ≤ l.length then some (digitEmb (l.getD (z - 1).toNat 0)) else none

/-- The count tape at a cell holding a digit. -/
theorem tapeCount_of_lt (l : List Redundant.Digit) (i : ℕ) (hi : i < l.length) :
    tapeCount l (i + 1) = some (digitEmb (l.getD i 0)) := by
  rw [tapeCount, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
    show ((i : ℤ) + 1 - 1).toNat = i by omega]

/-- The count tape above the digits. -/
theorem tapeCount_of_ge (l : List Redundant.Digit) (z : ℤ) (hz : (l.length : ℤ) < z) :
    tapeCount l z = none := by
  rw [tapeCount, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The count tape at the base marker. -/
@[simp] theorem tapeCount_zero (l : List Redundant.Digit) : tapeCount l 0 = some 3 := rfl

/-- The count tape below the base marker. -/
theorem tapeCount_of_neg (l : List Redundant.Digit) (z : ℤ) (hz : z < 0) :
    tapeCount l z = none := by
  rw [tapeCount, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The tape holding a leaf's digits at a scan state: the base marker at cell
{lit}`0`; reading the zeros, and after failure, a mark per zero read; reading
the digits, a mark per cell not yet holding a digit and the digits read at
the top of the claimed cells; in the countdown, the digits from cell
{lit}`1`; otherwise blank. -/
def tapeLeaf (s : Scan) (z : ℤ) : Option (Fin 4) :=
  if z = 0 then some 3
  else match s.mode with
    | .zeros | .dead => if 1 ≤ z ∧ z ≤ s.width then some 2 else none
    | .bits =>
      if 1 ≤ z ∧ z ≤ (s.width - s.digits.length : ℕ) then some 2
      else digitsAt (s.width - s.digits.length : ℕ) s.digits z
    | .count => digitsAt 0 s.digits z
    | _ => none

/-- The leaf tape's head at a scan state: past the marks while reading the
zeros and after failure, at the next cell to fill while reading the digits,
at the lowest digit in the countdown, at the base cell otherwise. -/
def headLeaf (s : Scan) : ℤ :=
  match s.mode with
  | .zeros | .dead => s.width + 1
  | .bits => (s.width - s.digits.length : ℕ)
  | .count => 1
  | _ => 0

/-- The ruler tape's head at a scan state: at the cell of the width while
reading the zeros and after failure, alongside the leaf tape's head while
reading the digits, at the base cell otherwise. -/
def headRuler (s : Scan) : ℤ :=
  match s.mode with
  | .zeros | .dead => s.width
  | .bits => (s.width - s.digits.length : ℕ)
  | _ => 0

section Heads

variable (c wd : ℕ) (d : List Bool)

/-- The leaf head outside a leaf. -/
@[simp] theorem headLeaf_term : headLeaf ⟨.term, c, wd, d⟩ = 0 := rfl

/-- The leaf head while reading the zeros. -/
@[simp] theorem headLeaf_zeros : headLeaf ⟨.zeros, c, wd, d⟩ = wd + 1 := rfl

/-- The leaf head while reading the digits. -/
@[simp] theorem headLeaf_bits : headLeaf ⟨.bits, c, wd, d⟩ = ((wd - d.length : ℕ) : ℤ) := rfl

/-- The leaf head in the countdown. -/
@[simp] theorem headLeaf_count : headLeaf ⟨.count, c, wd, d⟩ = 1 := rfl

/-- The leaf head after completion. -/
@[simp] theorem headLeaf_done : headLeaf ⟨.done, c, wd, d⟩ = 0 := rfl

/-- The leaf head after failure. -/
@[simp] theorem headLeaf_dead : headLeaf ⟨.dead, c, wd, d⟩ = wd + 1 := rfl

/-- The ruler head outside a leaf. -/
@[simp] theorem headRuler_term : headRuler ⟨.term, c, wd, d⟩ = 0 := rfl

/-- The ruler head while reading the zeros. -/
@[simp] theorem headRuler_zeros : headRuler ⟨.zeros, c, wd, d⟩ = wd := rfl

/-- The ruler head while reading the digits. -/
@[simp] theorem headRuler_bits : headRuler ⟨.bits, c, wd, d⟩ = ((wd - d.length : ℕ) : ℤ) := rfl

/-- The ruler head in the countdown. -/
@[simp] theorem headRuler_count : headRuler ⟨.count, c, wd, d⟩ = 0 := rfl

/-- The ruler head after completion. -/
@[simp] theorem headRuler_done : headRuler ⟨.done, c, wd, d⟩ = 0 := rfl

/-- The ruler head after failure. -/
@[simp] theorem headRuler_dead : headRuler ⟨.dead, c, wd, d⟩ = wd := rfl

end Heads

/-- The state a mode is run in: the countdown is the state at the lowest
digit. -/
def stateOf : Mode → Fin stateCount
  | .term => stMain
  | .zeros => stZeros
  | .bits => stBits
  | .count => stBorrow
  | .done => stDone
  | .dead => stDead

end Tapes

section Cfg

variable (w : List Bool)

/-- The closed-form configuration of the counting pass after {lit}`i` input
bits: the count's digits on the ruler tape, its head at the lowest digit. -/
def seekCfg (i : ℕ) (hi : i ≤ w.length) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stSeek
  inputPos := ⟨i + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount [], tapeDigits [], tapeDigits i.bits]
  workTapePos := ![1, 0, 1]

/-- The closed-form configuration of the return over the input, at input
position {lit}`i`. -/
def backCfg (i : ℕ) (hi : i ≤ w.length) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some stBack
  inputPos := ⟨i, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount [], tapeDigits [], tapeDigits w.length.bits]
  workTapePos := ![1, 0, 0]

/-- The closed-form configuration of the scan at a scan state and a counter
after a prefix of length {lit}`k`: the state of the scan's mode, the input
head past the prefix, the count tape at the counter with its head at the
lowest digit, the leaf tape and the ruler's head at the scan's state. -/
def cfgAt (k : ℕ) (hk : k ≤ w.length) (s : Scan) (l : List Redundant.Digit) :
    Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) where
  state := some (stateOf s.mode)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tapeCount l, tapeLeaf s, tapeDigits w.length.bits]
  workTapePos := ![1, headLeaf s, headRuler s]

/-- The configuration after reading the prefix of length {lit}`k` and doing
the work its last bit carries: {name}`cfgAt` at the scan's state and counter
after the prefix. -/
def cfgOf (k : ℕ) (hk : k ≤ w.length) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) :=
  cfgAt w k hk (scanAt (bound w) (w.take k)) (treeAt (bound w) (w.take k))

variable (k : ℕ) (hk : k ≤ w.length) (s : Scan) (l : List Redundant.Digit)

/-- {name}`cfgAt`'s input head is past the prefix. -/
@[simp] theorem cfgAt_inputPos_val : (cfgAt w k hk s l).inputPos.val = k + 1 := rfl

/-- {name}`cfgOf` is {name}`cfgAt` at the scan's state and counter after the
prefix. -/
theorem cfgOf_eq :
    cfgOf w k hk = cfgAt w k hk (scanAt (bound w) (w.take k)) (treeAt (bound w) (w.take k)) :=
  rfl

/-- A three-tape configuration's work-symbol function as a triple, the form
the transition consumes. -/
theorem workTapeSymbols_eq {Symbol State : Type} {input : List Symbol}
    (cfg : Cfg 3 Symbol State input) :
    cfg.workTapeSymbols =
      ![cfg.workTapes 0 (cfg.workTapePos 0), cfg.workTapes 1 (cfg.workTapePos 1),
        cfg.workTapes 2 (cfg.workTapePos 2)] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

end Cfg

end Geb.BitTreeScanner
