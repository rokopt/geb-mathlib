/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fin.VecNotation
public import Geb.Prototypes.Computability.BitTreeScanner.Scan

set_option doc.verso true

/-!
# A one-pass tree scanner with a binary length counter

A deterministic multi-tape Turing machine deciding {name}`Geb.BitTreeScanner.validBool`
in a single left-to-right pass over the input. The machine is
{name}`Geb.BitTreeScanner.scanStep` on two work tapes: the first keeps the pending
count as its head's position, with a marker at cell {lit}`0`, as the scan of
the ranked-term encoding does; the second keeps a leaf's length in binary,
least significant digit at cell {lit}`1` beside a base marker at cell {lit}`0`,
written as the gamma code's digits arrive and counted down as the payload's
bits are read.

A decrement borrows outward from the lowest digit through the zeros below the
lowest one, flips that one, and returns to the base marker, where the next
payload bit is consumed; a decrement that runs off the digits' end into blank
finds the count at zero, and the machine erases the digits on its way back
and leaves the leaf. The zeros of the gamma code are counted by writing a mark
per zero, which the digits then overwrite from the top down, so that the
lowest digit lands at cell {lit}`1` and the machine knows the digits are
complete when it reaches the base marker.

## Main definitions

* {lit}`Geb.BitTreeScanner.boolEmb` — the input alphabet's embedding into the
  four-symbol machine alphabet.
* {lit}`Geb.BitTreeScanner.stFirst` through {lit}`Geb.BitTreeScanner.stDead` —
  the eleven states.
* {lit}`Geb.BitTreeScanner.advance`, {lit}`Geb.BitTreeScanner.stay`,
  {lit}`Geb.BitTreeScanner.halt` — the three shapes of transition: read a bit
  and continue, work without reading, or read the end and emit.
* {lit}`Geb.BitTreeScanner.bitTreeScanner` — the machine.
* {lit}`Geb.BitTreeScanner.digitsAt`, {lit}`Geb.BitTreeScanner.tape1`,
  {lit}`Geb.BitTreeScanner.tapeDigits`, {lit}`Geb.BitTreeScanner.tape2`,
  {lit}`Geb.BitTreeScanner.head2`, {lit}`Geb.BitTreeScanner.stateOf` — the
  tapes' contents, the second head and the state, as functions of the scan's
  state.
* {lit}`Geb.BitTreeScanner.cfgAt` — the closed-form configuration at a scan
  state after a prefix, which the runs between bits pass through at states the
  scan does not settle in.
* {lit}`Geb.BitTreeScanner.cfgOf` — the closed-form configuration after
  reading a prefix, at the scan's state after it and the work that state's
  last bit carries done.

## Main statements

* {lit}`Geb.BitTreeScanner.cfgAt_state`,
  {lit}`Geb.BitTreeScanner.cfgAt_inputPos_val`,
  {lit}`Geb.BitTreeScanner.cfgAt_workTapes_zero`,
  {lit}`Geb.BitTreeScanner.cfgAt_workTapes_one`,
  {lit}`Geb.BitTreeScanner.cfgOf_eq` — the field projections of the closed
  form.
* {lit}`Geb.BitTreeScanner.workTapeSymbols_eq` — a configuration's
  work-symbol function as a pair, the form the transition consumes.
* {lit}`Geb.BitTreeScanner.cfgOf_zero` — the closed form at the empty prefix
  is the initial configuration.

## Implementation notes

The machine alphabet is {lit}`Fin 4`: the two digits, which are also the input
bits' images, the zero-count mark {lit}`2` and the base marker {lit}`3`. The
first tape's marker is the digit {lit}`0`, as in the ranked-term scanner.

{lit}`cfgOf` is indexed by the prefix's length and reads the scan's state off
{name}`Geb.BitTreeScanner.scanFinal` at that prefix, so no proof over it inducts on
the input. It is the configuration after the prefix's last bit and the work
that bit carries before the next, {lit}`Geb.BitTreeScanner.cost`, so that between
two consecutive closed forms the machine runs exactly that bit's cost.

## Tags

Turing machine, tree, prefix code, Elias gamma code, binary counter, one pass
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

/-- The input alphabet's embedding into the machine alphabet: {lit}`false` to
{lit}`0` and {lit}`true` to {lit}`1`, the two digits. -/
def boolEmb : Bool ↪ Fin 4 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- The state of the first step, which writes both markers. -/
def stFirst : Fin 11 := ⟨0, by omega⟩

/-- The state expecting a tree. -/
def stMain : Fin 11 := ⟨1, by omega⟩

/-- The state reading a gamma code's zeros. -/
def stZeros : Fin 11 := ⟨2, by omega⟩

/-- The state reading a gamma code's digits. -/
def stBits : Fin 11 := ⟨3, by omega⟩

/-- The state borrowing outward in the decrement that turns the length read
into the payload remaining. -/
def stBorrowInit : Fin 11 := ⟨4, by omega⟩

/-- The state returning to the base marker in that decrement. -/
def stReturnInit : Fin 11 := ⟨5, by omega⟩

/-- The state borrowing outward in a payload bit's decrement, and the state at
the lowest digit between payload bits. -/
def stBorrow : Fin 11 := ⟨6, by omega⟩

/-- The state returning to the base marker in a payload bit's decrement, whose
step at the marker consumes the bit. -/
def stReturn : Fin 11 := ⟨7, by omega⟩

/-- The state erasing the digits after a decrement found the count at zero. -/
def stClear : Fin 11 := ⟨8, by omega⟩

/-- The state after the one expected tree completes. -/
def stDone : Fin 11 := ⟨9, by omega⟩

/-- The state of a failed scan. -/
def stDead : Fin 11 := ⟨10, by omega⟩

/-- A work tape's action: what to write, if anything, and how to move. -/
abbrev Act : Type := Option (Option (Fin 4)) × SignType

/-- The action that neither writes nor moves. -/
def idle : Act := (none, 0)

/-- The transition that reads a bit: the input head advances, the two work
tapes take their actions, nothing is emitted. -/
def advance (q : Fin 11) (a₀ a₁ : Act) : TransitionOut 2 (Fin 4) (Fin 11) :=
  { inputMove := 1, workActions := ![a₀, a₁], outS := none, q' := some q }

/-- The transition that works without reading: the input head stays, the two
work tapes take their actions, nothing is emitted. -/
def stay (q : Fin 11) (a₀ a₁ : Act) : TransitionOut 2 (Fin 4) (Fin 11) :=
  { inputMove := 0, workActions := ![a₀, a₁], outS := none, q' := some q }

/-- The transition that reads the end: nothing moves, the given symbol is
emitted, the machine halts. -/
def halt (b : Fin 4) : TransitionOut 2 (Fin 4) (Fin 11) :=
  { inputMove := 0, workActions := ![idle, idle], outS := some b, q' := none }

/-- The machine. Two work tapes: the pending count is the first's head
position, with a marker at cell {lit}`0` from the first step on; the second
holds a leaf's length, least significant digit at cell {lit}`1`, above a base
marker at cell {lit}`0` written at the first step. -/
def bitTreeScanner : MultiTapeTM 2 (Fin 4) (Fin 11) where
  q₀ := stFirst
  tr q inSym work :=
    if q = stFirst then
      match inSym with
      | some 1 => advance stMain (some (some 0), 1) (some (some 3), 0)
      | some _ => advance stZeros (some (some 0), 0) (some (some 3), 1)
      | none => halt 0
    else if q = stMain then
      match inSym with
      | some 1 => advance stMain (none, 1) idle
      | some _ => advance stZeros idle (none, 1)
      | none => halt 0
    else if q = stZeros then
      match inSym with
      | some 1 => advance stBits idle (some (some 1), -1)
      | some _ => advance stZeros idle (some (some 2), 1)
      | none => halt 0
    else if q = stBits then
      match work 1 with
      | some 3 => stay stBorrowInit idle (none, 1)
      | _ =>
        match inSym with
        | some b => advance stBits idle (some (some b), -1)
        | none => halt 0
    else if q = stBorrowInit then
      match work 1 with
      | some 0 => stay stBorrowInit idle (some (some 1), 1)
      | some 1 => stay stReturnInit idle (some (some 0), -1)
      | _ => stay stClear idle (none, -1)
    else if q = stReturnInit then
      match work 1 with
      | some 3 => stay stBorrow idle (none, 1)
      | _ => stay stReturnInit idle (none, -1)
    else if q = stBorrow then
      match work 1 with
      | some 0 => stay stBorrow idle (some (some 1), 1)
      | some 1 => stay stReturn idle (some (some 0), -1)
      | _ => stay stClear idle (none, -1)
    else if q = stReturn then
      match work 1 with
      | some 3 =>
        match inSym with
        | some _ => advance stBorrow idle (none, 1)
        | none => halt 0
      | _ => stay stReturn idle (none, -1)
    else if q = stClear then
      match work 1 with
      | some 3 =>
        match work 0 with
        | some _ => stay stDone idle idle
        | none => stay stMain (none, -1) idle
      | _ => stay stClear idle (some none, -1)
    else if q = stDone then
      match inSym with
      | some _ => advance stDead idle idle
      | none => halt 1
    else
      match inSym with
      | some _ => advance stDead idle idle
      | none => halt 0

/-- Digits laid out above a base cell, least significant first: the digit at
cell {lit}`base + i + 1` is the list's {lit}`i`-th, and cells outside are
blank. -/
def digitsAt (base : ℤ) (d : List Bool) (z : ℤ) : Option (Fin 4) :=
  if base < z ∧ z ≤ base + d.length then some (boolEmb (d.getD (z - base - 1).toNat false))
  else none

/-- The first tape: the count marker at cell {lit}`0` once any step has run,
blank elsewhere. -/
def tape1 (k : ℕ) (z : ℤ) : Option (Fin 4) := if k ≠ 0 ∧ z = 0 then some 0 else none

/-- The second tape holding digits: the base marker at cell {lit}`0` and the
digits from cell {lit}`1`. -/
def tapeDigits (d : List Bool) (z : ℤ) : Option (Fin 4) :=
  if z = 0 then some 3 else digitsAt 0 d z

/-- The second tape's content at a scan state after a prefix of the given
length: the base marker at cell {lit}`0` once any step has run; reading the
zeros or the digits, a mark per cell not yet holding a digit and the digits
read at the top of the claimed cells; in the countdown, the digits from cell
{lit}`1`; outside a leaf, blank. -/
def tape2 (k : ℕ) (s : Scan) (z : ℤ) : Option (Fin 4) :=
  if z = 0 then (if k ≠ 0 then some 3 else none)
  else match s.mode with
    | .zeros => if 1 ≤ z ∧ z ≤ s.width then some 2 else none
    | .bits =>
      if 1 ≤ z ∧ z ≤ (s.width - s.digits.length : ℕ) then some 2
      else digitsAt (s.width - s.digits.length : ℕ) s.digits z
    | .count => digitsAt 0 s.digits z
    | _ => none

/-- The second tape's head at a scan state: past the marks while reading the
zeros, at the next cell to fill while reading the digits, at the lowest digit
in the countdown, at the base cell outside a leaf. -/
def head2 (s : Scan) : ℤ :=
  match s.mode with
  | .zeros => s.width + 1
  | .bits => (s.width - s.digits.length : ℕ)
  | .count => 1
  | _ => 0

/-- The state a mode is run in after a prefix of the given length: the
expecting mode is the first-step state at the empty prefix and the main state
after it, and the countdown is the state at the lowest digit. -/
def stateOf (k : ℕ) : Mode → Fin 11
  | .term => if k = 0 then stFirst else stMain
  | .zeros => stZeros
  | .bits => stBits
  | .count => stBorrow
  | .done => stDone
  | .dead => stDead

/-- The closed-form configuration at a scan state after a prefix of length
{lit}`k`: the state of the scan's mode, the input head past the prefix, the
first tape's marker once any step has run and its head at the pending count,
and the second tape at the scan's state. -/
def cfgAt (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (s : Scan) :
    Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb) where
  state := some (stateOf k s.mode)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes := ![tape1 k, tape2 k s]
  workTapePos := ![(s.count : ℤ), head2 s]

/-- The configuration after reading the prefix of length {lit}`k` and doing
the work its last bit carries: {name}`cfgAt` at the scan's state after the
prefix. -/
def cfgOf (w : List Bool) (k : ℕ) (hk : k ≤ w.length) : Cfg 2 (Fin 4) (Fin 11) (w.map boolEmb) :=
  cfgAt w k hk (scanFinal (w.take k))

section CfgProjections

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (s : Scan)

/-- {name}`cfgAt`'s state is the state of the scan's mode. -/
@[simp] theorem cfgAt_state : (cfgAt w k hk s).state = some (stateOf k s.mode) := rfl

/-- {name}`cfgAt`'s input head is past the prefix. -/
@[simp] theorem cfgAt_inputPos_val : (cfgAt w k hk s).inputPos.val = k + 1 := rfl

/-- {name}`cfgAt`'s first tape is {name}`tape1`. -/
@[simp] theorem cfgAt_workTapes_zero : (cfgAt w k hk s).workTapes 0 = tape1 k := rfl

/-- {name}`cfgAt`'s second tape is {name}`tape2` at the scan's state. -/
@[simp] theorem cfgAt_workTapes_one : (cfgAt w k hk s).workTapes 1 = tape2 k s := rfl

/-- {name}`cfgOf` is {name}`cfgAt` at the scan's state after the prefix. -/
theorem cfgOf_eq : cfgOf w k hk = cfgAt w k hk (scanFinal (w.take k)) := rfl

end CfgProjections

/-- A two-tape configuration's work-symbol function as a pair, the form the
transition consumes. -/
theorem workTapeSymbols_eq {Symbol State : Type} {input : List Symbol}
    (cfg : Cfg 2 Symbol State input) :
    cfg.workTapeSymbols =
      ![cfg.workTapes 0 (cfg.workTapePos 0), cfg.workTapes 1 (cfg.workTapePos 1)] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- {name}`cfgOf` at the empty prefix is {name}`bitTreeScanner`'s initial
configuration. -/
theorem cfgOf_zero (w : List Bool) :
    cfgOf w 0 (Nat.zero_le _) = bitTreeScanner.initCfg (w.map boolEmb) := by
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i z
    match i with
    | 0 =>
      rw [cfgOf_eq, cfgAt_workTapes_zero, tape1]
      simp only [ne_eq, not_true_eq_false, false_and, ite_false]
      rfl
    | 1 =>
      rw [cfgOf_eq, cfgAt_workTapes_one]
      simp only [List.take_zero, scanFinal_nil, tape2, init, ne_eq, not_true_eq_false, ite_false]
      split_ifs <;> rfl
  · funext i
    match i with
    | 0 => rfl
    | 1 => rfl

end Geb.BitTreeScanner
