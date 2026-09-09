/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

set_option doc.verso true

/-!
# A machine for trees with Elias delta leaf lengths

Four work tapes hold the pending-tree count, the leading-zero count, the binary
length of a length, and the binary payload length. The first two counts use head
positions. The binary counters have a marked origin and most-significant-first
digits, followed by a blank. Appending a digit takes one transition. Decrementing
a positive counter sweeps left and returns right, retaining a zero-test result
in finite control. Thus a declared length never causes a unary allocation.

## Main definitions

* {lit}`machine` is the four-work-tape transition table.
* {lit}`borrow`, {lit}`sweepLeft` and {lit}`sweepRight` implement a decrement.
* {lit}`clear` erases both binary fields when a leaf finishes.

## Tags

Elias delta code, Turing machine, binary tree, countdown
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Binary input and output use zero and one; two marks a work-tape origin. -/
def boolEmb : Bool ↪ Fin 3 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- The embedding reads as the corresponding finite alphabet digit. -/
theorem boolEmb_apply (b : Bool) : boolEmb b = if b then 1 else 0 := rfl

/-- The finite control has room for both counter subroutines and their boolean flags. -/
abbrev Control := Fin 25

/-- Initialize all four origin markers. -/
def stInit : Control := 0
/-- Read a tree constructor. -/
def stTree : Control := 1
/-- Count the zero prefix of a delta code. -/
def stZeros : Control := 2
/-- Test whether the binary width field is complete. -/
def stSizeCheck : Control := 3
/-- Append one bit to the binary width field. -/
def stSizeBit : Control := 4
/-- Append one bit to the binary payload-length field. -/
def stLengthBit : Control := 5
/-- Consume one raw payload bit. -/
def stPayloadBit : Control := 6
/-- Erase the completed leaf's binary counters. -/
def stClear : Control := 7
/-- Test whether decrementing the pending count completed the tree. -/
def stLeaf : Control := 8
/-- Accept precisely if no input remains. -/
def stDone : Control := 9
/-- Reject at the end of the input. -/
def stDead : Control := 10
/-- Enter the selected countdown from its right-hand blank. -/
def stDecrement (value : Bool) : Control := if value then 12 else 11
/-- Borrow leftward, remembering whether a lower digit has become one. -/
def stBorrow (value seen : Bool) : Control :=
  if value then (if seen then 16 else 15) else (if seen then 14 else 13)
/-- Inspect the remaining higher digits while continuing to the origin. -/
def stLeft (value seen : Bool) : Control :=
  if value then (if seen then 20 else 19) else (if seen then 18 else 17)
/-- Return to the right-hand blank carrying the zero-test result. -/
def stRight (value seen : Bool) : Control :=
  if value then (if seen then 24 else 23) else (if seen then 22 else 21)

/-- Select either the width countdown or the payload countdown. -/
def counterTape (value : Bool) : Fin 4 := if value then 3 else 2

/-- A stationary state change with no output or tape writes. -/
def jump (q : Control) : TransitionOut 4 (Fin 3) Control where
  inputMove := 0
  workActions _ := (none, 0)
  outS := none
  q' := some q

/-- Consume one input bit and enter the given state. -/
def consume (q : Control) : TransitionOut 4 (Fin 3) Control :=
  { jump q with inputMove := 1 }

/-- Emit one boolean and halt. -/
def finish (b : Bool) : TransitionOut 4 (Fin 3) Control :=
  { jump stDead with outS := some (boolEmb b), q' := none }

-- ponytail: full-width countdown sweeps give quadratic time;
-- amortized local updates can improve it.
/-- Move or write only the selected binary counter. -/
def counterAction (value : Bool) (write : Option (Option (Fin 3)))
    (move : SignType) (q : Control) : TransitionOut 4 (Fin 3) Control :=
  { jump q with
    workActions := fun i ↦ if i = counterTape value then (write, move) else (none, 0) }

/-- Subtract one, changing trailing zeros to ones until the first one is reached. -/
def borrow (value seen : Bool) (work : Fin 4 → Option (Fin 3)) :
    TransitionOut 4 (Fin 3) Control :=
  if work (counterTape value) == some 2 then finish false
  else if work (counterTape value) == some 1 then
    counterAction value (some (some 0)) (-1) (stLeft value seen)
  else counterAction value (some (some 1)) (-1) (stBorrow value true)

/-- Inspect higher digits, remembering whether any result digit is one. -/
def sweepLeft (value seen : Bool) (work : Fin 4 → Option (Fin 3)) :
    TransitionOut 4 (Fin 3) Control :=
  if work (counterTape value) == some 2 then
    counterAction value none 1 (stRight value seen)
  else counterAction value none (-1)
    (stLeft value (seen || work (counterTape value) == some 1))

/-- Resume decoding after the selected countdown has been tested for zero. -/
def afterDecrement (value seen : Bool) : Control :=
  if value then (if seen then stPayloadBit else stClear)
  else (if seen then stLengthBit else stDecrement true)

/-- Return to the blank immediately after the selected counter's last digit. -/
def sweepRight (value seen : Bool) (work : Fin 4 → Option (Fin 3)) :
    TransitionOut 4 (Fin 3) Control :=
  if work (counterTape value) == none then jump (afterDecrement value seen)
  else counterAction value none 1 (stRight value seen)

/-- Clear both binary fields in parallel, leaving their origin markers in place. -/
def clear (work : Fin 4 → Option (Fin 3)) : TransitionOut 4 (Fin 3) Control :=
  if work 2 == some 2 && work 3 == some 2 then
    { jump stLeaf with
      workActions := fun i ↦
        if i = 0 then (none, -1)
        else if i = 1 then (none, 0)
        else (none, 1) }
  else
    { jump stClear with
      workActions := fun i ↦
        if i = 0 ∨ i = 1 ∨ work i = some 2 then (none, 0)
        else (some none, -1) }

/-- Read the next external bit once every internal subroutine has finished. -/
def read (q : Control) (b : Fin 3) : TransitionOut 4 (Fin 3) Control :=
  if q = stTree then
    if b == 1 then
      { consume stTree with workActions := fun i ↦ (none, if i = 0 then 1 else 0) }
    else
      { consume stZeros with
        workActions := fun i ↦ if i = 3 then (some (some 1), 1) else (none, 0) }
  else if q = stZeros then
    if b == 0 then
      { consume stZeros with workActions := fun i ↦ (none, if i = 1 then 1 else 0) }
    else
      { consume stSizeCheck with
        workActions := fun i ↦ if i = 2 then (some (some 1), 1) else (none, 0) }
  else if q = stSizeBit then
    { consume stSizeCheck with
      workActions := fun i ↦
        if i = 1 then (none, -1)
        else if i = 2 then (some (some b), 1)
        else (none, 0) }
  else if q = stLengthBit then
    { consume (stDecrement false) with
      workActions := fun i ↦ if i = 3 then (some (some b), 1) else (none, 0) }
  else if q = stPayloadBit then consume (stDecrement true)
  else consume stDead

/-- The four-work-tape recognizer for delta-length-prefixed bitstring leaves. -/
def machine : MultiTapeTM 4 (Fin 3) Control where
  q₀ := stInit
  tr q input work :=
    if q = stInit then
      { jump stTree with
        workActions := fun i ↦ (some (some 2), if i = 1 then 0 else 1) }
    else if q = stSizeCheck then
      jump (if work 1 == some 2 then stDecrement false else stSizeBit)
    else if q = stDecrement false then counterAction false none (-1) (stBorrow false false)
    else if q = stDecrement true then counterAction true none (-1) (stBorrow true false)
    else if q = stBorrow false false then borrow false false work
    else if q = stBorrow false true then borrow false true work
    else if q = stBorrow true false then borrow true false work
    else if q = stBorrow true true then borrow true true work
    else if q = stLeft false false then sweepLeft false false work
    else if q = stLeft false true then sweepLeft false true work
    else if q = stLeft true false then sweepLeft true false work
    else if q = stLeft true true then sweepLeft true true work
    else if q = stRight false false then sweepRight false false work
    else if q = stRight false true then sweepRight false true work
    else if q = stRight true false then sweepRight true false work
    else if q = stRight true true then sweepRight true true work
    else if q = stClear then clear work
    else if q = stLeaf then jump (if work 0 == some 2 then stDone else stTree)
    else match input with
      | none => finish (q == stDone)
      | some b => read q b

/-- Both counter-entry states resolve without inspecting input. -/
theorem tr_decrement (value : Bool) (input : Option (Fin 3))
    (work : Fin 4 → Option (Fin 3)) :
    machine.tr (stDecrement value) input work =
      counterAction value none (-1) (stBorrow value false) := by
  cases value <;> rfl

/-- Borrow-state resolution exposes only the selected counter's current digit. -/
theorem tr_borrow (value seen : Bool) (input : Option (Fin 3))
    (work : Fin 4 → Option (Fin 3)) :
    machine.tr (stBorrow value seen) input work = borrow value seen work := by
  cases value <;> cases seen <;> rfl

/-- Left-sweep states preserve their two finite-control parameters. -/
theorem tr_left (value seen : Bool) (input : Option (Fin 3))
    (work : Fin 4 → Option (Fin 3)) :
    machine.tr (stLeft value seen) input work = sweepLeft value seen work := by
  cases value <;> cases seen <;> rfl

/-- Right-sweep states preserve their two finite-control parameters. -/
theorem tr_right (value seen : Bool) (input : Option (Fin 3))
    (work : Fin 4 → Option (Fin 3)) :
    machine.tr (stRight value seen) input work = sweepRight value seen work := by
  cases value <;> cases seen <;> rfl

/-- Reading states resolve directly to the external-bit transition table. -/
theorem tr_read (q : Control) (b : Fin 3) (work : Fin 4 → Option (Fin 3))
    (hq : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead) :
    machine.tr q (some b) work = read q b := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- An external reading state emits the end-of-input verdict and halts. -/
theorem tr_end (q : Control) (work : Fin 4 → Option (Fin 3))
    (hq : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead) :
    machine.tr q none work = finish (q == stDone) := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every external-bit transition advances the input head exactly once. -/
theorem read_inputMove (q : Control) (b : Fin 3) : (read q b).inputMove = 1 := by
  simp only [read]
  split_ifs <;> rfl

/-- No external-bit transition emits output. -/
theorem read_outS (q : Control) (b : Fin 3) : (read q b).outS = none := by
  simp only [read]
  split_ifs <;> rfl

/-- Store a least-significant-first list as a marked most-significant-first tape. -/
def wordTape (bs : List Bool) (z : ℤ) : Option (Fin 3) :=
  if z = 0 then some 2
  else if 0 < z then (bs.reverse[z.toNat - 1]?).map boolEmb
  else none

/-- Change the selected countdown's contents, head, and control while retaining the context. -/
def counterCfg {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (value : Bool) (bs : List Bool) (q : Control) (p : ℕ) :
    Cfg 4 (Fin 3) Control input where
  state := some q
  inputPos := cfg.inputPos
  workTapes i := if i = counterTape value then wordTape bs else cfg.workTapes i
  workTapePos i := if i = counterTape value then p else cfg.workTapePos i

/-- The origin marker does not depend on the stored binary word. -/
theorem wordTape_zero (bs : List Bool) : wordTape bs 0 = some 2 := rfl

/-- A positive tape position reads the corresponding most-significant-first digit. -/
theorem wordTape_succ (bs : List Bool) (j : ℕ) :
    wordTape bs (j + 1 : ℕ) = (bs.reverse[j]?).map boolEmb := by
  unfold wordTape
  have hz : ((j + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hp : (0 : ℤ) < (j + 1 : ℕ) := by omega
  rw [ite_eq_right hz, ite_eq_left hp]
  rfl

/-- Immediately after the stored word the tape is blank. -/
theorem wordTape_end (bs : List Bool) : wordTape bs (bs.length + 1 : ℕ) = none := by
  rw [wordTape_succ, List.getElem?_eq_none (by rw [List.length_reverse])]
  rfl

/-- All work heads are confined to a common nonnegative interval. -/
def HeadBound {input : List (Fin 3)} (width : ℕ)
    (cfg : Cfg 4 (Fin 3) Control input) : Prop :=
  ∀ i, 0 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ width

end Geb.BitTree.Elias.Machine
