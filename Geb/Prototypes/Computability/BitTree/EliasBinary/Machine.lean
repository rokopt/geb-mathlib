/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Layout

set_option doc.verso true

/-!
# A binary-counter machine for Elias-length trees

The machine reads the input twice. The first pass increments both pending counters once per
bit, so the forks tape afterwards spans the binary size of the input length; its head then
serves as a ruler bounding the zero run of a delta header and the width of a length field.
The second pass is the streaming scan. A size register and a counter from one count the
length field; a length register and a counter from one count the payload. All six increment
sites share the transitions of {name (full := Geb.BitTree.EliasBinary.carry)}`carry` and
{name (full := Geb.BitTree.EliasBinary.returnTr)}`returnTr`, distinguished by their
layouts and continuation states.

## Main definitions

* {lit}`machine` is the nine-work-tape transition table.
* {lit}`siteLayout`, {lit}`siteSel`, {lit}`siteZero` and {lit}`siteNext` describe the six
  increment sites.
* {lit}`stCarry` and {lit}`stReturn` name the two states of each site.
* {lit}`HeadBound` bounds every work-head position.

## Main statements

* {lit}`tr_carry` and {lit}`tr_return` resolve the site transitions.
* The remaining {lit}`tr_` statements resolve every other state.

## Implementation notes

Tapes zero to two hold the pending pair, three to five the size pair, six to eight the
length pair. The pending and size pairs keep their least significant digits at the origin;
the length pair keeps it at the last cell written, so its digits extend leftwards. Symbols
two and three are tagged digits. A mismatch tape carries a marker at its origin.

## Tags

Turing machine, binary counter, Elias delta code, bitstring tree
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin flipped mismatchMove)

/-- Write the tagged digits and the mismatch markers. -/
def stInit : Control := 0
/-- First pass: count the input bits into both pending counters. -/
def stCount : Control := 1
/-- Move the input head back to the left end. -/
def stRewind : Control := 2
/-- Expect a tree tag. -/
def stTree : Control := 3
/-- Read the zero run of a delta header. -/
def stZeros : Control := 4
/-- Move the size head to the zero count while returning the ruler head. -/
def stSizeSetup : Control := 5
/-- Write the leading one of the size register. -/
def stSizeInit : Control := 6
/-- Read one bit of the size field. -/
def stSizeBit : Control := 7
/-- Read one bit of the length field. -/
def stLengthBit : Control := 8
/-- Step the length head back onto the least significant digit. -/
def stLengthEnd : Control := 9
/-- Tag the least significant digit of the length register and start its counter. -/
def stTagLsb : Control := 10
/-- Erase the size pair. -/
def stEraseSize : Control := 11
/-- Return the size heads to the origin. -/
def stReturnSize : Control := 12
/-- Return the ruler head to the origin. -/
def stReturnF : Control := 13
/-- Read one payload bit. -/
def stPayloadBit : Control := 14
/-- Erase the length pair. -/
def stEraseLength : Control := 15
/-- The complete tree has ended; only end of input is accepted. -/
def stDone : Control := 16
/-- A malformed prefix has been found. -/
def stDead : Control := 17

/-- The carry state of an increment site. -/
def stCarry (k : Fin 6) : Control := ⟨18 + 2 * k.val, by omega⟩
/-- The return state of an increment site. -/
def stReturn (k : Fin 6) : Control := ⟨19 + 2 * k.val, by omega⟩

/-- The pending pair: forks plus one, completed leaves, and their mismatch. -/
def pendingLayout : Layout := ⟨0, 1, 2, 1⟩
/-- The size pair: the size register, the length-field counter, and their mismatch. -/
def sizeLayout : Layout := ⟨3, 4, 5, 1⟩
/-- The length pair, extending leftwards: the length register, the payload counter, and
their mismatch. -/
def lengthLayout : Layout := ⟨6, 7, 8, -1⟩

/-- The layout of each increment site. -/
def siteLayout : Fin 6 → Layout
  | 0 => pendingLayout
  | 1 => pendingLayout
  | 2 => pendingLayout
  | 3 => pendingLayout
  | 4 => sizeLayout
  | 5 => lengthLayout

/-- Whether each site increments the second tape of its pair. -/
def siteSel : Fin 6 → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => true

/-- The continuation of each site when the counters become equal. -/
def siteZero : Fin 6 → Control
  | 0 => stDead
  | 1 => stDead
  | 2 => stDead
  | 3 => stDone
  | 4 => stLengthEnd
  | 5 => stEraseLength

/-- The continuation of each site when the counters remain unequal. -/
def siteNext : Fin 6 → Control
  | 0 => stCarry 1
  | 1 => stCount
  | 2 => stTree
  | 3 => stTree
  | 4 => stLengthBit
  | 5 => stPayloadBit

/-- A transition consuming one input symbol without changing work tapes. -/
def consume (q : Control) : TransitionOut 9 (Fin 4) Control where
  inputMove := 1
  workActions _ := (none, 0)
  outS := none
  q' := some q

/-- A stationary transition with the given work actions. -/
def act (q : Control) (w : Fin 9 → Option (Option (Fin 4)) × SignType) :
    TransitionOut 9 (Fin 4) Control where
  inputMove := 0
  workActions := w
  outS := none
  q' := some q

/-- A transition consuming one input symbol with the given work actions. -/
def consumeAct (q : Control) (w : Fin 9 → Option (Option (Fin 4)) × SignType) :
    TransitionOut 9 (Fin 4) Control where
  inputMove := 1
  workActions := w
  outS := none
  q' := some q

/-- Move the input head one cell left while rewinding. -/
def rewindTr : TransitionOut 9 (Fin 4) Control where
  inputMove := -1
  workActions _ := (none, 0)
  outS := none
  q' := some stRewind

/-- Emit one boolean and halt. -/
def finish (b : Bool) : TransitionOut 9 (Fin 4) Control where
  inputMove := 0
  workActions _ := (none, 0)
  outS := some (boolEmb b)
  q' := none

/-- The untagged digit symbol of a bit. -/
def plain (b : Bool) : Fin 4 := if b then 1 else 0

/-- The tagged digit symbol of a bit. -/
def tagged (b : Bool) : Fin 4 := if b then 3 else 2

/-- Work actions of a transition. -/
abbrev Actions := Fin 9 → Option (Option (Fin 4)) × SignType

/-- No work action. -/
def stay : Actions := fun _ ↦ (none, 0)

/-- The input-reading transitions of the second pass: the next state and the work actions. -/
def scanTr (q : Control) (b : Bool) (work : Fin 9 → Option (Fin 4)) : Control × Actions :=
  if q = stTree then (if b then stCarry 2 else stZeros, stay)
  else if q = stZeros then
    if b then (if origin (work 0) then stCarry 3 else stSizeSetup, stay)
    else if work 0 = none then (stDead, stay)
    else (stZeros, fun i ↦ (none, if i = 0 then 1 else 0))
  else if q = stSizeBit then
    if origin (work 3) then
      (stLengthBit, fun i ↦
        if i = 3 then (some (some (tagged b)), 0)
        else if i = 5 then (none, if b then mismatchMove (work 3) (work 4) else 0)
        else if i = 6 then (some (some 1), 1)
        else if i = 7 then (none, 1)
        else if i = 8 then (none, 1)
        else (none, 0))
    else
      (stSizeBit, fun i ↦
        if i = 3 then (some (some (plain b)), -1)
        else if i = 5 then (none, if b then 1 else 0)
        else (none, 0))
  else if q = stLengthBit then
    if work 0 = none then (stDead, stay)
    else (stCarry 4, fun i ↦
      if i = 0 then (none, 1)
      else if i = 6 then (some (some (plain b)), 1)
      else if i = 7 then (none, 1)
      else if i = 8 then (none, if b then 1 else 0)
      else (none, 0))
  else if q = stPayloadBit then (stCarry 5, stay)
  else (stDead, stay)

/-- The stationary transitions between input bits: the next state and the work actions. -/
def phaseTr (q : Control) (work : Fin 9 → Option (Fin 4)) : Control × Actions :=
  if q = stSizeSetup then
    if origin (work 0) then
      (stSizeInit, fun i ↦
        if i = 3 then (some (some 1), -1) else if i = 5 then (none, 1) else (none, 0))
    else (stSizeSetup, fun i ↦ (none, if i = 0 then -1 else if i = 3 then 1 else 0))
  else if q = stSizeInit then
    (stSizeBit, fun i ↦ if i = 4 then (some (some 1), 0)
      else if i = 5 then (none, 1) else (none, 0))
  else if q = stLengthEnd then (stTagLsb, fun i ↦ (none, if i = 6 ∨ i = 7 then -1 else 0))
  else if q = stTagLsb then
    (stEraseSize, fun i ↦
      if i = 6 then (some (some (tagged (digit (work 6)))), 0)
      else if i = 7 then (some (some 1), 0)
      else if i = 8 then (none, mismatchMove (work 6) (work 7))
      else (none, 0))
  else if q = stEraseSize then
    if work 3 = none then (stReturnSize, stay)
    else (stEraseSize, fun i ↦
      if i = 3 then (some (if origin (work 3) then some 2 else none), 1)
      else if i = 4 then (some none, 1) else (none, 0))
  else if q = stReturnSize then
    if origin (work 3) then (stReturnF, stay)
    else (stReturnSize, fun i ↦ (none, if i = 3 ∨ i = 4 then -1 else 0))
  else if q = stReturnF then
    if origin (work 0) then (stPayloadBit, stay)
    else (stReturnF, fun i ↦ (none, if i = 0 then -1 else 0))
  else if q = stEraseLength then
    if work 6 = none then (stCarry 3, fun i ↦ (none, if i = 6 ∨ i = 7 then 1 else 0))
    else (stEraseLength, fun i ↦ if i = 6 ∨ i = 7 then (some none, -1) else (none, 0))
  else (stDead, stay)

/-- The initialization transition. -/
def initTr : TransitionOut 9 (Fin 4) Control :=
  act stCount (fun i ↦
    if i = 0 then (some (some 3), 0)
    else if i = 1 then (some (some 2), 0)
    else if i = 2 then (some (some 0), 1)
    else if i = 3 then (some (some 2), 0)
    else if i = 5 then (some (some 0), 0)
    else if i = 8 then (some (some 0), 0)
    else (none, 0))

/-- The nine-work-tape recognizer. -/
def machine : MultiTapeTM 9 (Fin 4) Control where
  q₀ := stInit
  tr q input work :=
    if h : 18 ≤ q.val then
      let k : Fin 6 := ⟨(q.val - 18) / 2, by omega⟩
      if (q.val - 18) % 2 = 0 then
        carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work
      else returnTr (siteLayout k) (stReturn k) (siteZero k) (siteNext k) work
    else if q = stInit then initTr
    else if q = stCount then
      match input with
      | none => rewindTr
      | some _ => consume (stCarry 0)
    else if q = stRewind then
      match input with
      | none => consume stTree
      | some _ => rewindTr
    else if q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
        q = stPayloadBit ∨ q = stDone ∨ q = stDead then
      match input with
      | none => finish (q == stDone)
      | some s => consumeAct (scanTr q (s == 1) work).1 (scanTr q (s == 1) work).2
    else act (phaseTr q work).1 (phaseTr q work).2

/-- Every work head lies in the interval from minus one to the chosen width. The length
pair's carry may step one cell past its most significant digit, at cell minus one. -/
def HeadBound {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input) :
    Prop := ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ (width : ℤ)

/-- A carry state resolves to the generic carry transition of its site. -/
theorem tr_carry (k : Fin 6) (input : Option (Fin 4)) (work : Fin 9 → Option (Fin 4)) :
    machine.tr (stCarry k) input work =
      carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- A return state resolves to the generic return transition of its site. -/
theorem tr_return (k : Fin 6) (input : Option (Fin 4)) (work : Fin 9 → Option (Fin 4)) :
    machine.tr (stReturn k) input work =
      returnTr (siteLayout k) (stReturn k) (siteZero k) (siteNext k) work := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- The initialization state writes the tags and markers. -/
theorem tr_init (input : Option (Fin 4)) (work : Fin 9 → Option (Fin 4)) :
    machine.tr stInit input work = initTr := rfl

/-- The counting state consumes a bit into the first pending increment. -/
theorem tr_count_some (s : Fin 4) (work : Fin 9 → Option (Fin 4)) :
    machine.tr stCount (some s) work = consume (stCarry 0) := rfl

/-- At the right end, the counting state starts the rewind. -/
theorem tr_count_none (work : Fin 9 → Option (Fin 4)) :
    machine.tr stCount none work = rewindTr := rfl

/-- The rewind moves left over every input symbol. -/
theorem tr_rewind_some (s : Fin 4) (work : Fin 9 → Option (Fin 4)) :
    machine.tr stRewind (some s) work = rewindTr := rfl

/-- At the left end, the rewind steps onto the first bit and starts the scan. -/
theorem tr_rewind_none (work : Fin 9 → Option (Fin 4)) :
    machine.tr stRewind none work = consume stTree := rfl

/-- Reading states resolve to the scan transition table. -/
theorem tr_scan (q : Control) (hq : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨
    q = stLengthBit ∨ q = stPayloadBit ∨ q = stDone ∨ q = stDead)
    (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    machine.tr q (some (boolEmb b)) work =
      consumeAct (scanTr q b work).1 (scanTr q b work).2 := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> rfl

/-- Reading states halt at the right end, emitting the accepting test. -/
theorem tr_end (q : Control) (hq : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨
    q = stLengthBit ∨ q = stPayloadBit ∨ q = stDone ∨ q = stDead)
    (work : Fin 9 → Option (Fin 4)) :
    machine.tr q none work = finish (q == stDone) := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Stationary states resolve to the phase transition table. -/
theorem tr_phase (q : Control) (hq : q = stSizeSetup ∨ q = stSizeInit ∨ q = stLengthEnd ∨
    q = stTagLsb ∨ q = stEraseSize ∨ q = stReturnSize ∨ q = stReturnF ∨ q = stEraseLength)
    (input : Option (Fin 4)) (work : Fin 9 → Option (Fin 4)) :
    machine.tr q input work = act (phaseTr q work).1 (phaseTr q work).2 := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Geb.BitTree.EliasBinary
