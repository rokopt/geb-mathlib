/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Prototypes.Computability.TreeScanner.Machine
public import Geb.Prototypes.Computability.BitTreeScanner.Scan

set_option doc.verso true

/-!
# A one-pass tree scanner

A deterministic multi-tape Turing machine deciding {name}`Geb.BitTreeScanner.validBool`
in a single left-to-right pass. The machine is {name}`Geb.BitTreeScanner.scanStep`
with the pending count kept as the work head's position: a pair bit moves the
head right, a leaf's closing bit moves it left, and a marker at cell {lit}`0`,
written at the first step, marks the count a closing bit lowers as the last,
at which the scan completes rather than expecting a further tree.

The first step is its own state: it writes the marker the closing steps read,
and no later step may, since a later step at cell {lit}`0` cannot tell that
cell from a blank cell to its right. Every other state is a mode of the scan.

## Main definitions

* {lit}`Geb.BitTreeScanner.stFirst`, {lit}`Geb.BitTreeScanner.stMain`,
  {lit}`Geb.BitTreeScanner.stLeafOpen`, {lit}`Geb.BitTreeScanner.stLeafBit`,
  {lit}`Geb.BitTreeScanner.stDone`, {lit}`Geb.BitTreeScanner.stDead` — the
  six states.
* {lit}`Geb.BitTreeScanner.advance`, {lit}`Geb.BitTreeScanner.halt` — the two
  shapes of transition: read a bit and continue, or read the end and emit.
* {lit}`Geb.BitTreeScanner.bitTreeScanner` — the machine.
* {lit}`Geb.BitTreeScanner.stateOf` — the state a mode is run in.
* {lit}`Geb.BitTreeScanner.cfgOf` — the closed-form configuration after
  reading a prefix.

## Main statements

* {lit}`Geb.BitTreeScanner.cfgOf_state`,
  {lit}`Geb.BitTreeScanner.cfgOf_inputPos_val`,
  {lit}`Geb.BitTreeScanner.cfgOf_workTapes`,
  {lit}`Geb.BitTreeScanner.cfgOf_workTapePos` — the field projections of the
  closed form.
* {lit}`Geb.BitTreeScanner.cfgOf_workTapeSymbols_eq` — the closed form's
  work-symbol function, in the unapplied form the transition consumes.
* {lit}`Geb.BitTreeScanner.cfgOf_zero` — the closed form at the empty prefix
  is the initial configuration.

## Implementation notes

The input alphabet's embedding is {name}`Geb.TreeScanner.boolEmb`, shared
with the ranked-term scanner. {lit}`cfgOf` is indexed by the prefix's length
and reads the scan's state off {name}`Geb.BitTreeScanner.scanFinal` at that prefix,
so no proof over it inducts on the input.

The work tape holds the marker at cell {lit}`0` from the first step on, which
{lit}`cfgOf` states as a condition on the prefix's length; the condition is
placed first in the conjunction so that at a literal length the cell's
content reduces without a decision on the cell index.

## Tags

Turing machine, tree, prefix code, linear time, one pass
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner
open Geb.TreeScanner (boolEmb)

/-- The state of the first step, which writes the marker. -/
def stFirst : Fin 6 := ⟨0, by omega⟩

/-- The state expecting a tree. -/
def stMain : Fin 6 := ⟨1, by omega⟩

/-- The state inside a leaf expecting a payload bit's prefix or the closing bit. -/
def stLeafOpen : Fin 6 := ⟨2, by omega⟩

/-- The state inside a leaf expecting a payload bit. -/
def stLeafBit : Fin 6 := ⟨3, by omega⟩

/-- The state after the one expected tree completes. -/
def stDone : Fin 6 := ⟨4, by omega⟩

/-- The state of a failed scan. -/
def stDead : Fin 6 := ⟨5, by omega⟩

/-- The transition that reads a bit: the input head advances, the one work
tape takes the given write and move, nothing is emitted. -/
def advance (q : Fin 6) (a : Option (Option (Fin 2)) × SignType) :
    TransitionOut 1 (Fin 2) (Fin 6) :=
  { inputMove := 1, workActions := fun _ ↦ a, outS := none, q' := some q }

/-- The transition that reads the end: nothing moves, the given bit is
emitted, the machine halts. -/
def halt (b : Fin 2) : TransitionOut 1 (Fin 2) (Fin 6) :=
  { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := some b, q' := none }

/-- The machine. One work tape; the pending count is the work head's position,
and cell {lit}`0` holds a marker from the first step on. -/
def bitTreeScanner : MultiTapeTM 1 (Fin 2) (Fin 6) where
  q₀ := stFirst
  tr q inSym work :=
    if q = stFirst then
      match inSym with
      | some 1 => advance stMain (some (some 0), 1)
      | some _ => advance stLeafOpen (some (some 0), 0)
      | none => halt 0
    else if q = stMain then
      match inSym with
      | some 1 => advance stMain (none, 1)
      | some _ => advance stLeafOpen (none, 0)
      | none => halt 0
    else if q = stLeafOpen then
      match inSym with
      | some 1 => advance stLeafBit (none, 0)
      | some _ =>
        match work 0 with
        | some _ => advance stDone (none, 0)
        | none => advance stMain (none, -1)
      | none => halt 0
    else if q = stLeafBit then
      match inSym with
      | some _ => advance stLeafOpen (none, 0)
      | none => halt 0
    else if q = stDone then
      match inSym with
      | some _ => advance stDead (none, 0)
      | none => halt 1
    else
      match inSym with
      | some _ => advance stDead (none, 0)
      | none => halt 0

/-- The state a mode is run in after a prefix of the given length: the
expecting mode is the first-step state at the empty prefix and the main state
after it. -/
def stateOf (k : ℕ) : Mode → Fin 6
  | .term => if k = 0 then stFirst else stMain
  | .leafOpen => stLeafOpen
  | .leafBit => stLeafBit
  | .done => stDone
  | .dead => stDead

/-- The configuration after reading the prefix of length {lit}`k`: the state
of the scan's mode at that prefix, the input head past the prefix, the marker
at cell {lit}`0` once any step has run, and the work head at the scan's
pending count. -/
def cfgOf (w : List Bool) (k : ℕ) (hk : k ≤ w.length) :
    Cfg 1 (Fin 2) (Fin 6) (w.map boolEmb) where
  state := some (stateOf k (scanFinal (w.take k)).mode)
  inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩
  workTapes _ z := if k ≠ 0 ∧ z = 0 then some 0 else none
  workTapePos _ := ((scanFinal (w.take k)).count : ℤ)

section CfgProjections

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length)

/-- {name}`cfgOf`'s state is the state of the scan's mode at the prefix. -/
@[simp] theorem cfgOf_state :
    (cfgOf w k hk).state = some (stateOf k (scanFinal (w.take k)).mode) := rfl

/-- {name}`cfgOf`'s input head is past the prefix. -/
@[simp] theorem cfgOf_inputPos_val : (cfgOf w k hk).inputPos.val = k + 1 := rfl

/-- {name}`cfgOf`'s work tape holds the marker at cell {lit}`0` once any step
has run, and is blank elsewhere. Not {lit}`@[simp]`: a step lemma cites this
rather than letting {lit}`simp` unfold {name}`cfgOf` in place. -/
theorem cfgOf_workTapes (i : Fin 1) (z : ℤ) :
    (cfgOf w k hk).workTapes i z = if k ≠ 0 ∧ z = 0 then some 0 else none := rfl

/-- {name}`cfgOf`'s work head is at the scan's pending count. -/
@[simp] theorem cfgOf_workTapePos (i : Fin 1) :
    (cfgOf w k hk).workTapePos i = ((scanFinal (w.take k)).count : ℤ) := rfl

/-- The work-symbol function at {name}`cfgOf`, in the unapplied form the
transition consumes: the marker exactly when a step has run and nothing is
pending. -/
theorem cfgOf_workTapeSymbols_eq :
    (cfgOf w k hk).workTapeSymbols =
      fun _ ↦ if k ≠ 0 ∧ (scanFinal (w.take k)).count = 0 then some 0 else none := by
  funext i
  unfold Cfg.workTapeSymbols
  rw [cfgOf_workTapes, cfgOf_workTapePos]
  simp only [Nat.cast_eq_zero]

end CfgProjections

/-- {name}`cfgOf` at the empty prefix is {name}`bitTreeScanner`'s initial
configuration. -/
theorem cfgOf_zero (w : List Bool) :
    cfgOf w 0 (Nat.zero_le _) = bitTreeScanner.initCfg (w.map boolEmb) := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i z
  rw [cfgOf_workTapes]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false]
  rfl

end Geb.BitTreeScanner
