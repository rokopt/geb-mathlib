/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Repeat -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Repeat -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Read -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Read -- shake: keep
public import Geb.Prototypes.Computability.SizeBounded.Machine.Exec -- shake: keep
public meta import Geb.Prototypes.Computability.SizeBounded.Machine.Exec -- shake: keep

set_option doc.verso true in
/-!
# Checks for the Logs machine primitives

Run the stored-word reader from nonempty scratch tapes, checking both in-range
and out-of-range indices, register preservation, head positions, and unchanged
output. Check the physical length reader on empty and nonempty input. Run the
word-square transducer on every Boolean word of length at most four.

## Main definitions

* {lit}`checkStored` checks a stored-word query from a reused workspace.
* {lit}`checkStoredLength` counts a stored word from a reused workspace.
* {lit}`checkLength` checks input counting from the home position.
* {lit}`checkInputAt` checks physical-input lookup in the same list order.
* {lit}`checkSquare` compares the concrete transducer with the interpretation.
* {lit}`checkSquareLength` counts a generated quadratic word without emitting it.
* {lit}`checkEmitNumber` checks shortlex encoding from a binary counter.

## Implementation notes

The executable simulator calls CSLib's configuration operations, inheriting their
{lit}`Classical.choice` dependency. This module is included in
{lit}`GebMeta.classicalAllowedModules`.

## Tags

Turing machine, word reader, executable checks, logarithmic space
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine.Tests

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Materialize a logical register in the tape convention used by the machine library. -/
@[expose] def register (w : List Bool) : Std.HashMap ℤ Bool :=
  w.reverse.zipIdx.foldl (fun tape (b, i) ↦ tape.insert (i : ℤ) b) ∅

/-- Check a stored-word query with dirty scratch registers and a protected sixth tape. -/
@[expose] def checkStored (w : List Bool) (q : ℕ) : Bool := Id.run do
  let r : Fin 5 → Fin 6 := Fin.castLE (by decide)
  let tm := readStored r
  let words : Vector (List Bool) 6 :=
    #v[w, counterWord q, [true, false, true], [false, true], [true, true], [false, false]]
  let start : ExecCfg 6 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 (max w.length q.size)
  let finish := (execStep tm)^[readStoredTime B q] start
  let expected := words.set 2 [] |>.set 3 [] |>.set 4 (w[q]?).toList
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 6).all (fun i ↦
      (List.range (B + 3)).all fun j ↦
        finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?)

/-- Check stored length with dirty scratch tapes and a protected caller register. -/
@[expose] def checkStoredLength (w : List Bool) : Bool := Id.run do
  let r : Fin 4 → Fin 5 := Fin.castLE (by decide)
  let tm := storedLength r
  let words : Vector (List Bool) 5 :=
    #v[w, [false, true, false], [true, false], [true, true], [false, true]]
  let start : ExecCfg 5 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 w.length
  let finish := (execStep tm)^[storedLengthTime B] start
  let expected := words.set 1 [] |>.set 2 (counterWord w.length) |>.set 3 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 5).all (fun i ↦
      (List.range (B + 3)).all fun j ↦
        finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?)

/-- Check input length and preservation of an unrelated work tape. -/
@[expose] def checkLength (w : List Bool) : Bool := Id.run do
  let tm := inputLength (0 : Fin 2)
  let start : ExecCfg 2 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := #v[register [false, true, false], register [true, false]]
      outputRev := [false, true] }
  let B := max 3 w.length.size
  let finish := (execStep tm)^[1 + countInputTime B w.length] start
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.range (B + 3)).all (fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? == (register (counterWord w.length))[(j : ℤ) - 1]? &&
      finish.tapes[1][(j : ℤ) - 1]? == start.tapes[1][(j : ℤ) - 1]?)

/-- Check physical-input lookup with the same index convention as stored lookup. -/
@[expose] def checkInputAt (w : List Bool) (q : ℕ) : Bool := Id.run do
  let tm := inputAt (0 : Fin 4) 1 2
  let words : Vector (List Bool) 4 :=
    #v[counterWord q, [false, true, false], [true, true], [false, true]]
  let start : ExecCfg 4 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := words.map register
      outputRev := [false, true] }
  let B := max 3 q.size
  let finish := (execStep tm)^[inputAtTime B q w.length] start
  let expected := words.set 1 [] |>.set 2 (w[q]?).toList
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 4).all (fun i ↦
      (List.range (B + 3)).all fun j ↦
        finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?)

/-- Check the transducer's output within the theorem's polynomial time bound. -/
@[expose] def checkSquare (w : List Bool) : Bool :=
  stepUntilHalt squareMachine (32 * (w.length + 1) ^ 2 + 1)
    (ExecCfg.init squareMachine w) [] == some (squareWord.eval ![w] Fin.elim0)

/-- Check the generic output counter on quadratic output, including a nonzero
initial counter and a preexisting output prefix. -/
@[expose] def checkSquareLength (w : List Bool) (n : ℕ) : Bool := Id.run do
  let tm := countOutput squareMachine
  let start : ExecCfg 2 (StateOf tm) w :=
    { ExecCfg.init tm w with
      tapes := #v[register (counterWord n), ∅]
      outputRev := [true, false] }
  let B := max w.length.size (n + w.length * w.length + 1).size
  let T := countInputTime w.length.size w.length +
    (w.length * (2 * w.length + 2 * w.length.size + 11) + 1)
  let finish := (execStep tm)^[T * (2 * B + 5)] start
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.range (B + 3)).all fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? ==
        (register (counterWord (n + w.length * w.length)))[(j : ℤ) - 1]? &&
      finish.tapes[1][(j : ℤ) - 1]? == none

/-- Check numerical emission while an unrelated tape has a nonzero head position. -/
@[expose] def checkEmitNumber (n : ℕ) : Bool := Id.run do
  let tm := emitNumber (0 : Fin 2)
  let start : ExecCfg 2 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      tapes := #v[register (counterWord n), register [true, false, true]]
      heads := #v[0, 2]
      outputRev := [true, false] }
  let B := max 3 (n + 1).size
  let finish := (execStep tm)^[3 * B + 5] start
  return finish.state.isNone && finish.inputPos.val == 1 &&
    finish.heads[0] == (n + 1).size && finish.heads[1] == 2 &&
    finish.outputRev.reverse == [false, true] ++ unrank n &&
    (List.range (B + 3)).all fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? == (register (counterWord (n + 1)))[(j : ℤ) - 1]? &&
      finish.tapes[1][(j : ℤ) - 1]? == start.tapes[1][(j : ℤ) - 1]?

#guard (List.range 65).all checkEmitNumber

#guard (List.range 5).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  checkLength w && checkStoredLength w && checkSquare w &&
    ([0, 1, 3] : List ℕ).all (checkSquareLength w) &&
    (let tm := lengthMachine squareMachine
     stepUntilHalt tm (256 * (w.length + 1) ^ 3 + 1) (ExecCfg.init tm w) [] ==
       some ((Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![w] Fin.elim0)) &&
    (List.range 8).all (fun q ↦ checkStored w q && checkInputAt w q)

#guard ([[], [false], [false, true, false]] : List (List Bool)).all fun w ↦
  (List.range 5).all fun q ↦
    let tm := repeatInput (0 : Fin 1)
    let start : ExecCfg 1 (StateOf tm) w :=
      { ExecCfg.init tm w with
        inputPos := 0
        tapes := #v[register (counterWord q)]
        outputRev := [false, true] }
    let finish := (execStep tm)^[q * (2 * w.length + 2 * q.size + 11) + 1] start
    finish.state.isNone && finish.outputRev.reverse ==
      [true, false] ++ (List.replicate q w).flatten

#guard (List.range 8).all fun n ↦
  let P : MultiTapeTM 0 Bool Unit :=
    { q₀ := ()
      tr := fun _ _ _ ↦
        { inputTape := 0, workTapes := Fin.elim0, output := some false, state := none } }
  let tm := countOutput P
  let start : ExecCfg 1 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      tapes := #v[register (counterWord n)]
      outputRev := [false, true] }
  let finish := (execStep tm)^[30] start
  finish.state.isNone && finish.inputPos.val == 1 && finish.heads[0] == 0 &&
    finish.outputRev == start.outputRev &&
    (List.range 7).all fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? == (register (counterWord (n + 1)))[(j : ℤ) - 1]?

#guard ([0, 1, 3, 7] : List ℕ).all fun n ↦
  let P : MultiTapeTM 1 Bool Bool :=
    { q₀ := false
      tr := fun q _ _ ↦
        if q then
          { inputTape := 0, workTapes := fun _ ↦ (some (some true), -1),
            output := some false, state := none }
        else
          { inputTape := 0, workTapes := fun _ ↦ (some (some false), 1),
            output := some true, state := some true } }
  let tm := countOutput P
  let start : ExecCfg 2 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      tapes := #v[register (counterWord n), register [false, false, true]]
      outputRev := [false, true] }
  let finish := (execStep tm)^[26] start
  finish.state.isNone && finish.inputPos.val == 1 && finish.heads.toList.all (· == 0) &&
    finish.outputRev == start.outputRev &&
    (List.range 7).all fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? == (register (counterWord (n + 2)))[(j : ℤ) - 1]? &&
      finish.tapes[1][(j : ℤ) - 1]? == (register [false, true, false])[(j : ℤ) - 1]?

end

end Geb.Oitavem.Machine.Tests
