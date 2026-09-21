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
public import Geb.Prototypes.Computability.Oitavem.Machine.RecursiveLength -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.RecursiveLength -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Compose -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Compose -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Segment -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Segment -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Subtraction -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Subtraction -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Realizer -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Initial -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Initial -- shake: keep
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Recursion -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Recursion -- shake: keep
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
* {lit}`checkSquareDigit` queries that word while preserving a caller register.
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

/-- A composed generator that imports one stored word into two argument slots. -/
@[expose] def duplicateProduct :=
  let Pre := fun (_ : List Bool) (σ : Fin 2 → List Bool) ↦ (σ 1).length ≤ 4
  let G := (Generator.stored 2 Pre 0).numericSucc
  let H := Generator.stored 2 Pre 1
  let P := G.product H (fun _ ↦ 4) 3 (fun _ _ h ↦ h)
    (fun n ↦ by change 3 ≤ 3 * (n.size + 1); omega)
  (P.rename (fun _ : Fin 2 ↦ (0 : Fin 1))
    (Pre' := fun _ σ ↦ (σ 0).length ≤ 4) (fun _ _ h ↦ h)).numericPred

/-- Nested generators restore their private workspaces and the aliased source word. -/
@[expose] def checkEnvironment (w : List Bool) : Bool := Id.run do
  let G := duplicateProduct
  let start : ExecCfg G.tapes G.State [] :=
    { ExecCfg.init G.program [] with
      inputPos := 0
      tapes := Vector.ofFn fun i ↦ if i.val = 0 then register w else ∅
      outputRev := [true, false] }
  let finish := (execStep G.program)^[10000] start
  let expected := numericPred (List.replicate w.length (numericSucc w)).flatten
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) &&
    finish.outputRev.reverse == [false, true] ++ expected &&
    (List.finRange G.tapes).all (fun i ↦ (List.range 12).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == start.tapes[i][(j : ℤ) - 1]?)

#guard (List.range 31).all fun n ↦ checkEnvironment (unrank n)

/-- Generated readers keep the source and query while replacing a dirty result. -/
@[expose] def checkEnvironmentReader (w : List Bool) (q : ℕ) : Bool := Id.run do
  let G := duplicateProduct
  let L := G.lengthReader (fun _ ↦ (0 : Fin 4)) 2
  let P := G.atReader (fun _ ↦ (0 : Fin 4)) 1 2
  let words := #v[w, counterWord q, [true, false, true], [false, false]]
  let source := numericPred (List.replicate w.length (numericSucc w)).flatten
  let start : ExecCfg _ (StateOf P) [] :=
    { ExecCfg.init P [] with
      inputPos := 0
      tapes := Vector.ofFn fun i ↦ if h : i.val < 4 then register words[i.val] else ∅
      outputRev := [true, false] }
  let finish := (execStep P)^[50000] start
  let lengthStart : ExecCfg _ (StateOf L) [] :=
    { ExecCfg.init L [] with
      inputPos := 0
      tapes := Vector.ofFn fun i ↦ if h : i.val < 4 then register words[i.val] else ∅
      outputRev := [true, false] }
  let lengthFinish := (execStep L)^[50000] lengthStart
  let expected := words.set 2 (source[q]?).toList
  let expectedLength := words.set 2 (counterWord source.length)
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    lengthFinish.state.isNone && lengthFinish.inputPos.val == 0 &&
    lengthFinish.heads.toList.all (· == 0) && lengthFinish.outputRev == lengthStart.outputRev &&
    (List.finRange finish.tapes.size).all (fun i ↦ (List.range 12).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? ==
        (if h : i.val < 4 then (register expected[i.val])[(j : ℤ) - 1]? else none)) &&
    (List.finRange lengthFinish.tapes.size).all (fun i ↦ (List.range 12).all fun j ↦
      lengthFinish.tapes[i][(j : ℤ) - 1]? ==
        (if h : i.val < 4 then (register expectedLength[i.val])[(j : ℤ) - 1]? else none))

#guard ([[], [false], [true, false]] : List (List Bool)).all fun w ↦
  ([0, 1, 4, 9] : List ℕ).all (checkEnvironmentReader w)

/-- Execute a packaged generator and check its output, restoration, and parked heads. -/
@[expose] def checkGenerator {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
    {W : List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W) (input : List Bool) (σ : Fin m → List Bool) (fuel : ℕ) : Bool :=
  Id.run do
    let start : ExecCfg G.tapes G.State input :=
      { ExecCfg.init G.program input with
        inputPos := 0
        tapes := Vector.ofFn fun i ↦ register
          (((List.finRange m).find? (fun j ↦ G.env j == i)).map σ |>.getD [])
        outputRev := [true, false] }
    let mut finish := start
    for _ in [:fuel] do
      if finish.state.isNone then break
      finish := execStep G.program finish
    return finish.state.isNone && finish.inputPos.val == 0 &&
      finish.heads.toList.all (· == 0) &&
      finish.outputRev.reverse == [false, true] ++ W input σ &&
      (List.finRange G.tapes).all (fun i ↦ (List.range 12).all fun j ↦
        finish.tapes[i][(j : ℤ) - 1]? == start.tapes[i][(j : ℤ) - 1]?)

#guard (List.range 7).all fun a ↦ (List.range 7).all fun b ↦
  let Pre := fun (_ : List Bool) (σ : Fin 2 → List Bool) ↦ ∀ i, (σ i).length ≤ 4
  let G := Generator.stored 2 Pre 0
  let H := Generator.stored 2 Pre 1
  let S := G.numericSub H (fun _ ↦ 5) 3
    (fun _ σ hp ↦ by have := hp 0; have := hp 1; omega)
    (fun n ↦ by change 3 ≤ 3 * (n.size + 1); omega)
  let D := G.iterPred H (fun _ ↦ 4) 3
    (fun _ _ hp ↦ max_le (hp 0) (hp 1))
    (fun n ↦ by change 3 ≤ 3 * (n.size + 1); omega)
  let C := G.cond (fun b ↦ Generator.stored 2 Pre (if b then 1 else 0)) 3
    (fun input σ hp ↦ (size_le_size (Nat.add_le_add_right (hp 0) 1)).trans
      (by change 3 ≤ 3 * (input.length.size + 1); omega))
  checkGenerator S [] ![unrank a, unrank b] 100000 &&
    checkGenerator D [] ![unrank a, unrank b] 100000 &&
    checkGenerator C [] ![unrank a, unrank b] 100000

#guard ([[], [false], [true, false, true]] : List (List Bool)).all fun w ↦
  ([0, 1, 3] : List ℕ).all fun k ↦
    let Pre := fun (_ : List Bool) (σ : Fin 2 → List Bool) ↦ (σ 0).length ≤ 4
    let N := fun (_ : ℕ) ↦ 4
    let hsize := fun n ↦ (show (N n + 1).size ≤ 3 * (n.size + 1) by
      dsimp only [N]
      exact (show (5 : ℕ).size ≤ 3 by decide).trans (by omega))
    let G := Generator.stored 2 Pre 0
    let QPre := QueryPre Pre N
    let Q := (Generator.stored 3 QPre 0).dropCounter 2 N 3
      (fun _ _ hp ↦ hp.2) (fun _ _ hp ↦ hp.1) hsize
    let P : Generator 3 QPre (fun _ σ ↦ [(σ 0)[counterValue (σ 2)]?.getD false]) :=
      Q.last.congr (by intro input σ _; simp only [List.headD_eq_head?_getD, List.head?_drop])
    let I := G.indexed (F := fun _ σ j ↦ (σ 0)[j]?.getD false) P (fun _ σ ↦ σ 0) 3
      (fun _ _ hp ↦ hp) hsize (fun _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl)
    let LP := (Generator.stored 3 (LengthPre Pre (fun _ σ ↦ σ 0)) 2).congr
      (V := fun _ σ ↦ counterWord (σ 0).length) (fun _ _ hp ↦ hp.2)
    let L := G.withLength (V := fun _ σ ↦ counterWord (σ 0).length) LP 3
      (fun input σ hp ↦ (size_le_size (Nat.add_le_add_right hp 1)).trans (hsize input.length))
    let RP := (Generator.stored 4 (RetainedPre Pre 1 N) 2).succ false
    let Value := fun (_ : List Bool) (σ : Fin 2 → List Bool) ↦
      Nat.rec ((σ 0).take (σ 1).length) (fun _ r ↦ (false :: r).take (σ 1).length)
    let R := G.retained (H := fun _ _ v _ ↦ false :: v) G 1 RP Value
      (fun input σ ↦ false :: Value input σ (σ 0).length) 3 (fun _ _ hp ↦ hp) hsize
      (fun _ _ _ ↦ rfl) (by intro input σ _ j _; cases j <;> exact List.length_take_le ..)
      (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    checkGenerator I [] ![w, List.replicate k true] 100000 &&
      checkGenerator L [] ![w, List.replicate k true] 100000 &&
      checkGenerator R [] ![w, List.replicate k true] 100000

#guard (List.range 31).all fun n ↦
  let w := unrank n
  let G := Generator.input
  let start : ExecCfg G.tapes G.State w :=
    { ExecCfg.init G.program w with inputPos := 0, outputRev := [true, false] }
  let finish := (execStep G.program)^[10000] start
  finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ w &&
    (List.finRange G.tapes).all (fun i ↦
      (List.range 8).all fun j ↦ finish.tapes[i][(j : ℤ) - 1]?.isNone)

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

/-- Query a generated quadratic word with dirty generator scratch and a protected
caller register. The result tape is blank as the reader's contract requires. -/
@[expose] def checkSquareDigit (w : List Bool) (q : ℕ) : Bool := Id.run do
  let tm := readOutput (squareInput (0 : Fin 2))
  let start : ExecCfg 4 (StateOf tm) w :=
    { ExecCfg.init tm w with
      tapes := #v[register (counterWord q), ∅,
        register [false, true, false], register [true, false]]
      outputRev := [false, true] }
  let B := max 3 (max w.length.size q.size)
  let T := countInputTime B w.length + w.length * (2 * w.length + 2 * B + 11) + 1
  let finish := (execStep tm)^[T * (2 * B + 8)] start
  let expected : Vector (List Bool) 4 :=
    #v[counterWord (q - w.length * w.length),
      ((squareWord.eval ![w] Fin.elim0)[q]?).toList, [], [true, false]]
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 4).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Repeatedly reconstruct a generated square through digit queries from dirty ports,
checking scratch cleanup, the returned length, and a protected caller register. -/
@[expose] def checkSquareViaReader (w : List Bool) : Bool := Id.run do
  let p := squareViaReaderFromHome (0 : Fin 3) 1
  let tm := seq p p
  let B := 2 * w.length.size + 1
  let dirty := [false, true, false].take B
  let words : Vector (List Bool) 5 := #v[dirty, dirty, dirty, dirty, [false]]
  let start : ExecCfg 5 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let finish := (execStep tm)^[2 * squareViaReaderTime B w.length] start
  let expected := #v[[], [], [], counterWord (w.length * w.length), [false]]
  let out := squareWord.eval ![w] Fin.elim0
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ out ++ out &&
    (List.finRange 5).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Move a generated reader's scratch past the caller's tape. The protected head
starts away from zero and remains there during the allocated streaming program. -/
@[expose] def checkAllocatedReader (w : List Bool) : Bool := Id.run do
  let e : Fin 5 ≃ Fin 4 ⊕ Fin 1 :=
    (Equiv.swap 0 4).trans (finSumFinEquiv (m := 4) (n := 1)).symm
  let tm := onTapes (squareViaReaderFromHome (0 : Fin 2) 1) e
  let B := 2 * w.length.size + 1
  let dirty := [true, false, true].take B
  let words : Vector (List Bool) 5 := #v[[false], dirty, dirty, dirty, dirty]
  let start : ExecCfg 5 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := words.map register
      heads := #v[1, 0, 0, 0, 0]
      outputRev := [false] }
  let finish := (execStep tm)^[squareViaReaderTime B w.length] start
  let expected := #v[[false], [], [], counterWord (w.length * w.length), []]
  return finish.state.isNone && finish.inputPos.val == 0 && finish.heads == start.heads &&
    finish.outputRev.reverse == [false] ++ squareWord.eval ![w] Fin.elim0 &&
    (List.finRange 5).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

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

/-- Repeat a generated length call with dirty scratch and an unrelated caller tape. -/
@[expose] def checkGeneratedLength (w : List Bool) : Bool := Id.run do
  let p := generatedLength (squareFromHome (0 : Fin 2))
  let tm := seq p p
  let words : Vector (List Bool) 3 :=
    #v[[true, false, true], [false, true], [true, false]]
  let start : ExecCfg 3 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 (2 * w.length.size + 1)
  let T := (4 * B + 9) + squareFromHomeTime B w.length * (2 * B + 5)
  let finish := (execStep tm)^[2 * T] start
  let expected := words.set 0 (counterWord (w.length * w.length)) |>.set 1 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 3).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Repeat a generated digit call, preserving the saved query and a caller tape.
The second call must clear the result left by the first. -/
@[expose] def checkGeneratedAt (w : List Bool) (q : ℕ) : Bool := Id.run do
  let p := generatedAt (squareFromHome (1 : Fin 3)) 0
  let tm := seq p p
  let words : Vector (List Bool) 5 :=
    #v[[true, false], [true, true, true], counterWord q, [false, true], [true, false]]
  let start : ExecCfg 5 (StateOf tm) w :=
    { ExecCfg.init tm w with
      inputPos := 0
      tapes := words.map register
      outputRev := [false, true] }
  let B := max 3 (max w.length.size q.size)
  let T := squareFromHomeTime B w.length * (2 * B + 8) + 13 * B + 30
  let finish := (execStep tm)^[2 * T] start
  let expected := words.set 0 [] |>.set 1 ((squareWord.eval ![w] Fin.elim0)[q]?).toList
    |>.set 3 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 5).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Check the quartic-output composition against the Logs interpreter. -/
@[expose] def checkSquareSquare (w : List Bool) : Bool :=
  stepUntilHalt squareSquareMachine (squareSquareTime w.length + 2)
    (ExecCfg.init squareSquareMachine w) [] ==
      some ((Expr.comp (safe := false) squareWord ![squareWord]).eval ![w] Fin.elim0)

#guard (List.range 65).all checkEmitNumber

/-- Check a stored-word generator, including protected data and the existing output prefix. -/
@[expose] def checkStoredGenerator {S : Type} (tm : MultiTapeTM 2 Bool S)
    (w expected : List Bool) : Bool := Id.run do
  let start : ExecCfg 2 S [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := #v[register w, register [false, true, false]]
      outputRev := [true, false] }
  let finish := (execStep tm)^[2 * max 3 w.length + 6] start
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ expected &&
    (List.finRange 2).all fun i ↦ (List.range (w.length + 5)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == start.tapes[i][(j : ℤ) - 1]?

/-- Replace a saved word by a captured successor prefix, starting with dirty capture scratch. -/
@[expose] def checkCapturedSuccessor (w : List Bool) (K : ℕ) : Bool := Id.run do
  let tm := generatedPrefix (numericSuccGenerator (emitStored (0 : Fin 2))) 0
  let mask := (List.range K).map (fun n ↦ n % 2 == 0)
  let words := #v[mask, [true, false, true], w, [false, true]]
  let start : ExecCfg 4 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 (max K w.length)
  let finish := (execStep tm)^[17 * B + 39] start
  let expected := words.set 1 [] |>.set 2 ((numericSucc w).take K)
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 4).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Execute the saved-prefix recursion, checking its result and complete scratch cleanup. -/
@[expose] def checkRecursiveLength (w : List Bool) : Bool := Id.run do
  let start := { ExecCfg.init squareRecLengthMachine w with outputRev := [true, false] }
  let finish := (execStep squareRecLengthMachine)^[squareRecLengthTime w.length + 1] start
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse ==
      [false, true] ++ (Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![w] Fin.elim0 &&
    finish.tapes.toList.all (fun tape ↦ tape.isEmpty)

/-- Query a suffix through a translated index, retaining the offset and caller registers. -/
@[expose] def checkSegment (w : List Bool) (d q : ℕ) : Bool := Id.run do
  let source : Fin 5 → Fin 9 := ![5, 2, 6, 7, 4]
  let ports : Fin 5 → Fin 9 := ![0, 1, 2, 3, 4]
  let tm := dropReader (readStored source) ports
  let words := #v[counterWord d, counterWord q, [], [], [true, true], w, [], [], [false, true]]
  let start : ExecCfg 9 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 w.length
  let T := (5 * B + 12) + (5 * B + 12) + (w.length * (4 * B + 11) + 1) +
    (readStoredTime B B + (4 * B + 9))
  let finish := (execStep tm)^[T] start
  let expected := words.set 4 ((w.drop d)[q]?).toList
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev == start.outputRev &&
    (List.finRange 9).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Stream a suffix with an arbitrary offset, including offsets beyond the source. -/
@[expose] def checkDrop (w : List Bool) (d : ℕ) : Bool := Id.run do
  let source : Fin 5 → Fin 10 := ![5, 2, 6, 7, 4]
  let ports : Fin 5 → Fin 10 := ![0, 1, 2, 3, 4]
  let tm := dropGenerator (readStored source) ports 8
  let words := #v[counterWord d, [true], [], [false, true], [true, true], w, [], [],
    counterWord w.length, [false, true]]
  let start : ExecCfg 10 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 (max w.length d.size)
  let T := dropGeneratorTime (fun _ ↦ readStoredTime B B) (fun _ ↦ B)
    (fun _ ↦ max d w.length) 0
  let finish := (execStep tm)^[T] start
  let expected := words.set 0 [] |>.set 1 [] |>.set 3 [] |>.set 4 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ w.drop d &&
    (List.finRange 10).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Check a constructor with a dirty extra counter and three preserved argument registers. -/
@[expose] def checkConstructor {S : Type} (tm : MultiTapeTM 4 Bool S)
    (w expected : List Bool) : Bool := Id.run do
  let words := #v[[true, false], w, [false, true], [true]]
  let start : ExecCfg 4 S [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let finish := (execStep tm)^[100 * (w.length + 3)] start
  let finalWords := words.set 0 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ expected &&
    (List.finRange 4).all fun i ↦ (List.range (w.length + 5)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register finalWords[i])[(j : ℤ) - 1]?

/-- Emit a counted prefix through repeated queries, preserving the source and caller tapes. -/
@[expose] def checkEmitPrefix (w : List Bool) (K : ℕ) : Bool := Id.run do
  let source : Fin 5 → Fin 7 := ![3, 1, 4, 5, 2]
  let tm := emitPrefix (readStored source) 0 1 2
  let words := #v[counterWord K, [], [], w, [], [], [true, false]]
  let start : ExecCfg 7 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let B := max 3 w.length
  let finish := (execStep tm)^[K * (readStoredTime B B + 8 * B + 21) + 1 + (4 * B + 9)] start
  let expected := words.set 0 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse == [false, true] ++ w.take K &&
    (List.finRange 7).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

/-- Initialize and run subtraction with reused counters, checking normalization and cleanup. -/
@[expose] def checkSubtraction (v w : List Bool) : Bool := Id.run do
  let a : Fin 5 → Fin 12 := ![7, 5, 9, 10, 0]
  let b : Fin 5 → Fin 12 := ![8, 5, 9, 10, 1]
  let lengthV := seq (storedLength (![8, 9, 4, 10] : Fin 4 → Fin 12)) (dec 4)
  let lengthW := seq (storedLength (![7, 9, 5, 10] : Fin 4 → Fin 12)) (dec 5)
  let tm := numericSubGenerator lengthV lengthW (readStored a) (readStored b) (Fin.castAdd 5)
  let N := max v.length w.length + 1
  let B := max 3 N
  let words := #v[[], [], [false, true], [], [true, false, false], [true], [false, true],
    w ++ [true], v ++ [true], [], [], [true, false]]
  let start : ExecCfg 12 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let L := storedLengthTime B + 2 * B + 6
  let T := numericSubTime L L (readStoredTime B N) (readStoredTime B N) B N
  let finish := (execStep tm)^[T] start
  let expected := words.set 2 [] |>.set 4 [] |>.set 5 [] |>.set 6 []
  return finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) &&
    finish.outputRev.reverse == [false, true] ++ numericSub v w &&
    (List.finRange 12).all fun i ↦ (List.range (B + 3)).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

#guard (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
  checkSubtraction (unrank a) (unrank b)

#guard (List.range 4).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  (List.range (n + 3)).all (checkDrop w) && (List.range (n + 1)).all (checkEmitPrefix w) &&
    checkConstructor (lengthGenerator (emitStored 0)) w (unrank w.length) &&
    checkConstructor (productGenerator (emitStored 1) (emitStored 0)) w
      (List.replicate w.length [false, true]).flatten &&
    checkConstructor (condGenerator (emitStored 0)
      (fun b ↦ if b then emitStored 1 else emitStored 2)) w
      (if w.isEmpty then [false, true] else [true])

#guard (List.range 6).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  checkStoredGenerator (numericSuccGenerator (emitStored 0)) w (numericSucc w) &&
    checkStoredGenerator (numericPredGenerator (emitStored 0)) w (numericPred w) &&
    checkStoredGenerator (predGenerator (emitStored 0)) w w.tail &&
    checkStoredGenerator (lastGenerator (emitStored 0)) w [w.headD false] &&
    (List.range 7).all (checkCapturedSuccessor w)

#guard (List.range 4).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  checkRecursiveLength w && (List.range (n + 1)).all fun d ↦
    (List.range (n - d + 1)).all (checkSegment w d)

#guard (List.range 3).all fun K ↦
  let tm := captureOutput (emitSymbol (k := 0) (some false))
  let start : ExecCfg 2 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      tapes := #v[register (List.replicate K true), ∅]
      outputRev := [true, false] }
  let finish := execStep tm start
  finish.state.isNone && finish.outputRev == start.outputRev &&
    finish.heads == #v[(min 1 K : ℤ), (min 1 K : ℤ)] &&
    finish.tapes[1][(0 : ℤ)]? == (if K = 0 then none else some false)

#guard ([false, true] : List Bool).all fun a ↦ ([false, true] : List Bool).all fun b ↦
  ([none, some false, some true] : List (Option Bool)).all fun c ↦
  ([[], [true]] : List (List Bool)).all fun old ↦
    let tm := subBitStep (Fin.castAdd 1 : Fin 4 → Fin 5)
    let words := #v[[a], [b], c.toList, old, [true, false]]
    let start : ExecCfg 5 Unit [] :=
      { ExecCfg.init tm [] with
        inputPos := 0
        tapes := words.map register
        outputRev := [true, false] }
    let finish := execStep tm start
    let d := (a.toNat : ℤ) - b.toNat + carryValue c
    let carry : Option Bool := if d / 2 < 0 then none else some (d / 2 == 1)
    let expected := words.set 2 carry.toList |>.set 3 [d % 2 == 1]
    finish.state.isNone && finish.inputPos.val == 0 &&
      finish.heads == start.heads && finish.outputRev == start.outputRev &&
      (List.finRange 5).all fun i ↦ (List.range 5).all fun j ↦
        finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

#guard (List.range 6).all fun n ↦ ([false, true] : List Bool).all fun b ↦
  let tm := concatRecGenerator (emitSymbol (some b)) (emitStored (2 : Fin 4)) 0 1
  let words := #v[counterWord n, [], [false, true, false], [true, false]]
  let start : ExecCfg 4 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      inputPos := 0
      tapes := words.map register
      outputRev := [true, false] }
  let finish := (execStep tm)^[n * 24 + 45] start
  let expected := words.set 0 []
  finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) && finish.outputRev.reverse ==
      [false, true] ++ List.replicate n b ++ [false, true, false] &&
    (List.finRange 4).all fun i ↦ (List.range 6).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == (register expected[i])[(j : ℤ) - 1]?

#guard (List.range 4).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  checkSquareViaReader w && checkAllocatedReader w &&
    stepUntilHalt squareViaReaderMachine (squareViaReaderTime (2 * n.size + 1) n + 2)
      (ExecCfg.init squareViaReaderMachine w) [] == some (squareWord.eval ![w] Fin.elim0)

#guard ([[], [false], [false, true, false]] : List (List Bool)).all fun w ↦
  let tm := squareInput (1 : Fin 2)
  let start : ExecCfg 2 (StateOf tm) w :=
    { ExecCfg.init tm w with
      tapes := #v[register [false, false], register [true, false, true]]
      outputRev := [true, false] }
  let B := max 3 w.length.size
  let T := countInputTime B w.length + w.length * (2 * w.length + 2 * B + 11) + 1
  let finish := (execStep tm)^[T] start
  finish.state.isNone && finish.inputPos.val == 0 &&
    finish.heads.toList.all (· == 0) &&
    finish.outputRev.reverse == [false, true] ++ (List.replicate w.length w).flatten &&
    (List.range (B + 3)).all fun j ↦
      finish.tapes[0][(j : ℤ) - 1]? == start.tapes[0][(j : ℤ) - 1]? &&
      finish.tapes[1][(j : ℤ) - 1]? == none

#guard (List.range 5).all fun n ↦ (List.range (2 ^ n)).all fun x ↦
  let w := (List.range n).map (Nat.testBit x)
  checkLength w && checkStoredLength w && checkSquare w &&
    checkGeneratedLength w && checkSquareSquare w &&
    ([0, 1, 3] : List ℕ).all (checkSquareLength w) &&
    (let tm := lengthMachine squareMachine
     stepUntilHalt tm (256 * (w.length + 1) ^ 3 + 1) (ExecCfg.init tm w) [] ==
       some ((Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![w] Fin.elim0)) &&
    (List.range 8).all (fun q ↦ checkStored w q && checkInputAt w q) &&
    (List.range (n * n + 2)).all (fun q ↦ checkSquareDigit w q && checkGeneratedAt w q)

#guard (List.range 9).all fun q ↦
  let P : MultiTapeTM 1 Bool (Fin 3) :=
    { q₀ := 0
      tr := fun state _ _ ↦
        if state = 0 then
          { inputTape := 0, workTapes := fun _ ↦ (some (some false), 1),
            output := some false, state := some 1 }
        else if state = 1 then
          { inputTape := 0, workTapes := fun _ ↦ (some (some true), -1),
            output := some true, state := some 2 }
        else
          { inputTape := 0, workTapes := fun _ ↦ (none, 0),
            output := some false, state := none } }
  let tm := readOutput P
  let start : ExecCfg 3 (StateOf tm) [] :=
    { ExecCfg.init tm [] with
      tapes := #v[register (counterWord q), ∅, register [false, true, false, true]]
      heads := #v[0, 0, 2]
      outputRev := [true, false] }
  let finish := (execStep tm)^[3 * (2 * 4 + 8)] start
  let expected := #v[register (counterWord (q - 3)), register (([false, true, false][q]?).toList),
    start.tapes[2] |>.insert 2 false |>.insert 3 true]
  finish.state.isNone && finish.inputPos.val == 1 && finish.heads == start.heads &&
    finish.outputRev == start.outputRev &&
    (List.finRange 3).all fun i ↦ (List.range 7).all fun j ↦
      finish.tapes[i][(j : ℤ) - 1]? == expected[i][(j : ℤ) - 1]?

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
