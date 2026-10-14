/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Machine

set_option doc.verso true in
/-!
# Machines for word-algebra primitives

Constants can be emitted by finite control without work tapes. The unary projection
copies the read-only input to the write-only output, also without work tapes.

## Main definitions

* {lit}`constantMachineTr`, {lit}`constantMachine` — the transition, and the
  machine, that emit a fixed word.
* {lit}`identityMachineTr`, {lit}`identityMachine` — the transition, and the
  machine, that copy the input word.

## Tags

Turing machine, bitstring, constant, projection
-/

set_option doc.verso true

@[expose] public section

namespace Geb.SizeBounded

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb)

/-- The transition of {lit}`constantMachine`: state {lit}`q` emits the
{lit}`q`-th letter of {lit}`v` and advances, the last state halts. -/
def constantMachineTr (v : List Bool) (q : Fin (v.length + 1)) (_ : Option (Fin 2))
    (_ : Fin 0 → Option (Fin 2)) : Action 0 (Fin 2) (Fin (v.length + 1)) :=
  { inputTape := 0, workTapes := Fin.elim0,
    output := v[q.val]?.map boolEmb,
    state := if h : q.val < v.length then some ⟨q.val + 1, by omega⟩ else none }

/-- Emit the prescribed word in order, then halt; the input is ignored. -/
def constantMachine (v : List Bool) : MultiTapeTM 0 (Fin 2) (Fin (v.length + 1)) :=
  ofTr 0 (constantMachineTr v)

/-- The transition of {lit}`identityMachine`: emit the symbol read and move the
input head right, halting at the blank past the input. -/
def identityMachineTr (_ : Fin 1) (input : Option (Fin 2)) (_ : Fin 0 → Option (Fin 2)) :
    Action 0 (Fin 2) (Fin 1) :=
  { inputTape := 1, workTapes := Fin.elim0, output := input,
    state := input.map fun _ ↦ 0 }

/-- Copy one input symbol per transition and halt at the right input boundary. -/
def identityMachine : MultiTapeTM 0 (Fin 2) (Fin 1) := ofTr 0 identityMachineTr

end Geb.SizeBounded
