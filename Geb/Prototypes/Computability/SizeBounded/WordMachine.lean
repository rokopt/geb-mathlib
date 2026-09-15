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

* {lit}`constantMachine` emits a fixed word.
* {lit}`identityMachine` copies the input word.

## Tags

Turing machine, bitstring, constant, projection
-/

set_option doc.verso true

@[expose] public section

namespace Geb.SizeBounded

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb)

/-- Emit the prescribed word in order, then halt; the input is ignored. -/
def constantMachine (v : List Bool) : MultiTapeTM 0 (Fin 2) (Fin (v.length + 1)) where
  q₀ := 0
  tr q _ _ :=
    { inputTape := 0, workTapes := Fin.elim0,
      output := v[q.val]?.map boolEmb,
      state := if h : q.val < v.length then some ⟨q.val + 1, by omega⟩ else none }

/-- Copy one input symbol per transition and halt at the right input boundary. -/
def identityMachine : MultiTapeTM 0 (Fin 2) (Fin 1) where
  q₀ := 0
  tr _ input _ :=
    { inputTape := 1, workTapes := Fin.elim0, output := input,
      state := input.map fun _ ↦ 0 }

end Geb.SizeBounded
