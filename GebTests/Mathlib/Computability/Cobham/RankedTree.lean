/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Mathlib.Data.Tree.Ranked.Basic

import Geb.Mathlib.Computability.Cobham.RankedTree

/-!
# The generic ranked recognizer on worked alphabets

The recognizer's verdict on short accepted and rejected words at two worked
alphabets, the decoder's fields at each block length the scan reaches, and the
agreement of the recognizer with `RankedAlphabet.validBool` over an
enumeration of words at three alphabets.

## Main definitions

* `isRankedArity` — the recognizer at its declared arity.

## Main statements

The assertions below give the recognizer's value at `binRanked` on a leaf's
spelling, on a bare node and on a node over two leaves; its value at
`narrowAlphabet` on a nullary symbol's block, on a block spelling no symbol, on
a unary symbol over a nullary one, and on a symbol whose arity exceeds the
pending count; the decoder's fields on the initial state, on a state carrying
an incomplete block, on a failed state, and on a state whose pending count
exceeds the depth window `R.maxArity + 1`; the slot's length at a block
violating
`Cobham.length_bufBits_of_lt`'s hypothesis, pinning that the hypothesis is
consumed; and the agreement of `Cobham.isRankedSem` with
`RankedAlphabet.validBool` over every word of at most the length each sweep
records.

## Implementation notes

`RankedAlphabet.Scan` derives no `DecidableEq`, so the decoder's inversion is
asserted field by field rather than as one equation.

The sweep lengths are measured rather than conventional. `sampleAlphabet`'s
largest arity is one above `narrowAlphabet`'s, so its dispatch is one bit
wider and each reduction descends one dispatch level further; its sweep is
taken to length five, six exceeding the default heartbeat limit. The case
tree is a `Nat.rec`, so the elaborated term is of constant size and one
reduction follows a single root-to-leaf path; the cost is linear in the
number of bits dispatched on, not exponential in them.
`binRanked` has width one, so its block slot is the bare sentinel, and that
alphabet is the subject of the bridge to `Cobham.isTree`.

## Tags

Cobham, ranked alphabet, preorder, recognizer
-/

set_option linter.privateModule false

open Cobham RankedAlphabet

/-- The recognizer at its declared arity: this module's only use of
`Cobham.isRankedOf`, the assertions below reading `Cobham.isRankedSem`
instead. -/
def isRankedArity : COf 1 := isRankedOf narrowAlphabet

/-- At the two-symbol alphabet a leaf's spelling is accepted. -/
theorem isRankedSem_binRanked_leaf :
    isRankedSem RankedAlphabet.Binary.binRanked ![[false]] = [true] := by decide

/-- A bare node symbol has no children pending, and is rejected. -/
theorem isRankedSem_binRanked_bare_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true]] = [] := by decide

/-- A node over two leaves is accepted. -/
theorem isRankedSem_binRanked_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true, false, false]] =
      [true] := by decide

/-- A nullary symbol's block alone is accepted. -/
theorem isRankedSem_narrow_nullary :
    isRankedSem narrowAlphabet ![[false, false]] = [true] := by decide

/-- A block spelling no symbol is rejected. -/
theorem isRankedSem_narrow_no_symbol :
    isRankedSem narrowAlphabet ![[true, true]] = [] := by decide

/-- A unary symbol over a nullary one is accepted. -/
theorem isRankedSem_narrow_unary :
    isRankedSem narrowAlphabet ![[true, false, false, false]] = [true] := by decide

/-- A binary symbol with nothing pending is rejected. -/
theorem isRankedSem_narrow_underflow :
    isRankedSem narrowAlphabet ![[false, true]] = [] := by decide

/-- The decoder recovers the initial state's empty block. -/
theorem decodeState_initial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).buf = [] := by decide

/-- And its pending count. -/
theorem decodeState_initial_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).depth = 0 := by decide

/-- And its flag. -/
theorem decodeState_initial_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).live = true := by decide

/-- The decoder recovers a state carrying one bit of an incomplete block. -/
theorem decodeState_partial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[true], 1, true⟩))).buf = [true] := by decide

/-- And a failed state's flag. -/
theorem decodeState_dead_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 2, false⟩))).live = false := by decide

/-- A pending count above the depth window is recovered capped, which is what
`Cobham.decodeState_stateWord_of_lt`'s `min` states. That window is
`R.maxArity + 1`, three at `narrowAlphabet`, and is not `dispatchWidth`, which
is six there. -/
theorem decodeState_capped_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 5, true⟩))).depth = 3 := by decide

/-- A block of the alphabet's own width overflows the slot, so
`Cobham.length_bufBits_of_lt`'s hypothesis is consumed rather than
decorative. -/
theorem length_bufBits_overflow :
    (bufBits narrowAlphabet [false, true]).length = 3 := by decide

/-- The recognizer and the validity scan accept the same words, at the
alphabet reaching the block that spells no symbol, over every word of length
at most six. -/
theorem isRankedSem_eq_validBool_narrow :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem narrowAlphabet ![w] == [true]) ==
        narrowAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at an alphabet every one of whose blocks spells a symbol, over every
word of length at most five. -/
theorem isRankedSem_eq_validBool_sample :
    (wordsUpTo 5).all (fun w ↦
      (isRankedSem sampleAlphabet ![w] == [true]) ==
        sampleAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at the two-symbol alphabet, over every word of length at most six. -/
theorem isRankedSem_eq_validBool_binRanked :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem RankedAlphabet.Binary.binRanked ![w] == [true]) ==
        RankedAlphabet.Binary.binRanked.validBool w) = true := by
  set_option maxRecDepth 100000 in decide
