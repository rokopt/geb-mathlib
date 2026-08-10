/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Ranked.Code
public import GebTests.Mathlib.Data.Tree.Ranked.Basic

/-!
# Symbol codes on a worked alphabet

The blocks of `sampleAlphabet`, their decoding, and the arity they carry,
including the value beyond the alphabet at which `arOf` is absent.

## Main statements

The assertions below give the blocks of the nullary and binary symbols, the
value each block denotes, the arity each carries, and the absence of an arity
at a value no symbol has.

## Tags

ranked alphabet, code, binary representation, decoding
-/

set_option linter.privateModule false

open RankedAlphabet

/-- A block is the symbol's index in binary, least significant bit first. -/
theorem code_sampleSym0 : sampleAlphabet.code sampleSym0 = [false, false] := by decide

/-- The binary symbol's index is two, whose low bit is clear and whose next
bit is set. -/
theorem code_sampleSym2 : sampleAlphabet.code sampleSym2 = [false, true] := by decide

/-- A block decodes to the symbol it spells. -/
theorem decodeBits_code_sampleSym2 :
    decodeBits (sampleAlphabet.code sampleSym2) = 2 := by decide

/-- And so carries that symbol's arity. -/
theorem arOf_two : sampleAlphabet.arOf 2 = some 2 := by decide

/-- The nullary symbol's arity. -/
theorem arOf_zero : sampleAlphabet.arOf 0 = some 0 := by decide

/-- A value no symbol has carries no arity. Every two-bit block spells a
symbol of this alphabet, so the absent case is reached only from beyond the
alphabet. -/
theorem arOf_four : sampleAlphabet.arOf 4 = none := by decide

/-- A block's entries are the bits of the value it denotes. -/
theorem testBit_decodeBits_sampleSym2 :
    (decodeBits (sampleAlphabet.code sampleSym2)).testBit 1 = true := by decide
