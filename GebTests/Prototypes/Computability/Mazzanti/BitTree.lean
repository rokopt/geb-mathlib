/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Computability.Mazzanti.BitTree

/-!
# The bit-tree recognizer on worked bitstrings

The registers after scanning the encoding of the empty leaf, and the recognizer
on the empty leaf, a leaf with a payload, a fork of two leaves, the empty word,
a lone fork bit, an incomplete fork, a leaf followed by a trailing leaf, and the
all-fork word whose count would exceed the bound.

## Main statements

The recognizer returns `[true]` on each encoding and the empty word on each
non-encoding, agreeing with `Geb.BitTree.validBool` at every worked word.

## Tags

non-size-increasing, binary tree, bitstring, recognizer
-/

set_option linter.privateModule false

open Geb.Mazzanti

/-- The recognizer, named so that this module references a constant of the module
under test. -/
def isBitTreeArity : SOf 1 := isBitTree

/-- After the encoding of the empty leaf the remainder register is empty. -/
theorem regs_empty_leaf_rest : regs [false, false] [false, false] 0 = [] := rfl

/-- After the encoding of the empty leaf the mode register holds the done code. -/
theorem regs_empty_leaf_mode : regs [false, false] [false, false] 1 = modeCode .done := rfl

/-- After the encoding of the empty leaf the count register is empty: the one
pending tree, minus one. -/
theorem regs_empty_leaf_count : regs [false, false] [false, false] 2 = [] := rfl

/-- After the first bit of the empty leaf the mode register holds the string code
and the count register is still empty. -/
theorem regs_half_leaf_mode : regs [false] [false, false] 1 = modeCode .string := rfl

/-- After a fork bit the count register holds one `true`: two pending trees, minus
one. -/
theorem regs_fork_count : regs [true] [true, false, false, false, false] 2 = [true] := rfl

/-- The empty leaf is accepted. -/
theorem accept_empty_leaf : isBitTree.sem ![[false, false]] = [true] := rfl

/-- A leaf with the payload `[true]` is accepted. -/
theorem accept_payload_leaf : isBitTree.sem ![[false, true, true, false]] = [true] := rfl

/-- A fork of two empty leaves is accepted. -/
theorem accept_fork : isBitTree.sem ![[true, false, false, false, false]] = [true] := rfl

/-- The empty word is rejected. -/
theorem reject_nil : isBitTree.sem ![[]] = [] := rfl

/-- A lone fork bit is rejected. -/
theorem reject_fork_bit : isBitTree.sem ![[true]] = [] := rfl

/-- A fork with one child is rejected. -/
theorem reject_incomplete_fork : isBitTree.sem ![[true, false, false]] = [] := rfl

/-- A leaf followed by another leaf is rejected. -/
theorem reject_trailing : isBitTree.sem ![[false, false, false, false]] = [] := rfl

/-- The all-fork word is rejected; its last increment is suppressed by the bound,
which does not change the verdict. -/
theorem reject_all_forks : isBitTree.sem ![[true, true, true]] = [] := rfl

/-- The worked words. -/
def workedWords : List (List Bool) :=
  [[false, false], [false, true, true, false], [true, false, false, false, false], [], [true],
    [true, false, false], [false, false, false, false], [true, true, true]]

/-- The recognizer agrees with the scanner on the worked words. -/
theorem agree_validBool :
    workedWords.map (fun w ↦ decide (isBitTree.sem ![w] = [true])) =
      workedWords.map Geb.BitTree.validBool := by decide
