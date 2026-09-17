/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace -- shake: keep; #guard needs it

/-!
# The logspace subalgebra on worked bitstrings

The tail and the four-way conditional as successor-free expressions, evaluated
on representations at a worked input: a value is a word followed by an end
segment of the input, and each evaluation's denotation is the expression's
meaning on words.

## Main statements

The tail of an end segment of the input is the end segment one shorter, and the
tail of a value with a word part drops that part's head bit; the conditional
selects by the head bit of a value whose word part is empty, read off the
input. Each denotes what the expression means on words.

## Tags

logspace, simultaneous recursion on notation, representation
-/

set_option linter.privateModule false

open Geb.SizeBounded Geb.SizeBounded.Logspace

/-- The tail as a successor-free expression, named so that this module references a
constant of the module under test. It is `opaque` so that the compiler's type of
its machine, in the machine test module, is the one other modules would infer: a
`def` would be unfolded into the machine's state type locally and erased
elsewhere, which the compiler rejects. -/
public opaque tailL : LOf 1 := srnL (fun _ ↦ constL 0 []) (fun _ _ ↦ projL 2 0) 0

/-- The four-way conditional as a successor-free expression. -/
def condL : LOf 4 :=
  srnL (fun _ ↦ projL 3 0) (fun i _ ↦ if i then projL 5 3 else projL 5 4) 0

/-- The worked input. -/
def input : List Bool := [true, false, true, true, false]

/-- The tail of the whole input as a representation. -/
def tailInput : Rep := tailL.repSem input ![⟨[], 5⟩]

#guard tailInput = ⟨[], 4⟩

#guard tailInput.den input = input.tail

#guard tailL.sem ![input] = input.tail

/-- The tail of a value with a word part. -/
def tailWord : Rep := tailL.repSem input ![⟨[true, false], 2⟩]

#guard tailWord = ⟨[false], 2⟩

#guard tailWord.den input = [false, true, false]

/-- The tail of the empty value. -/
def tailEmpty : Rep := tailL.repSem input ![⟨[], 0⟩]

#guard tailEmpty = ⟨[], 0⟩

/-- The conditional on an end segment of the input with head bit `true`. -/
def condTrue : Rep := condL.repSem input ![⟨[], 3⟩, ⟨[true], 0⟩, ⟨[false], 0⟩, ⟨[], 1⟩]

#guard condTrue = ⟨[false], 0⟩

/-- The conditional on an end segment of the input with head bit `false`. -/
def condFalse : Rep := condL.repSem input ![⟨[], 1⟩, ⟨[true], 0⟩, ⟨[false], 0⟩, ⟨[], 2⟩]

#guard condFalse = ⟨[], 2⟩

/-- The conditional on the empty value. -/
def condEmpty : Rep := condL.repSem input ![⟨[], 0⟩, ⟨[true], 0⟩, ⟨[false], 0⟩, ⟨[], 2⟩]

#guard condEmpty = ⟨[true], 0⟩

#guard condL.sem ![input.rtake 3, [true], [false], input.rtake 1] = condTrue.den input

/-- Lemma 4.5 on the worked input: the value is short or an end segment. -/
example : (tailL.sem ![input]).length ≤ nsiConst tailL.1.1.1 ∨
    ∃ i, tailL.sem ![input] <:+ ![input] i :=
  length_le_or_suffix tailL ![input]
