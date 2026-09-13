/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Computability.SizeBounded.Combinators

/-!
# The combinators on worked bitstrings

The size-bounded successor at and past its bound, the tail, the conditional on
each shape of scrutinee, and a two-register simultaneous recursion: the word's
length in unary alongside the word itself, which a single recursion on notation
cannot produce without a bound.

## Main statements

The size-bounded successor prepends exactly when the result fits the bound; the
tail drops the head bit; the conditional selects by emptiness and head bit; and
the two registers of the recursion are computed together, each reading the other.

## Tags

non-size-increasing, simultaneous recursion on notation, combinator
-/

set_option linter.privateModule false

open Geb.SizeBounded

/-- The tail, named so that this module references a constant of the module under
test. -/
def tailArity : SOf 1 := tailOf

/-- Within the bound, the successor prepends. -/
theorem sbsOf_within : (sbsOf true).sem ![[false], [true, true]] = [true, false] := rfl

/-- At the bound, the successor returns its first argument unchanged. -/
theorem sbsOf_at_bound : (sbsOf true).sem ![[false, false], [true, true]] = [false, false] := rfl

/-- On the empty word the tail is empty. -/
theorem tailOf_nil : tailOf.sem ![[]] = [] := rfl

/-- The tail drops the head bit. -/
theorem tailOf_cons : tailOf.sem ![[true, false, true]] = [false, true] := rfl

/-- The conditional on the empty scrutinee. -/
theorem condOf_nil : condOf.sem ![[], [true], [false], [true, true]] = [true] := rfl

/-- The conditional on a scrutinee with head `true`. -/
theorem condOf_true : condOf.sem ![[true, false], [true], [false], [true, true]] = [false] := rfl

/-- The conditional on a scrutinee with head `false`. -/
theorem condOf_false : condOf.sem ![[false], [true], [false], [true, true]] = [true, true] := rfl

/-- Two registers over the word: the first holds the word read so far and the
second its length in unary, bounded by the parameter. The step of register one
prepends `true` bounded by the parameter, and that of register zero is the
remaining word. -/
def lengthRegs (l : Fin 2) : SOf 2 :=
  srnOf ![constOf 1 [], constOf 1 []]
    (fun _ ↦ ![projOf 4 0, sbsApp true (projOf 4 2) (projOf 4 3)]) l

/-- Register zero after the whole word is the tail of the word. -/
theorem lengthRegs_zero :
    (lengthRegs 0).sem ![[true, false, true], [true, false, true]] = [false, true] := rfl

/-- Register one after the whole word is the word's length in unary. -/
theorem lengthRegs_one :
    (lengthRegs 1).sem ![[true, false, true], [true, false, true]] = [true, true, true] := rfl

/-- With a shorter parameter the unary length is capped at the parameter's
length: the bound is a parameter, not the recursion variable. -/
theorem lengthRegs_one_capped :
    (lengthRegs 1).sem ![[true, false, true], [true]] = [true] := rfl
