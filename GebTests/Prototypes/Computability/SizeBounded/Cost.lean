/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Computability.SizeBounded.Cost
import Geb.Prototypes.Computability.SizeBounded.Combinators

/-!
# The cost model on worked bitstrings

The account of the tail on a two-bit word: its value, its time, which counts
the base and two steps each reading the remaining word, and its greatest
length, which is the longer remaining word; and the tail's polynomial at that
length, which dominates the time.

## Main statements

The accounted value is the meaning, the time and greatest length are the ones
the evaluator's clauses give, and the polynomial read off the syntax bounds the
time at the word's length.

## Tags

non-size-increasing, cost model, polynomial time, linear space
-/

set_option linter.privateModule false

open Geb.SizeBounded

/-- The tail's account, named so that this module references a constant of the
module under test. -/
def tailAccount : Account := tailOf.account ![[true, false]]

/-- The accounted value is the tail. -/
theorem tailAccount_value : tailAccount.value = [false] := rfl

/-- The time: the base costs two, and each of the two steps one plus the length
of the remaining word plus one. -/
theorem tailAccount_time : tailAccount.time = 7 := rfl

/-- The greatest length read is that of the remaining word at the outer step. -/
theorem tailAccount_space : tailAccount.space = 1 := rfl

/-- The tail's polynomial at length two. -/
theorem timePoly_tailOf_two : timePoly tailOf.1.1 2 = 16 := rfl

/-- The time is within the polynomial at the word's length. -/
theorem tailAccount_time_le : tailAccount.time ≤ timePoly tailOf.1.1 2 := by decide

/-- The greatest length is within the linear bound. -/
theorem tailAccount_space_le : tailAccount.space ≤ max 2 (nsiConst tailOf.1.1) := by decide
