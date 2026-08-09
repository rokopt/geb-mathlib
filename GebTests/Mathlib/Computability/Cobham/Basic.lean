/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.Cobham.Basic

/-!
# Worked evaluations of Cobham's generators and bounded recursion

`concat`, `succ` and `smash` on literal environments, discriminating the
bit-order convention that a Lean list's head is a bitstring's last bit and
confirming `smash`'s length formula; and a two-argument `boundedRec` term
discriminating recursion on the first argument from recursion on the last.

## Main statements

The four assertions below.

## Tags

Cobham, bounded recursion on notation, bitstring generators
-/

set_option linter.privateModule false

open Cobham

/-- The `concat` generator as a single node, its `Direction` being empty. -/
def concatTermRaw : sig.toPFunctor.W := WType.mk .concat Fin.elim0

/-- The `concat` generator, admissible. -/
def concatTerm : sig.W := ⟨concatTermRaw, by decide⟩

/-- `concat` reads its second argument as the earlier part of the word and its
first as the later part: under an order where the first argument came first,
`![true], [false, false]` would evaluate to `[true, false, false]` rather than
the `[false, false, true]` asserted here. -/
theorem eval_concatTerm :
    (eval concatTerm).2 ![[true], [false, false]] = [false, false, true] := rfl

/-- The `smash` generator as a single node, its `Direction` being empty. -/
def smashTermRaw : sig.toPFunctor.W := WType.mk .smash Fin.elim0

/-- The `smash` generator, admissible. -/
def smashTerm : sig.W := ⟨smashTermRaw, by decide⟩

/-- `smash` marks its result with a leading `true`, so its length is the
product of its arguments' lengths plus one. -/
theorem eval_smashTerm :
    (eval smashTerm).2 ![[true, false], [true, true, false]] =
      true :: List.replicate 6 false := rfl

/-- The `succ true` generator as a single node, its `Direction` being empty. -/
def succTermRaw : sig.toPFunctor.W := WType.mk (.succ true) Fin.elim0

/-- The `succ true` generator, admissible. -/
def succTerm : sig.W := ⟨succTermRaw, by decide⟩

/-- `succ b` prepends `b` to its argument: under a convention that appended
instead, `![true, false]` would evaluate to `[true, false, true]` rather than
the `[true, true, false]` asserted here. -/
theorem eval_succTerm : (eval succTerm).2 ![[true, false]] = [true, true, false] := rfl

/-- A `boundedRec` term of arity `(1 + 1)` whose base and both step
expressions ignore the recursed bitstring and the recursive value, returning
only the other argument (`proj 3 2` reads the third slot of the step
children's `Fin.cons v (Fin.cons (ih x) x)` environment, which is `x 0`; `proj
1 0` reads the base's sole slot the same way). Every branch therefore returns
whichever of the two original arguments `evalValue`'s `boundedRec` clause
threads through as the fixed argument, regardless of the other argument's
length or content. The bound child (`proj 2 0`) is never consulted by `eval`
and is present only to complete the tree. -/
def boundedRecOrderTermRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 1)
    ![WType.mk (.proj 1 0) Fin.elim0, WType.mk (.proj 3 2) Fin.elim0,
      WType.mk (.proj 3 2) Fin.elim0, WType.mk (.proj 2 0) Fin.elim0]

/-- The order-discriminating `boundedRec` term, admissible. -/
def boundedRecOrderTerm : sig.W := ⟨boundedRecOrderTermRaw, by decide⟩

/-- `evalRec` recurses on the first argument, per [HeraudNowak2011]'s `Rec`,
threading the second argument through unchanged: the result is the second
argument regardless of the first. Under [Strahm2003]'s last-argument form,
recursion would instead run on the second argument while the first is
threaded through, so the same environment would evaluate to `[true]`, the
first argument, rather than the `[false, false]` asserted here. -/
theorem eval_boundedRecOrderTerm :
    (eval boundedRecOrderTerm).2 ![[true], [false, false]] = [false, false] := rfl
