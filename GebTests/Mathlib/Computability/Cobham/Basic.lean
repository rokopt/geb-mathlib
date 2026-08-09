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
Admissibility is exercised in both directions: a `boundedRec` term whose
recursion stays within its bound and one whose recursion outgrows it, the
latter refuted at a literal environment. The derived predecessor and
conditional are evaluated at literal environments, the conditional at all
three of its scrutinee cases against pairwise distinct branch arguments, and
both are checked to be smash-free.

## Main statements

The evaluations agree with the bit-order convention and with `smash`'s length
formula, and pin the argument `boundedRec` recurses on; `RecBounded` separates a
recursion meeting its bound from one outgrowing it; and `SmashFree` rejects a
`smash` node at any depth while accepting a term carrying none, the derived
predecessor and conditional among them.

## References

* [HeraudNowak2011]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, bitstring generators, admissibility
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

/-- `C.eval` agrees with the underlying tree's interpretation: the transport along
`fst_eval` that carries the meaning to the expression's own arity does not obstruct
reduction. -/
theorem eval_concatOf :
    concatOf.1.eval ![[true], [false, false]] = [false, false, true] := rfl

/-- The order-discriminating term is not admissible: its recursion returns the
second argument while its bound child (`proj 2 0`) returns the first, so at
`![[true], [false, false]]` the value has length two and the bound length one.
`RecBounded` therefore rejects a recursion that outgrows its bound, rather than
holding of every tree. -/
theorem not_recBounded_boundedRecOrderTerm : ¬ RecBounded boundedRecOrderTerm :=
  fun h ↦ absurd (h.1 ![[true], [false, false]]) (by decide)

/-- The order-discriminating term with its bound child replaced by `proj 2 1`, which
returns the same argument the recursion threads through. -/
def boundedRecBoundTermRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 1)
    ![WType.mk (.proj 1 0) Fin.elim0, WType.mk (.proj 3 2) Fin.elim0,
      WType.mk (.proj 3 2) Fin.elim0, WType.mk (.proj 2 1) Fin.elim0]

/-- The bounded term, admissible. -/
def boundedRecBoundTerm : sig.W := ⟨boundedRecBoundTermRaw, by decide⟩

/-- A `boundedRec` node whose bound holds: the recursion returns the second argument
at every recursion variable, which is what the bound child returns too. Together with
`not_recBounded_boundedRecOrderTerm` this pins the `boundedRec` clause of
`RecBoundedValue` to a condition that some recursions meet and others fail. -/
theorem recBounded_boundedRecBoundTerm : RecBounded boundedRecBoundTerm := by
  refine ⟨fun x ↦ le_of_eq (congrArg List.length ?_), ?_⟩
  · refine List.rec rfl (fun b _ _ ↦ ?_) (x 0)
    cases b <;> rfl
  · refine fun b : Fin 4 ↦ ?_
    match b with
    | 0 | 1 | 2 | 3 => exact ⟨trivial, fun d ↦ d.elim0⟩

open scoped FinEnum in
/-- A smash node is rejected wherever it sits. -/
def smashFreeCheck : Bool :=
  decide (Cobham.SmashFree Cobham.concatOf.1) &&
    decide (¬ Cobham.SmashFree Cobham.smashOf.1)

example : smashFreeCheck = true := by decide

/-- A `comp`-headed raw tree whose sole argument is the shape given, its head a
`proj 1 0` node of the matching arity, isolating which node makes `smashFreeBool`
differ. -/
def compOfRaw (child : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 2 1) fun d ↦
    match d with
    | .inl () => WType.mk (.proj 1 0) Fin.elim0
    | .inr _ => child

/-- A `comp` node whose argument is `smash`, one level below the root. -/
def smashBelowRootRaw : sig.toPFunctor.W := compOfRaw smashRaw

/-- `smashBelowRootRaw`, admissible as a `sig`-tree. -/
theorem smashBelowRootRaw_admissible : sig.WValid smashBelowRootRaw := by decide

/-- `smashBelowRootRaw` as an expression, its recursion bound vacuous at every node
since both nodes are `comp`. -/
def smashBelowRootTerm : C :=
  ⟨⟨smashBelowRootRaw, smashBelowRootRaw_admissible⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩

/-- A `comp` node whose argument is `smashBelowRootRaw`, so `smash` sits two levels
below the root. -/
def smashNestedRaw : sig.toPFunctor.W := compOfRaw smashBelowRootRaw

/-- `smashNestedRaw`, admissible as a `sig`-tree. -/
theorem smashNestedRaw_admissible : sig.WValid smashNestedRaw := by decide

/-- `smashNestedRaw` as an expression. -/
def smashNestedTerm : C :=
  ⟨⟨smashNestedRaw, smashNestedRaw_admissible⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => smashBelowRootTerm.2⟩⟩

/-- A `comp` node whose argument is `concat`, structurally parallel to
`smashBelowRootRaw` but with `smash` replaced by `concat`. -/
def concatBelowRootRaw : sig.toPFunctor.W := compOfRaw concatRaw

/-- `concatBelowRootRaw`, admissible as a `sig`-tree. -/
theorem concatBelowRootRaw_admissible : sig.WValid concatBelowRootRaw := by decide

/-- `concatBelowRootRaw` as an expression. -/
def concatBelowRootTerm : C :=
  ⟨⟨concatBelowRootRaw, concatBelowRootRaw_admissible⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩

/-- A `comp` node whose argument is `concatBelowRootRaw`, smash-free two levels
below the root as well as at the root and at depth one. -/
def smashFreeNestedRaw : sig.toPFunctor.W := compOfRaw concatBelowRootRaw

/-- `smashFreeNestedRaw`, admissible as a `sig`-tree. -/
theorem smashFreeNestedRaw_admissible : sig.WValid smashFreeNestedRaw := by decide

/-- `smashFreeNestedRaw` as an expression. -/
def smashFreeNestedTerm : C :=
  ⟨⟨smashFreeNestedRaw, smashFreeNestedRaw_admissible⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => concatBelowRootTerm.2⟩⟩

/-- `SmashFree` rejects a `smash` node one level below the root, and two levels
below the root, catching a check that inspects only the root's own shape or only
its immediate children; and accepts a term smash-free at every depth, catching a
check that rejects `comp` nodes outright or that never recurses past depth one. -/
def smashFreeHereditaryCheck : Bool :=
  decide (¬ Cobham.SmashFree smashBelowRootTerm) &&
    decide (¬ Cobham.SmashFree smashNestedTerm) &&
      decide (Cobham.SmashFree smashFreeNestedTerm)

example : smashFreeHereditaryCheck = true := by decide

/-- `pred` drops the Lean list's head, which is the word's last bit, and fixes the
empty word. -/
def predCheck : Bool :=
  decide (predSem ![[true, false, true]] = [false, true]) && decide (predSem ![[]] = [])

example : predCheck = true := by decide

/-- The three-way dispatch of `cond`, at three branch arguments pairwise distinct
in both value and length. The empty scrutinee selects the second argument, a
scrutinee whose last bit is `1` the third, and one whose last bit is `0` the
fourth. Transposing the two step children of `condRaw` would return `[true, true]`
where `[true]` is asserted and `[true]` where `[true, true]` is asserted, so this
discriminates that transposition independently of how `condSem_eq` is stated. -/
def condDispatchCheck : Bool :=
  decide (condSem ![[], [false], [true], [true, true]] = [false]) &&
    decide (condSem ![[true], [false], [true], [true, true]] = [true]) &&
      decide (condSem ![[false], [false], [true], [true, true]] = [true, true])

example : condDispatchCheck = true := by decide

/-- `pred` and `cond` lie in the subalgebra `SmashFree` names: the bound child of
`condRaw` concatenates the three branch arguments where [HeraudNowak2011] smashes
them. -/
def smashFreeDerivedCheck : Bool :=
  decide (Cobham.SmashFree pred.1) && decide (Cobham.SmashFree cond.1)

example : smashFreeDerivedCheck = true := by decide
