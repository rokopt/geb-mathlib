/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.BellantoniCook.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable

/-!
# A tree recognizer in the Bellantoni-Cook class

Three expressions of `B` deciding whether a bitstring is the preorder
spelling of a binary tree. `B` is a characterization of the
polynomial-time functions [BellantoniCook1992], which is used and not
proved here, so the membership test lies in that class without a separate
complexity argument.

The recognizer is a single right-to-left scan rather than a recursive
descent. A descent would parse the second subtree from a remainder the
first call computes, which sits in safe position, and recursion on a safe
argument is what the class forbids.

## Main definitions

* `BellantoniCook.zeroAtRaw`, `BellantoniCook.oneAtRaw` — the empty
  bitstring and the one-bit string `[true]` at an arbitrary arity.
* `BellantoniCook.falseAtRaw` — the one-bit string `[false]` at an
  arbitrary arity.
* `BellantoniCook.comb` — the stack depth and the underflow verdict in a
  single value, of arity `(1, 0)`.
* `BellantoniCook.eqOne` — whether a bitstring has length one, of arity
  `(0, 1)`.
* `BellantoniCook.isTree` — the recognizer, of arity `(1, 0)`.
* `BellantoniCook.combSem`, `BellantoniCook.eqOneSem` and
  `BellantoniCook.isTreeSem` — the meaning of each of the three at its
  arity, over which every statement of the module is stated.

## Implementation notes

The scan carries the stack depth and the underflow verdict in one
recursive value, told apart by its head. While no node bit has been read
below depth two the value is the depth in unary offset by one, so its
head is `true`; once one has been, the value is `[false]`, which the node
step reproduces, that value's two predecessors being empty. Each bit is
read once.

`combSem`, `eqOneSem` and `isTreeSem` name each meaning at its arity, so
that the arity pair is reduced and rewriting under it type-checks. A
meaning taken through the `Sigma` projection instead has a type headed by
that projection rather than by an arrow, and `rw` under it fails as not
type-correct at `implicit` transparency.

## References

* [BellantoniCook1992]

## Tags

Bellantoni-Cook, polytime, implicit computational complexity, safe
recursion, binary tree, preorder, recognizer
-/

namespace BellantoniCook

public section

/-- The empty bitstring at an arbitrary arity. -/
@[expose] def zeroAtRaw (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 0)
    (compChildren (WType.mk .zero Fin.elim0) Fin.elim0 Fin.elim0)

/-- The one-bit string `[true]` at an arbitrary arity. -/
@[expose] def oneAtRaw (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0 ![zeroAtRaw n s])

/-- The one-bit string `[false]` at an arbitrary arity. -/
@[expose] def falseAtRaw (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 1)
    (compChildren (WType.mk (.succ false) Fin.elim0) Fin.elim0 ![zeroAtRaw n s])

/-- Prepend `true` to the recursive value. -/
@[expose] def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

/-- Drop the low bit of the recursive value. -/
@[expose] def decRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

/-- The guard of the node step: the recursive value with two bits
dropped. It is empty exactly when the value is the failure flag, whose
two predecessors truncate to the empty bitstring, or a depth below
two. -/
@[expose] def predPredRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0 ![decRaw])

/-- The leaf step: push a level onto a live value, whose head is `true`,
and return the failure flag on a value that is empty or has head
`false`. -/
@[expose] def combFalseStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0, falseAtRaw 1 1, incRaw,
        falseAtRaw 1 1])

/-- The node step: pop a level when at least two remain, and return the
failure flag otherwise. An existing failure propagates, its guard being
empty. -/
@[expose] def combTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![predPredRaw, falseAtRaw 1 1, decRaw, decRaw])

/-- The raw tree of the scan. The base is `[true]`, the empty bitstring
having depth zero and satisfying `ok`. -/
@[expose] def combRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0) ![oneAtRaw 0 0, combFalseStepRaw, combTrueStepRaw]

/-- The stack depth and the underflow verdict of a bitstring in one
value: the depth in unary, offset by one so that a live value is
non-empty with head `true`, and `[false]` once a node bit has been read
below depth two. -/
@[expose] def comb : BC := ⟨combRaw, by decide⟩

/-- The inner conditional of `eqOne`: whether the predecessor of the
argument is empty. The even branch is unreachable only under this
module's own use, where the argument is always a unary numeral; the
expression and its characterization are stated for an arbitrary
bitstring, over which the branch is reached. -/
@[expose] def eqOneInnerRaw : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.comp 0 1 0 1)
          (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
            ![WType.mk (.proj 0 1 0) Fin.elim0]),
        oneAtRaw 0 1, zeroAtRaw 0 1, zeroAtRaw 0 1])

/-- The raw tree of the one-test: empty is not one, and otherwise the
argument is one exactly when its predecessor is empty. -/
@[expose] def eqOneRaw : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.proj 0 1 0) Fin.elim0, zeroAtRaw 0 1, eqOneInnerRaw,
        eqOneInnerRaw])

/-- Whether a bitstring has length one, returning `[true]` or `[]`. -/
@[expose] def eqOne : BC := ⟨eqOneRaw, by decide⟩

/-- The raw tree of the recognizer: the scan's predecessor has length
one. -/
@[expose] def isTreeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 0 0 1)
    (compChildren eqOneRaw Fin.elim0
      ![WType.mk (.comp 1 0 0 1)
          (compChildren (WType.mk .pred Fin.elim0) Fin.elim0 ![combRaw])])

/-- The recognizer: whether a bitstring is the preorder spelling of a
binary tree. The output is `[true]` or `[]`, so correctness is an
equation rather than a disequation. -/
@[expose] def isTree : BC := ⟨isTreeRaw, by decide⟩

/-- `comb` at its declared arity. Elaborating this is the assertion that
`BC.arity comb` is `(1, 0)`. -/
@[expose] def combOf : BCOf 1 0 := ⟨comb, rfl⟩

/-- `eqOne` at its declared arity. -/
@[expose] def eqOneOf : BCOf 0 1 := ⟨eqOne, rfl⟩

/-- `isTree` at its declared arity. -/
@[expose] def isTreeOf : BCOf 1 0 := ⟨isTree, rfl⟩

/-- The scan's meaning at its arity, ascribed so that the arity pair is
reduced and rewriting under it type-checks. -/
@[expose] def combSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool := (BC.eval comb).2

/-- The one-test's meaning at its arity, ascribed likewise. -/
@[expose] def eqOneSem :
    (Fin 0 → List Bool) → (Fin 1 → List Bool) → List Bool := (BC.eval eqOne).2

/-- The recognizer's meaning at its arity, ascribed likewise. -/
@[expose] def isTreeSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool := (BC.eval isTree).2

end

end BellantoniCook
