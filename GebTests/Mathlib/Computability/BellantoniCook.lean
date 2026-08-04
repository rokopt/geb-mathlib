/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.BellantoniCook
import Geb.Mathlib.Data.PFunctor.Slice.Decidable

/-!
# Worked expressions of the Bellantoni-Cook class

The `plus` and `mult` of [HeraudNowak2011] § 3.2, a recursion whose two step
expressions differ, four single-node expressions, and one inadmissible raw
tree. Each expression is built in two steps — a raw tree bound as its own
definition, then the admissible expression — because an inline `WType.mk`
application blocks the instance search that `decide` needs.

`plus` and `mult` are transcribed with the arities of the authors' Coq
development. The composition superscripts printed in § 3.2's `mult` are
`plus`'s and do not satisfy the paper's own arity relation.

## Main statements

The thirteen assertions below: twelve expected outputs of `BC.eval`, and one
inadmissible tree.

## References

* [HeraudNowak2011]

## Tags

Bellantoni-Cook, polytime, safe recursion
-/

set_option linter.privateModule false

open BellantoniCook

/-- The children of a `comp` node, in the order `Direction` gives them: the
head, then the normal arguments, then the safe arguments. -/
def compChildren {m k : ℕ} (h : sig.toPFunctor.W)
    (gN : Fin m → sig.toPFunctor.W) (gS : Fin k → sig.toPFunctor.W) :
    Unit ⊕ Fin m ⊕ Fin k → sig.toPFunctor.W :=
  Sum.elim (fun _ ↦ h) (Sum.elim gN gS)

/-- The step expression of `plus`: the successor appending `true`, applied
to the recursive value. -/
def plusStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 2 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 2 1) Fin.elim0])

/-- The step expression of `plus`, admissible. -/
def plusStep : BC := ⟨plusStepRaw, by decide⟩

/-- `plus`, of arity `(1, 1)`: it prepends one `true` per bit of its normal
argument to its safe argument. -/
def plusRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 1)
    ![WType.mk (.proj 0 1 0) Fin.elim0, plusStep.val, plusStep.val]

/-- `plus`, admissible. -/
def plus : BC := ⟨plusRaw, by decide⟩

/-- The base expression of `mult`: the constant empty bitstring at
arity `(1, 0)`. -/
def multBaseRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 0 0 0)
    (compChildren (WType.mk .zero Fin.elim0) Fin.elim0 Fin.elim0)

/-- The base expression of `mult`, admissible. -/
def multBase : BC := ⟨multBaseRaw, by decide⟩

/-- The step expression of `mult`: `plus` of the second normal argument and
the recursive value. -/
def multStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 1 1 1)
    (compChildren plus.val ![WType.mk (.proj 2 0 1) Fin.elim0]
      ![WType.mk (.proj 2 1 2) Fin.elim0])

/-- The step expression of `mult`, admissible. -/
def multStep : BC := ⟨multStepRaw, by decide⟩

/-- `mult`, of arity `(2, 0)`: it produces one `true` per pair of bits of
its two normal arguments. -/
def multRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 1 0) ![multBase.val, multStep.val, multStep.val]

/-- `mult`, admissible. -/
def mult : BC := ⟨multRaw, by decide⟩

/-- `plus` at its declared arity. Elaborating this is exactly the assertion
that `BC.arity plus` is `(1, 1)`. -/
def plusOf : BCOf 1 1 := ⟨plus, rfl⟩

/-- `mult` at its declared arity. -/
def multOf : BCOf 2 0 := ⟨mult, rfl⟩

/-- `plus` on an empty normal argument returns its safe argument. -/
theorem eval_plus_nil : (BC.eval plus).2 ![[]] ![[false]] = [false] := rfl

/-- `plus` prepends one `true` per bit of its normal argument. -/
theorem eval_plus_cons :
    (BC.eval plus).2 ![[true, true]] ![[false]] = [true, true, false] := rfl

/-- `mult` produces one `true` per pair of bits of its two normal
arguments. -/
theorem eval_mult :
    (BC.eval mult).2 ![[true, true], [true, true, true]] ![] =
      List.replicate 6 true := rfl

/-- A recursion whose two step expressions differ: the `false` branch
returns the remaining bitstring, the `true` branch recurses. Without it no
assertion here would distinguish the two step expressions, `plus` and `mult`
passing the same expression as both. -/
def branchRecRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0)
    ![WType.mk .zero Fin.elim0, WType.mk (.proj 1 1 0) Fin.elim0,
      WType.mk (.proj 1 1 1) Fin.elim0]

/-- The discriminating recursion, admissible. -/
def branchRec : BC := ⟨branchRecRaw, by decide⟩

/-- On a `false`-headed argument the `false` branch returns the remaining
bitstring. Arguments of length one do not discriminate the branches: both
readings return the empty bitstring. -/
theorem eval_branchRec_false :
    (BC.eval branchRec).2 ![[false, true]] ![] = [true] := rfl

/-- On a `true`-headed argument the `true` branch recurses. -/
theorem eval_branchRec_true :
    (BC.eval branchRec).2 ![[true, true]] ![] = [] := rfl

/-- The predecessor as a single node. -/
def predTermRaw : sig.toPFunctor.W := WType.mk .pred Fin.elim0

/-- The predecessor, admissible. -/
def predTerm : BC := ⟨predTermRaw, by decide⟩

/-- The predecessor of the empty bitstring is the empty bitstring. -/
theorem eval_predTerm_nil : (BC.eval predTerm).2 ![] ![[]] = [] := rfl

/-- The predecessor drops the low bit. -/
theorem eval_predTerm_cons :
    (BC.eval predTerm).2 ![] ![[true, false]] = [false] := rfl

/-- The conditional as a single node. -/
def condTermRaw : sig.toPFunctor.W := WType.mk .cond Fin.elim0

/-- The conditional, admissible. -/
def condTerm : BC := ⟨condTermRaw, by decide⟩

/-- On the empty bitstring the conditional returns its second safe
argument. -/
theorem eval_condTerm_empty :
    (BC.eval condTerm).2 ![] ![[], [false], [true], [true, true]] = [false] :=
  rfl

/-- On an odd bitstring it returns its third. The authors' Coq development
assigns the third to the odd case and the fourth to the even case; § 3.2
prints them the other way round. -/
theorem eval_condTerm_odd :
    (BC.eval condTerm).2 ![] ![[true], [false], [true], [true, true]] =
      [true] := rfl

/-- On an even bitstring it returns its fourth. -/
theorem eval_condTerm_even :
    (BC.eval condTerm).2 ![] ![[false], [false], [true], [true, true]] =
      [true, true] := rfl

/-- A projection onto a normal variable, as a single node. -/
def projNTermRaw : sig.toPFunctor.W := WType.mk (.proj 1 1 0) Fin.elim0

/-- The normal projection, admissible. -/
def projNTerm : BC := ⟨projNTermRaw, by decide⟩

/-- The normal projection returns the normal argument. -/
theorem eval_projNTerm :
    (BC.eval projNTerm).2 ![[true]] ![[false]] = [true] := rfl

/-- A projection onto a safe variable, as a single node. Together with
`projNTerm` this separates the two halves of `Fin.append`, which a
mistranscribed index would silently permute. -/
def projSTermRaw : sig.toPFunctor.W := WType.mk (.proj 1 1 1) Fin.elim0

/-- The safe projection, admissible. -/
def projSTerm : BC := ⟨projSTermRaw, by decide⟩

/-- The safe projection returns the safe argument. -/
theorem eval_projSTerm :
    (BC.eval projSTerm).2 ![[true]] ![[false]] = [false] := rfl

/-- `plusStepRaw` with its safe argument replaced by an expression of arity
`(2, 0)` where the signature demands `(1, 2)`. -/
def badRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 2 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 2 0 1) Fin.elim0])

/-- The inadmissible tree is rejected, so admissibility is not vacuous. -/
theorem wValid_badRaw_eq_false : decide (sig.WValid badRaw) = false := rfl
