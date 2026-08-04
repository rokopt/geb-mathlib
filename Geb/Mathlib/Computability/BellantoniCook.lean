/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The function class `B` of Bellantoni and Cook

The syntax of the function class `B` and its interpretation, following
[HeraudNowak2011] § 3.2. Terms of `B` are built from a constant zero,
projections, two successors, a predecessor and a conditional, and are closed
under a composition and a recursion that distinguish normal from safe
argument positions; the distinction is what bounds the growth rate of the
definable functions.

The class defined here is the reformulation of § 3.2, not the class of
[BellantoniCook1992]. Two differences: the conditional takes four safe
arguments and branches three ways, on the empty, odd and even bitstrings,
where the original branches two ways on parity and treats the empty
bitstring as even; and the base case of the recursion is the empty
bitstring, where the original's is every bitstring denoting zero.

The two sources transpose the conditional's last two safe arguments. The
order here follows the authors' Coq development, that being the artifact
against which the paper's theorems were machine-checked.

## Main definitions

* `BellantoniCook.Shape` — the seven constructor forms, with their arities
  as parameters.
* `BellantoniCook.Direction` — the subterm positions of a shape.
* `BellantoniCook.rc` — the arity each subterm position must carry.
* `BellantoniCook.q` — the arity a shape produces.
* `BellantoniCook.sig` — the signature, as a slice polynomial functor over
  `ℕ × ℕ`.
* `BellantoniCook.BC` — an expression of `B`: a `sig`-tree whose every node
  respects `rc`.
* `BellantoniCook.BC.arity` — its pair of normal and safe arities.
* `BellantoniCook.BCOf` — the expressions of a given arity pair.
* `BellantoniCook.Sem` — the meaning of an arity pair: a function of a
  normal and a safe environment.
* `BellantoniCook.transport` — transport of a meaning along an equality of
  arity pairs.
* `BellantoniCook.evalRec` — the recursion on the consumed bitstring.
* `BellantoniCook.evalValue` — the meaning of one node from its children's.
* `BellantoniCook.evalStep` — `evalValue` as a slice algebra.
* `BellantoniCook.BC.eval` — the interpretation, by the slice W-type's
  eliminator.

## Implementation notes

This repository expresses all recursion through recursors, admitting
neither a self-referential `inductive` nor a self-calling `def`, so the
arity-indexed syntax is the slice W-type of `sig` and the interpretation is
one application of `SlicePFunctor.W.elim`. `Shape` is itself non-recursive
and so is the shape set of a `PFunctor`, not a datatype the rule reaches.

`evalValue` is separate from `evalStep` because the match on `Shape` must
generalize the compatibility hypothesis, which arrives bundled in
`SliceDomPFunctor.Obj`. A child's meaning carries the index it was built at
rather than the index `rc` prescribes, equal but not definitionally so;
`transport` carries it across, with the motive of `▸` fixed once instead of
at each of the six sites.

`Direction`, `rc` and `q` are `@[reducible]`. Instance search does not
delta-reduce a semireducible definition, and every numeral in `evalValue`
elaborates against `Fin (q a).1` or `Direction a`.

`finEnumFin` and `finEnumCompDirection` are `scoped`, and hand-built:
mathlib's `FinEnum` instances depend on `Classical.choice`, which
`lake lint` rejects, and an unscoped instance at the head symbol `FinEnum
(Fin _)` would compete with `FinEnum.fin` wherever `Geb` is imported.

## References

* [HeraudNowak2011]
* [BellantoniCook1992]

## Tags

Bellantoni-Cook, polytime, implicit computational complexity, safe
recursion, W-type, polynomial functor
-/

namespace BellantoniCook

public section

/-- The seven constructor forms of `B`, each carrying its arities as
parameters: `zero` the constant empty bitstring; `proj n s i` the `i`th of
`n` normal and `s` safe variables; `succ b` the successor appending the bit
`b`; `pred` the predecessor; `cond` the four-argument conditional;
`safeRec n s` the recursion producing arity `(n + 1, s)`; and `comp n s m k`
the composition of an expression of arity `(m, k)` with `m` normal and `k`
safe argument expressions of arity `(n, 0)` and `(n, s)`. -/
inductive Shape
  | zero
  | proj (n s : ℕ) (i : Fin (n + s))
  | succ (b : Bool)
  | pred
  | cond
  | safeRec (n s : ℕ)
  | comp (n s m k : ℕ)

/-- The subterm positions of a shape. The five base forms have none;
`safeRec` has three, its base and its two step expressions; `comp` has its
head, its `m` normal arguments and its `k` safe arguments. -/
@[expose, reducible] def Direction : Shape → Type
  | .zero => Fin 0
  | .proj _ _ _ => Fin 0
  | .succ _ => Fin 0
  | .pred => Fin 0
  | .cond => Fin 0
  | .safeRec _ _ => Fin 3
  | .comp _ _ m k => Unit ⊕ Fin m ⊕ Fin k

/-- The arity each subterm position must carry: the hypotheses of the
arity relation of [HeraudNowak2011] § 3.2. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ × ℕ
  | .zero, i => i.elim0
  | .proj _ _ _, i => i.elim0
  | .succ _, i => i.elim0
  | .pred, i => i.elim0
  | .cond, i => i.elim0
  | .safeRec n s, ⟨0, _⟩ => (n, s)
  | .safeRec n s, _ => (n + 1, s + 1)
  | .comp _ _ m k, .inl () => (m, k)
  | .comp n _ _ _, .inr (.inl _) => (n, 0)
  | .comp n s _ _, .inr (.inr _) => (n, s)

/-- The arity a shape produces: the conclusions of the arity relation of
[HeraudNowak2011] § 3.2. -/
@[expose, reducible] def q : Shape → ℕ × ℕ
  | .zero => (0, 0)
  | .proj n s _ => (n, s)
  | .succ _ => (0, 1)
  | .pred => (0, 1)
  | .cond => (0, 4)
  | .safeRec n s => (n + 1, s)
  | .comp n s _ _ => (n, s)

/-- The signature of `B` as a slice polynomial functor over `ℕ × ℕ`, the
index being the pair of normal and safe arities. -/
@[expose] def sig : SlicePFunctor (ℕ × ℕ) (ℕ × ℕ) where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

/-- A choice-free `FinEnum (Fin n)`: the cardinality is `n` and the
enumeration is the identity. `scoped`, so that it does not compete with
mathlib's `FinEnum.fin` at the same head symbol outside this namespace. -/
scoped instance finEnumFin (n : ℕ) :
    FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _
  decEq := inferInstance

/-- A choice-free `FinEnum` for `comp`'s directions. `scoped`, for the same
reason as `finEnumFin`. -/
scoped instance finEnumCompDirection (m k : ℕ) :
    FinEnum (Unit ⊕ Fin m ⊕ Fin k) where
  card := 1 + (m + k)
  equiv := (Equiv.sumCongr finOneEquiv.symm finSumFinEquiv).trans finSumFinEquiv
  decEq := inferInstance

/-- Every shape has finitely many directions, which is what makes
admissibility of a `sig`-tree decidable. The branches ascribe their
instances explicitly: instance search stops at reducible transparency on the
projection `sig.B a`, so a bare `inferInstance` does not find them. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .zero => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .pred => inferInstanceAs (FinEnum (Fin 0))
  | .cond => inferInstanceAs (FinEnum (Fin 0))
  | .safeRec _ _ => inferInstanceAs (FinEnum (Fin 3))
  | .comp _ _ m k => inferInstanceAs (FinEnum (Unit ⊕ Fin m ⊕ Fin k))

end

end BellantoniCook
