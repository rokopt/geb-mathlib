/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable -- shake: keep
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The signature of Cobham's class of bitstring functions

The syntactic signature of a Cobham-style function algebra on bitstrings, whose
recursion scheme is bounded recursion on notation [Cobham1965]. Terms are built from
a constant zero, projections, two successors, a smash and a concat generator, and are
closed under a composition and a bounded recursion. This module fixes the shape of the
syntax alone — each constructor's arity and the arity relation its subterms must
satisfy, as the polynomial functor `sig` — leaving the terms themselves and their
interpretation to where the module's contents are complete.

## Main definitions

* `Cobham.Shape` — the seven constructor forms, with their arities as parameters.
* `Cobham.Direction` — the subterm positions of a shape.
* `Cobham.rc` — the arity each subterm position must carry.
* `Cobham.q` — the arity a shape produces.
* `Cobham.sig` — the signature, as a slice polynomial functor over `ℕ`.
* `Cobham.sigFinitary` — every shape has finitely many directions.

## Implementation notes

`SlicePFunctor.decidableWValid` is imported for a later task that commits the first
`⟨_, by decide⟩` term against `sig`; this module commits none and so does not
reference it, but importing it here avoids adding an import mid-module.

`Direction`, `rc` and `q` are `@[reducible]`. Instance search does not delta-reduce a
semireducible definition, and `sigFinitary` resolves `FinEnum (sig.B a)` against the
literal `Direction a` each branch produces.

`sigFinitary`'s `comp` branch resolves `FinEnum (Unit ⊕ Fin m)` through the
choice-free `FinEnum.unit` and `FinEnum.finSum`, and its other branches resolve
`FinEnum (Fin n)` through the choice-free `FinEnum.finFin`. Those instances are
`scoped` in `namespace FinEnum`; this module's `open scoped FinEnum` is required for
them to win resolution over mathlib's `Classical.choice`-dependent counterparts,
which `lake lint` rejects.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, W-type, polynomial functor
-/

namespace Cobham

open scoped FinEnum

public section

/-- The seven constructor forms of Cobham's class, each carrying its arities as
parameters: `zero` the constant empty bitstring; `proj n i` the `i`th of `n`
variables; `succ b` the successor appending the bit `b`; `smash` and `concat` the two
bitstring generators; `comp n m` the composition of an `m`-ary expression with `m`
`n`-ary argument expressions; `boundedRec n` the bounded recursion producing arity
`n + 1`. -/
inductive Shape
  | zero
  | proj (n : ℕ) (i : Fin n)
  | succ (b : Bool)
  | smash
  | concat
  | comp (n m : ℕ)
  | boundedRec (n : ℕ)

/-- The subterm positions of a shape. The five base forms — `zero`, `proj`, `succ`,
`smash` and `concat` — have none, `smash` and `concat` being generators rather than
recursive constructions; `comp` has its head and its `m` argument expressions;
`boundedRec` has four, its base, its two step expressions and its bound. -/
@[expose, reducible] def Direction : Shape → Type
  | .zero => Fin 0
  | .proj _ _ => Fin 0
  | .succ _ => Fin 0
  | .smash => Fin 0
  | .concat => Fin 0
  | .comp _ m => Unit ⊕ Fin m
  | .boundedRec _ => Fin 4

/-- The arity each subterm position must carry: the hypotheses of the arity relation
of bounded recursion on notation [Cobham1965]. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ
  | .zero, i => i.elim0
  | .proj _ _, i => i.elim0
  | .succ _, i => i.elim0
  | .smash, i => i.elim0
  | .concat, i => i.elim0
  | .comp _ m, .inl () => m
  | .comp n _, .inr _ => n
  | .boundedRec n, ⟨0, _⟩ => n
  | .boundedRec n, ⟨1, _⟩ => n + 2
  | .boundedRec n, ⟨2, _⟩ => n + 2
  | .boundedRec n, _ => n + 1

/-- The arity a shape produces: the conclusions of the arity relation of bounded
recursion on notation [Cobham1965]. -/
@[expose, reducible] def q : Shape → ℕ
  | .zero => 0
  | .proj n _ => n
  | .succ _ => 1
  | .smash => 2
  | .concat => 2
  | .comp n _ => n
  | .boundedRec n => n + 1

/-- The signature of Cobham's class as a slice polynomial functor over `ℕ`, the index
being the arity. -/
@[expose] def sig : SlicePFunctor ℕ ℕ where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

/-- Every shape has finitely many directions, which is what makes admissibility of a
`sig`-tree decidable. The branches ascribe their instances explicitly: instance
search stops at reducible transparency on the projection `sig.B a`, so a bare
`inferInstance` does not find them. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .zero => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .smash => inferInstanceAs (FinEnum (Fin 0))
  | .concat => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ m => inferInstanceAs (FinEnum (Unit ⊕ Fin m))
  | .boundedRec _ => inferInstanceAs (FinEnum (Fin 4))

end

end Cobham
