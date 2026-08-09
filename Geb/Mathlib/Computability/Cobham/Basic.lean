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
recursion scheme is bounded recursion on notation [Cobham1965], together with its
interpretation over every `sig`-tree. Terms are built from a constant zero,
projections, two successors, a smash and a concat generator, and are closed under a
composition and a bounded recursion. `sig` fixes the shape of the syntax alone — each
constructor's arity and the arity relation its subterms must satisfy — and `eval`
gives the meaning of any tree respecting that relation; the admissible terms, those
whose recursions additionally respect a length bound, are left to where the module's
contents are complete.

## Main definitions

* `Cobham.Shape` — the seven constructor forms, with their arities as parameters.
* `Cobham.Direction` — the subterm positions of a shape.
* `Cobham.rc` — the arity each subterm position must carry.
* `Cobham.q` — the arity a shape produces.
* `Cobham.sig` — the signature, as a slice polynomial functor over `ℕ`.
* `Cobham.sigFinitary` — every shape has finitely many directions.
* `Cobham.Sem` — the meaning of an arity: a function of an environment of bitstrings.
* `Cobham.transport` — transport of a meaning along an equality of arities.
* `Cobham.evalRec` — the recursion `boundedRec` performs on its recursion variable.
* `Cobham.evalValue` — the meaning of one node from its children's meanings.
* `Cobham.evalStep` — `evalValue` as a slice algebra.
* `Cobham.eval` — the interpretation of a `sig`-tree, by the slice W-type's
  eliminator.
* `Cobham.arity` — the arity of a `sig`-tree.

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

A bitstring is represented as a `List Bool` whose head is the word's last bit, so
`succ b` prepends by consing `b`. `evalValue` is a separate definition from
`evalStep` because the match on `Shape` must generalize the compatibility hypothesis,
which arrives bundled in `SliceDomPFunctor.Obj`. A child's meaning carries the index
it was built at rather than the index `rc` prescribes, equal but not definitionally
so; `transport` carries it across, with the motive of `▸` fixed once instead of at
each use site. `evalValue`'s `boundedRec` clause does not consult its bound child's
meaning: the bound is a side condition on admissibility, introduced where the
admissible terms are, not part of a tree's value.

## References

* [Cobham1965]
* [HeraudNowak2011]
* [Strahm2003]

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

/-- The meaning of an arity: a function of an environment of bitstrings, one per
argument, returning a bitstring. -/
@[expose] def Sem : ℕ → Type := fun n ↦ (Fin n → List Bool) → List Bool

/-- Transport of a meaning along an equality of arities. Named so that the motive of
`▸` is fixed once rather than inferred at each use in `evalValue`. -/
@[expose] def transport {i j : ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v

/-- The recursion `boundedRec` performs on its recursion variable, by `List.rec`,
matching [HeraudNowak2011]'s `Rec` (`f(y·i, x) = h_i(y, f(y,x), x)`), not
[Strahm2003]'s last-argument form. The base case is the empty bitstring; a step
consumes the low bit `b`, passes the remaining bitstring `v` as the new recursion
variable, and passes the recursive value alongside it. -/
@[expose] def evalRec {n : ℕ} (g : Sem n) (h₀ h₁ : Sem (n + 2)) :
    List Bool → Sem n :=
  List.rec g (fun b v ih x ↦
    (if b then h₁ else h₀) (Fin.cons v (Fin.cons (ih x) x)))

/-- The meaning of one node, from its children's meanings and the proof that each
child's index is the one `rc` prescribes. A separate definition from `evalStep`
because the match on `Shape` must generalize that proof.

The bitstring generators read the ambient environment directly, `Direction` being
`Fin 0` for each: `zero` returns the empty bitstring; `proj n i` returns the `i`th
argument; `succ b` prepends `b` to the argument. `smash` and `concat` are Cobham's
two generators: `smash` marks its result with a leading `true`, so
`|#(a, b)| = |a| · |b| + 1`; `concat` reads its second argument as the earlier part
of the word and its first as the later part, consistent with the list head
representing the word's last bit. `comp` applies its head's meaning to the argument
expressions' meanings, each read at the ambient environment. `boundedRec` performs
`evalRec` on its recursion variable, its base and two step children supplying `g`,
`h₀` and `h₁`. -/
@[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .zero, _, _ => fun _ ↦ []
  | .proj _ i, _, _ => fun x ↦ x i
  | .succ b, _, _ => fun x ↦ b :: x 0
  | .smash, _, _ => fun x ↦ true :: List.replicate ((x 0).length * (x 1).length) false
  | .concat, _, _ => fun x ↦ x 1 ++ x 0
  | .comp _ _, c, h => fun x ↦
      transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x)
  | .boundedRec _, c, h => fun x ↦
      evalRec (transport (h 0) (c 0).2) (transport (h 1) (c 1).2)
        (transport (h 2) (c 2).2) (x 0) (Fin.tail x)

/-- `evalValue` as an algebra for `sig` in the slice over `ℕ`. Returning the shape's
own output index as the first component makes the eliminator's coherence obligation
hold by `rfl`. -/
@[expose] def evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The interpretation of a `sig`-tree: its arity together with its meaning at that
arity, by the slice W-type's eliminator. -/
@[expose] def eval : sig.W → Σ n, Sem n :=
  SlicePFunctor.W.elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl

/-- The arity of a `sig`-tree. -/
@[expose] def arity : sig.W → ℕ := sig.wIndex

end

end Cobham
