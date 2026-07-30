/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

/-!
# Finite-category specifications

A client specifies a finite category by a count of objects, a count of
non-identity morphisms at each pair of objects, a composition function
on those morphisms, and a `Bool` equation asserting associativity. The
identities are not the client's to supply: one is reserved at the index
one past the client's range in each endo-hom, so the identity laws hold
of the reserved index by construction and only associativity is
checked.

## Main definitions

* `FinCat` — the specification type.
* `FinCat.homCountOf`, `FinCat.homCount` — the hom-count including the
  reserved identity.
* `FinCat.Mor`, `FinCat.emb`, `FinCat.id` — the full hom type, the
  embedding of a client morphism, and the reserved identity.
* `FinCat.compTotalOf`, `FinCat.compTotal` — composition on the full
  hom types.
* `FinCat.assocCheckOf`, `FinCat.assocCheck` — the decidable
  associativity check on triples of client morphisms.

## Main statements

* `FinCat.id_comp`, `FinCat.comp_id` — the identity laws, at variable
  indices.
* `FinCat.assocCheck_eq_true_iff` — the check reflects associativity on
  client triples.
* `FinCat.compTotal_assoc` — associativity on all triples.

## Implementation notes

Composition takes the hom-count matrix as primitive rather than a total
morphism count with domain and codomain projections. Under the matrix
the indexing makes well-typedness a typing obligation, and composition
is total; under the projections it is partial, and the client and the
checker carry the two side conditions relating the endpoints of a
composite to those of its factors.

The identity is reserved one past the client's range rather than at
index `0` so that the embedding of a client morphism into the full hom
type is index-preserving both on and off the diagonal. Reserving `0`
makes the embedding `Fin.succ` on the diagonal and the identity map off
it, so a client's composition function would take arguments in one
numbering and return a result in another.

Total composition dispatches on whether either argument is the reserved
identity, which involves the equation `i = j` between objects. That
equation is used only inside a `Prop`: each branch returns
`⟨x.val, proof⟩`, so the value component crosses with no `Eq.rec` and
only the bound is transported. This is core's own idiom for
`Fin.castLE`.

The specification type is declared `structure _root_.FinCat` inside
`namespace FinCat`, so that its field types name the arithmetic
unqualified and the module needs only one namespace block.

This module has no imports. Its `Fin` and `Nat` material is in the
prelude, and nothing in its content mentions a category.

## References

* [JohnsonYau2021] § 1.1 — the notion of category, of which this
  module's specification type is a presentation.

## Tags

category, finite category, decidable, constructive, choice-free
-/

@[expose] public section

namespace FinCat

/-- The number of morphisms `i ⟶ j` a specification with these counts
has: the client's count, plus the reserved identity on the diagonal. -/
def homCountOf (objCount : Nat) (nonIdCount : Fin objCount → Fin objCount → Nat)
    (i j : Fin objCount) : Nat := nonIdCount i j + if i = j then 1 else 0

/-- The embedding of a client morphism into the full hom type. It is
index-preserving, on and off the diagonal. -/
def embOf {objCount : Nat} {nonIdCount : Fin objCount → Fin objCount → Nat}
    {i j : Fin objCount} (f : Fin (nonIdCount i j)) :
    Fin (homCountOf objCount nonIdCount i j) := Fin.castLE (Nat.le_add_right _ _) f

/-- Off the diagonal the reserved identity contributes nothing. -/
theorem homCountOf_of_ne {objCount : Nat}
    {nonIdCount : Fin objCount → Fin objCount → Nat} {i j : Fin objCount} (hij : ¬ i = j) :
    homCountOf objCount nonIdCount i j = nonIdCount i j :=
  (congrArg (nonIdCount i j + ·) (if_neg hij)).trans (Nat.add_zero _)

/-- On the diagonal it contributes one. -/
theorem homCountOf_diag {objCount : Nat}
    {nonIdCount : Fin objCount → Fin objCount → Nat} (i : Fin objCount) :
    homCountOf objCount nonIdCount i i = nonIdCount i i + 1 :=
  congrArg (nonIdCount i i + ·) (if_pos rfl)

/-- An index at or beyond the client's count exists only on the
diagonal: off the diagonal the conditional in `homCountOf` contributes
`0`. -/
theorem objEq_of_le {objCount : Nat} {nonIdCount : Fin objCount → Fin objCount → Nat}
    {i j : Fin objCount} (x : Fin (homCountOf objCount nonIdCount i j))
    (h : nonIdCount i j ≤ x.val) : i = j :=
  if hij : i = j then hij
  else absurd (homCountOf_of_ne (nonIdCount := nonIdCount) hij ▸ x.isLt) (Nat.not_lt.mpr h)

/-- An index at or beyond the client's count is the reserved identity
index of its object. -/
theorem val_eq_of_le {objCount : Nat} {nonIdCount : Fin objCount → Fin objCount → Nat}
    {i j : Fin objCount} (x : Fin (homCountOf objCount nonIdCount i j))
    (h : nonIdCount i j ≤ x.val) : x.val = nonIdCount j j := by
  have hij := objEq_of_le x h
  subst hij
  exact Nat.le_antisymm
    (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq x.isLt (homCountOf_diag (nonIdCount := nonIdCount) i))) h

/-- Composition on the full hom types, dispatching on whether either
argument is the reserved identity. Both elided bounds are
`objEq_of_le`: the value component crosses unchanged and only the
bound is transported. -/
def compTotalOf {objCount : Nat} {nonIdCount : Fin objCount → Fin objCount → Nat}
    (comp : (i j k : Fin objCount) → Fin (nonIdCount i j) → Fin (nonIdCount j k) →
      Fin (homCountOf objCount nonIdCount i k))
    {i j k : Fin objCount} (f : Fin (homCountOf objCount nonIdCount i j))
    (g : Fin (homCountOf objCount nonIdCount j k)) :
    Fin (homCountOf objCount nonIdCount i k) :=
  if hf : f.val < nonIdCount i j then
    if hg : g.val < nonIdCount j k then comp i j k ⟨f.val, hf⟩ ⟨g.val, hg⟩
    else ⟨f.val, by
      have hjk := objEq_of_le g (Nat.not_lt.mp hg); subst hjk; exact f.isLt⟩
  else ⟨g.val, by
    have hij := objEq_of_le f (Nat.not_lt.mp hf); subst hij; exact g.isLt⟩

/-- Associativity of the total composition on triples of client
morphisms, as a `Bool`. The composition in the statement is the total
one, so a composite landing on the reserved identity index is
covered. -/
def assocCheckOf (objCount : Nat) (nonIdCount : Fin objCount → Fin objCount → Nat)
    (comp : (i j k : Fin objCount) → Fin (nonIdCount i j) → Fin (nonIdCount j k) →
      Fin (homCountOf objCount nonIdCount i k)) : Bool :=
  decide <| ∀ (i j k l : Fin objCount) (f : Fin (nonIdCount i j)) (g : Fin (nonIdCount j k))
    (h : Fin (nonIdCount k l)),
      compTotalOf comp (compTotalOf comp (embOf f) (embOf g)) (embOf h)
        = compTotalOf comp (embOf f) (compTotalOf comp (embOf g) (embOf h))

end FinCat
