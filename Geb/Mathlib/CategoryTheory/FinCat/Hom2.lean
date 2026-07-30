/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom
public import Mathlib.CategoryTheory.Functor.Category

/-!
# 2-cell specifications

A natural transformation between two functor specifications with the
same source and target is specified by a component at each object
index and a `Bool` equation asserting naturality. The component ranges
over the target's full hom type from the outset, so the identity
2-cell has every component an identity.

## Main definitions

* `FinCat.Hom₂.natCheckOf`, `FinCat.Hom₂.natCheck` — the decidable
  naturality check on client morphisms.
* `FinCat.Hom₂` — the 2-cell specification type.

## Main statements

* `FinCat.Hom₂.natCheck_eq_true_iff` — the check reflects naturality on
  client morphisms.

## Implementation notes

`natCheckOf` precedes the structure because the `natValid` field's type
mentions it. The enclosing `namespace FinCat` stays open throughout;
the inner `namespace Hom₂` block closes before `structure Hom₂`, which
cannot be declared inside a namespace of its own name, and reopens
after.

The check is stated over the total composition and the total morphism
maps, for the reason `FinCat.Hom.compCheckOf` is: a client composite
may land on the reserved identity index, on which the client's
morphism map is undefined.

`FinCat.Hom₂` is not marked `@[ext]`, the one structure in the
workstream that departs from the `@[ext]` reflex. A structure-derived
extensionality lemma does not fire on goals stated through the hom
notation `F ⟶ G`, so it would be unusable at the only place it is
needed; the name `FinCat.Hom₂.ext` is left free for a hand-written
lemma phrased at `F ⟶ G`, matching what mathlib does for
`CategoryTheory.Cat.Hom₂`.

## References

* [JohnsonYau2021] § 1.1 — the notion of natural transformation, of
  which this module's specification type is a presentation.

## Tags

category, functor, natural transformation, finite category, decidable,
constructive, choice-free
-/

@[expose] public section

open CategoryTheory

namespace FinCat

namespace Hom₂

/-- Naturality, as a `Bool`, on client morphisms. Stated over the total
composition and the total morphism maps, for the reason
`FinCat.Hom.compCheckOf` is. -/
def natCheckOf (S T : FinCat) (F G : FinCat.Hom S T)
    (app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)) : Bool :=
  decide <| ∀ (i j : Fin S.objCount) (f : Fin (S.nonIdCount i j)),
    T.compTotal (F.mapTotal (S.emb f)) (app j)
      = T.compTotal (app i) (G.mapTotal (S.emb f))

end Hom₂

/-- A 2-cell specification: a natural transformation between two
functor specifications. -/
structure Hom₂ {S T : FinCat} (F G : FinCat.Hom S T) where
  /-- The component at each object. It ranges over the full hom type
  from the outset, the identity 2-cell having every component an
  identity. -/
  app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)
  /-- Naturality. -/
  natValid : FinCat.Hom₂.natCheckOf S T F G app = true

namespace Hom₂

/-- The naturality check reflects naturality on client morphisms. -/
theorem natCheck_eq_true_iff (S T : FinCat) (F G : FinCat.Hom S T)
    (app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)) :
    natCheckOf S T F G app = true ↔
      ∀ (i j : Fin S.objCount) (f : Fin (S.nonIdCount i j)),
        T.compTotal (F.mapTotal (S.emb f)) (app j)
          = T.compTotal (app i) (G.mapTotal (S.emb f)) :=
  decide_eq_true_iff

/-- `α`'s naturality check. -/
def natCheck {S T : FinCat} {F G : FinCat.Hom S T} (α : FinCat.Hom₂ F G) : Bool :=
  natCheckOf S T F G α.app

end Hom₂

end FinCat
