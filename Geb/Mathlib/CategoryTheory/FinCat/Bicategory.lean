/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Whiskering of 2-cell specifications

Whiskering a 2-cell specification by a 1-cell specification on either
side. Left whiskering reindexes the components along the inner 1-cell's
object map; right whiskering applies the outer 1-cell's total morphism
map to each component.

## Main definitions

* `FinCat.Hom₂.whiskerLeft`, `FinCat.Hom₂.whiskerRight` — the two
  whiskerings.

## Main statements

* `FinCat.Hom₂.eqToHom_app` — the components of `CategoryTheory.eqToHom`
  at an equality of 1-cell specifications.

## Implementation notes

The whiskerings' result types are written with `⟶` at the 2-cell level,
which resolves through `FinCat.Hom.instCategory`, and with
`FinCat.Hom.comp` for the 1-cell composite. The 1-cell composite cannot
be written `≫`: that notation needs a `CategoryTheory.CategoryStruct`
on `FinCat`, which does not yet exist.

`FinCat.Hom.comp_mapTotal` is what both naturality checks open with: the
composite specification's total map and the composite of the two total
maps dispatch on different `Nat.decLt` instances and are not
definitionally equal.

Left whiskering's check reduces to the inner 2-cell's naturality at
`F.mapTotal (S.emb f)`, which `FinCat.Hom.mapTotal_emb` identifies with
`F.map i j f` — a value of the full hom type rather than an embedded
client morphism, a 1-cell specification being free to send a client
morphism to a reserved identity. It therefore needs
`FinCat.Hom₂.natCheck_total`, the extension of the check off the client
range, rather than `FinCat.Hom₂.natCheck_eq_true_iff` alone.

## References

* [JohnsonYau2021] § 2.1 — the notion of bicategory, of which the
  whiskerings are part of the data.
* [JohnsonYau2021] § 2.3 — 2-categories, Definition 2.3.1, the strict
  case.

## Tags

category, functor, natural transformation, bicategory, 2-category,
whiskering, finite category, decidable, constructive, choice-free
-/

@[expose] public section

open CategoryTheory

namespace FinCat

namespace Hom₂

/-- Left whiskering: pure reindexing. -/
def whiskerLeft {S T U : FinCat} (F : FinCat.Hom S T) {G H : FinCat.Hom T U}
    (η : G ⟶ H) : F.comp G ⟶ F.comp H where
  app i := η.app (F.objMap i)
  natValid := by
    refine (natCheck_eq_true_iff S U (F.comp G) (F.comp H) _).mpr ?_
    intro i j f
    rw [Hom.comp_mapTotal, Hom.comp_mapTotal]
    exact natCheck_total η (F.mapTotal (S.emb f))

/-- Right whiskering: application of the outer 1-cell's total map. -/
def whiskerRight {S T U : FinCat} {F G : FinCat.Hom S T} (η : F ⟶ G)
    (H : FinCat.Hom T U) : F.comp H ⟶ G.comp H where
  app i := H.mapTotal (η.app i)
  natValid := by
    refine (natCheck_eq_true_iff S U (F.comp H) (G.comp H) _).mpr ?_
    intro i j f
    have h := congrArg H.mapTotal ((natCheck_eq_true_iff S T F G η.app).mp η.natValid i j f)
    rw [H.mapTotal_compTotal, H.mapTotal_compTotal] at h
    rw [Hom.comp_mapTotal, Hom.comp_mapTotal]
    exact h

/-- The components of `eqToHom` at an equality of 1-cells. It cannot be
stated as `(eqToHom p).app i = T.id (F.objMap i)`: `app`'s type
mentions both `F.objMap` and `G.objMap`, so the two sides would have
different types. -/
theorem eqToHom_app {S T : FinCat} {F G : FinCat.Hom S T} (p : F = G) (i : Fin S.objCount) :
    (eqToHom p : F ⟶ G).app i
      = Fin.cast (congrArg (fun H ↦ T.homCount (F.objMap i) (H.objMap i)) p)
          (T.id (F.objMap i)) := by cases p; rfl

end Hom₂

end FinCat
