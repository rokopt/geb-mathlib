/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc

/-!
# Natural transformations between completion maps

Natural transformations between morphism-mapped object maps of free
coproduct completions (`FreeCoprodCompDisc.Map` paired with
`FreeCoprodCompDisc.MapMor`): the naturality condition, the
transformation space as a subtype, and the vertical structure
(identity, composition, and the category laws). Functor-law
predicates and composite maps support the horizontal structure.

## Main definitions

* `FreeCoprodCompDisc.IsNatTrans`, `FreeCoprodCompDisc.NatTrans` —
  the naturality condition and the transformation space.
* `FreeCoprodCompDisc.NatTrans.id`,
  `FreeCoprodCompDisc.NatTrans.vcomp` — the vertical structure.
* `FreeCoprodCompDisc.PreservesId`,
  `FreeCoprodCompDisc.PreservesComp` — functor-law predicates on a
  morphism map.
* `FreeCoprodCompDisc.mapComp`, `FreeCoprodCompDisc.mapMorComp` —
  the composite of two object maps and of their morphism maps.

## Main statements

* `FreeCoprodCompDisc.NatTrans.id_vcomp`,
  `FreeCoprodCompDisc.NatTrans.vcomp_id`,
  `FreeCoprodCompDisc.NatTrans.vcomp_assoc` — the vertical
  category laws.

## Implementation notes

A transformation is a subtype over a `Prop`-valued naturality
condition, so equality of transformations is `Subtype.ext` plus
`funext`, and the vertical laws are componentwise consequences of
the `FreeCoprodCompDisc.Hom` category laws. Morphism maps carry no
functor laws; the operations that need one take the corresponding
`FreeCoprodCompDisc.PreservesId`/`FreeCoprodCompDisc.PreservesComp`
law as an explicit hypothesis.

## Tags

free coproduct completion, natural transformation, functor category
-/

@[expose] public section

universe u v w x

namespace CategoryTheory

namespace FreeCoprodCompDisc

/-- The naturality condition on a family of componentwise morphisms
between two morphism-mapped object maps. -/
def IsNatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
    (mF : MapMor I O F) (mG : MapMor I O G)
    (η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X)) :
    Prop :=
  ∀ (X Y : FreeCoprodCompDisc.{u, v} I) (h : Hom.{u, v, u} I X Y),
    Hom.comp O (mF X Y h) (η Y) = Hom.comp O (η X) (mG X Y h)

/-- A natural transformation between two morphism-mapped object maps:
a componentwise family of morphisms satisfying the naturality
condition. -/
def NatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
    (mF : MapMor I O F) (mG : MapMor I O G) : Type (max (u + 1) v) :=
  {η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X) //
    IsNatTrans I O F G mF mG η}

variable {I : Type v} {O : Type w} {P : Type x}

/-- The identity natural transformation. -/
def NatTrans.id (F : Map.{u, v, w} I O) (mF : MapMor I O F) :
    NatTrans I O F F mF mF :=
  ⟨fun X ↦ Hom.id O (F X),
    fun X Y h ↦
      (Hom.comp_id O (mF X Y h)).trans (Hom.id_comp O (mF X Y h)).symm⟩

/-- Vertical composition of natural transformations. -/
def NatTrans.vcomp {F G H : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} {mH : MapMor I O H}
    (η : NatTrans I O F G mF mG) (θ : NatTrans I O G H mG mH) :
    NatTrans I O F H mF mH :=
  ⟨fun X ↦ Hom.comp O (η.1 X) (θ.1 X),
    fun X Y h ↦
      (Hom.comp_assoc O (mF X Y h) (η.1 Y) (θ.1 Y)).symm.trans
        ((congrArg (fun t ↦ Hom.comp O t (θ.1 Y)) (η.2 X Y h)).trans
          ((Hom.comp_assoc O (η.1 X) (mG X Y h) (θ.1 Y)).trans
            ((congrArg (Hom.comp O (η.1 X)) (θ.2 X Y h)).trans
              (Hom.comp_assoc O (η.1 X) (θ.1 X) (mH X Y h)).symm)))⟩

/-- Vertical left identity. -/
theorem NatTrans.id_vcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
    NatTrans.vcomp (NatTrans.id F mF) η = η :=
  Subtype.ext (funext (fun X ↦ Hom.id_comp O (η.1 X)))

/-- Vertical right identity. -/
theorem NatTrans.vcomp_id {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
    NatTrans.vcomp η (NatTrans.id G mG) = η :=
  Subtype.ext (funext (fun X ↦ Hom.comp_id O (η.1 X)))

/-- Vertical associativity. -/
theorem NatTrans.vcomp_assoc {F G H K : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
    {mK : MapMor I O K} (η : NatTrans I O F G mF mG)
    (θ : NatTrans I O G H mG mH) (ρ : NatTrans I O H K mH mK) :
    NatTrans.vcomp (NatTrans.vcomp η θ) ρ =
      NatTrans.vcomp η (NatTrans.vcomp θ ρ) :=
  Subtype.ext (funext (fun X ↦ Hom.comp_assoc O (η.1 X) (θ.1 X) (ρ.1 X)))

/-- Preservation of identities by a morphism map. -/
def PreservesId (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
  ∀ X : FreeCoprodCompDisc.{u, v} I,
    mF X X (Hom.id I X) = Hom.id O (F X)

/-- Preservation of composition by a morphism map. -/
def PreservesComp (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
  ∀ (X Y Z : FreeCoprodCompDisc.{u, v} I) (f : Hom I X Y) (g : Hom I Y Z),
    mF X Z (Hom.comp I f g) = Hom.comp O (mF X Y f) (mF Y Z g)

/-- The composite of two object maps. -/
def mapComp (F : Map.{u, v, w} I O) (F' : Map.{u, w, x} O P) :
    Map.{u, v, x} I P :=
  fun X ↦ F' (F X)

/-- The composite of two morphism maps, over the composite object
map. -/
def mapMorComp {F : Map.{u, v, w} I O} {F' : Map.{u, w, x} O P}
    (mF : MapMor I O F) (mF' : MapMor O P F') :
    MapMor I P (mapComp F F') :=
  fun X Y h ↦ mF' (F X) (F Y) (mF X Y h)

end FreeCoprodCompDisc

end CategoryTheory
