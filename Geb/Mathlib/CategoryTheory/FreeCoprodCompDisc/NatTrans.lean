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
* `FreeCoprodCompDisc.NatTrans.whiskerRight`,
  `FreeCoprodCompDisc.NatTrans.whiskerLeft`,
  `FreeCoprodCompDisc.NatTrans.hcomp` — whiskering and horizontal
  composition.
* `FreeCoprodCompDisc.idMap`, `FreeCoprodCompDisc.idMapMor` — the
  identity object map and its morphism-map component.

## Main statements

* `FreeCoprodCompDisc.NatTrans.id_vcomp`,
  `FreeCoprodCompDisc.NatTrans.vcomp_id`,
  `FreeCoprodCompDisc.NatTrans.vcomp_assoc` — the vertical
  category laws.
* `FreeCoprodCompDisc.NatTrans.hcomp_eq_vcomp_whisker`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id_right`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id_left`,
  `FreeCoprodCompDisc.NatTrans.hcomp_vcomp` — the coherence and
  interchange laws of horizontal composition.
* `FreeCoprodCompDisc.NatTrans.whiskerRight_idMap`,
  `FreeCoprodCompDisc.NatTrans.whiskerLeft_idMap` — whiskering by
  the identity object map is the identity operation (with the
  functor-law witnesses `FreeCoprodCompDisc.idMapMor_preservesId`
  and `FreeCoprodCompDisc.idMapMor_preservesComp`).

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

/-- Right whiskering: precomposition of a transformation with an
object map (no functor-law hypotheses). -/
def NatTrans.whiskerRight {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'} (F : Map.{u, v, w} I O)
    (mF : MapMor I O F) (θ : NatTrans O P F' G' mF' mG') :
    NatTrans I P (mapComp F F') (mapComp F G')
      (mapMorComp mF mF') (mapMorComp mF mG') :=
  ⟨fun X ↦ θ.1 (F X), fun X Y h ↦ θ.2 (F X) (F Y) (mF X Y h)⟩

/-- Left whiskering: postcomposition of a transformation with an
object map, whose naturality consumes the outer morphism map's
composition-preservation law. -/
def NatTrans.whiskerLeft {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG)
    (F' : Map.{u, w, x} O P) (mF' : MapMor O P F')
    (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G F')
      (mapMorComp mF mF') (mapMorComp mG mF') :=
  ⟨fun X ↦ mF' (F X) (G X) (η.1 X),
    fun X Y h ↦
      (hF' (F X) (F Y) (G Y) (mF X Y h) (η.1 Y)).symm.trans
        ((congrArg (mF' (F X) (G Y)) (η.2 X Y h)).trans
          (hF' (F X) (G X) (G Y) (η.1 X) (mG X Y h)))⟩

/-- Horizontal composition of natural transformations, in the
`whiskerLeft`-then-`whiskerRight` orientation. -/
def NatTrans.hcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
    (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G G')
      (mapMorComp mF mF') (mapMorComp mG mG') :=
  NatTrans.vcomp (NatTrans.whiskerLeft η F' mF' hF')
    (NatTrans.whiskerRight G mG θ)

/-- The two orientations of the horizontal composite agree, by the
second transformation's naturality. -/
theorem NatTrans.hcomp_eq_vcomp_whisker {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
    (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
    NatTrans.hcomp η θ hF' =
      NatTrans.vcomp (NatTrans.whiskerRight F mF θ)
        (NatTrans.whiskerLeft η G' mG' hG') :=
  Subtype.ext (funext (fun X ↦ θ.2 (F X) (G X) (η.1 X)))

/-- The horizontal composite of identity transformations is the
identity (consuming the outer morphism map's identity-preservation
law). -/
theorem NatTrans.hcomp_id {F : Map.{u, v, w} I O} {mF : MapMor I O F}
    {F' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
    (hF'comp : PreservesComp F' mF') (hF'id : PreservesId F' mF') :
    NatTrans.hcomp (NatTrans.id F mF) (NatTrans.id F' mF') hF'comp =
      NatTrans.id (mapComp F F') (mapMorComp mF mF') :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t (Hom.id P (F' (F X))))
        (hF'id (F X))).trans
      (Hom.comp_id P (Hom.id P (F' (F X))))))

/-- Whiskering by an identity-transformation on the right is left
whiskering. -/
theorem NatTrans.hcomp_id_right {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {F' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} (η : NatTrans I O F G mF mG)
    (hF' : PreservesComp F' mF') :
    NatTrans.hcomp η (NatTrans.id F' mF') hF' =
      NatTrans.whiskerLeft η F' mF' hF' :=
  Subtype.ext (funext (fun X ↦ Hom.comp_id P (mF' (F X) (G X) (η.1 X))))

/-- Whiskering by an identity-transformation on the left is right
whiskering. -/
theorem NatTrans.hcomp_id_left {F : Map.{u, v, w} I O}
    {mF : MapMor I O F} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (θ : NatTrans O P F' G' mF' mG') (hF'comp : PreservesComp F' mF')
    (hF'id : PreservesId F' mF') :
    NatTrans.hcomp (NatTrans.id F mF) θ hF'comp =
      NatTrans.whiskerRight F mF θ :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t (θ.1 (F X))) (hF'id (F X))).trans
      (Hom.id_comp P (θ.1 (F X)))))

/-- The identity object map. -/
def idMap : Map.{u, v, v} I I :=
  fun X ↦ X

/-- The morphism-map component of the identity object map. -/
def idMapMor : MapMor I I (idMap : Map.{u, v, v} I I) :=
  fun _ _ h ↦ h

/-- The identity object map preserves identities. -/
theorem idMapMor_preservesId :
    PreservesId (idMap : Map.{u, v, v} I I) idMapMor :=
  fun _ ↦ rfl

/-- The identity object map preserves composition. -/
theorem idMapMor_preservesComp :
    PreservesComp (idMap : Map.{u, v, v} I I) idMapMor :=
  fun _ _ _ _ _ ↦ rfl

/-- Whiskering a transformation with the identity object map on the
precomposition side is the identity operation. -/
theorem NatTrans.whiskerRight_idMap {F' G' : Map.{u, v, w} I O}
    {mF' : MapMor I O F'} {mG' : MapMor I O G'}
    (θ : NatTrans I O F' G' mF' mG') :
    NatTrans.whiskerRight (idMap : Map.{u, v, v} I I) idMapMor θ = θ :=
  Subtype.ext rfl

/-- Whiskering a transformation with the identity object map on the
postcomposition side is the identity operation. -/
theorem NatTrans.whiskerLeft_idMap {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (η : NatTrans I O F G mF mG) :
    NatTrans.whiskerLeft η (idMap : Map.{u, w, w} O O) idMapMor
      idMapMor_preservesComp = η :=
  Subtype.ext rfl

/-- The interchange law between horizontal and vertical composition. -/
theorem NatTrans.hcomp_vcomp {F G H : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
    {F' G' H' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
    {mG' : MapMor O P G'} {mH' : MapMor O P H'}
    (η : NatTrans I O F G mF mG) (η' : NatTrans I O G H mG mH)
    (θ : NatTrans O P F' G' mF' mG') (θ' : NatTrans O P G' H' mG' mH')
    (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
    NatTrans.hcomp (NatTrans.vcomp η η') (NatTrans.vcomp θ θ') hF' =
      NatTrans.vcomp (NatTrans.hcomp η θ hF')
        (NatTrans.hcomp η' θ' hG') :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t
        (Hom.comp P (θ.1 (H X)) (θ'.1 (H X))))
      (hF' (F X) (G X) (H X) (η.1 X) (η'.1 X))).trans
    (congrArg (fun t ↦
        Hom.comp P (Hom.comp P (mF' (F X) (G X) (η.1 X)) t)
          (θ'.1 (H X)))
      (θ.2 (G X) (H X) (η'.1 X)))))

end FreeCoprodCompDisc

end CategoryTheory
