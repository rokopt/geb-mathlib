/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos
import Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Tests for `ElementaryTopos FinSetSkel`

Four assertions that the instance makes the classes it alone supplies
resolve, seven that each of its fields is the term assigned to it, and one
worked finite colimit at a shape neither the binary coproducts nor the
coequalizers cover.

## Main statements

* `hasPushouts_finSetSkel` — pushouts resolve, which they do not without
  the instance.
* `sampleSkelToposPushoutInitialSpan_eq` — the pushout of a span with
  initial apex is the two-element object.

## Tags

elementary topos, finite set, skeleton, test
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FinSetSkel

/-- Equalizers resolve through the instance. -/
theorem hasEqualizers_finSetSkel : HasEqualizers FinSetSkel.{0} := inferInstance

/-- Finite limits resolve through the instance. -/
theorem hasFiniteLimits_finSetSkel : HasFiniteLimits FinSetSkel.{0} :=
  inferInstance

/-- Finite colimits resolve through the instance. -/
theorem hasFiniteColimits_finSetSkel : HasFiniteColimits FinSetSkel.{0} :=
  inferInstance

/-- Pushouts resolve, through the derived finite colimits. -/
theorem hasPushouts_finSetSkel : HasPushouts FinSetSkel.{0} := inferInstance

/-- The cartesian field is the shapes module's structure. -/
theorem sampleSkelTopos_cartesian :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).cartesian
      = FinSetSkel.cartesianMonoidalCategory := rfl

/-- The closed field is the exponential module's structure. -/
theorem sampleSkelTopos_closed :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).closed
      = FinSetSkel.monoidalClosed := rfl

/-- The initial-cocone field is the shapes module's cocone. -/
theorem sampleSkelTopos_initialCocone :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).initialCocone
      = FinSetSkel.initialCocone := rfl

/-- The binary-coproduct field is the shapes module's family. -/
theorem sampleSkelTopos_binaryCoproductCocone (X Y : FinSetSkel.{0}) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).binaryCoproductCocone X Y
      = FinSetSkel.binaryCoproductCocone X Y := rfl

/-- The equalizer field is the equalizer module's family. -/
theorem sampleSkelTopos_equalizerCone {X Y : FinSetSkel.{0}} (f g : X ⟶ Y) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).equalizerCone f g
      = FinSetSkel.equalizerCone f g := rfl

/-- The coequalizer field is the coequalizer module's family. -/
theorem sampleSkelTopos_coequalizerCocone {X Y : FinSetSkel.{0}}
    (f g : X ⟶ Y) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).coequalizerCocone f g
      = FinSetSkel.coequalizerCocone f g := rfl

/-- The classifier field is the classifier module's structure. -/
theorem sampleSkelTopos_classifier :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).classifier
      = FinSetSkel.classifier := rfl

/-- The pushout of a span whose apex is initial is the binary coproduct,
and `FinSetSkel` being skeletal makes that isomorphism an equality. -/
theorem sampleSkelToposPushoutInitialSpan_eq :
    pushout (initial.to (mk 1 : FinSetSkel.{0})) (initial.to (mk 1))
      = mk 2 :=
  skeletal
    ⟨(IsPushout.of_hasBinaryCoproduct' (mk 1 : FinSetSkel.{0})
        (mk 1)).isoPushout.symm ≪≫
      colimit.isoColimitCocone (binaryCoproductCocone (mk 1) (mk 1))⟩
