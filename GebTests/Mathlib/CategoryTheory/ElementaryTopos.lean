/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.ElementaryTopos

/-!
# Tests for the elementary-topos class

An instance at the degenerate topos `Discrete PUnit` witnesses that
the class is inhabitable, and resolution assertions confirm that each
derived `Prop` instance is reachable through it.

## Tags

elementary topos, subobject classifier, degenerate topos
-/

set_option linter.privateModule false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

section Resolution

variable (C : Type u) [Category.{v} C] [ElementaryTopos C]

example : HasInitial C := inferInstance
example : HasBinaryCoproducts C := inferInstance
example : HasEqualizers C := inferInstance
example : HasCoequalizers C := inferInstance
example : HasFiniteCoproducts C := inferInstance
example : HasFiniteLimits C := inferInstance
example : HasFiniteColimits C := inferInstance

attribute [local instance] ElementaryTopos.cartesianMonoidalCategory

/-- The data accessors cross the module boundary. -/
example : CartesianMonoidalCategory C :=
  ElementaryTopos.cartesianMonoidalCategory C

example : MonoidalClosed C := ElementaryTopos.monoidalClosed C

end Resolution

section Witness

/-- The degenerate topos: one object, one morphism. -/
abbrev Pt := Discrete PUnit.{1}

/-- Every hom-set of `Pt` is a singleton. mathlib supplies
`Subsingleton`; the `Unique` instance is what the constructions below
need. -/
instance uniqueHom (X Y : Pt) : Unique (X ⟶ Y) where
  default := eqToHom (by obtain ⟨⟨⟩⟩ := X; obtain ⟨⟨⟩⟩ := Y; rfl)
  uniq _ := Subsingleton.elim _ _

variable {J : Type u} [Category.{v} J] {F : J ⥤ Pt}

/-- Every cone over a functor into `Pt` is a limit cone. -/
def ptIsLimit (c : Cone F) : IsLimit c where
  lift _ := default
  fac := by intros; apply Subsingleton.elim
  uniq := by intros; apply Subsingleton.elim

/-- Every cocone over a functor into `Pt` is a colimit cocone. -/
def ptIsColimit (c : Cocone F) : IsColimit c where
  desc _ := default
  fac := by intros; apply Subsingleton.elim
  uniq := by intros; apply Subsingleton.elim

/-- A chosen limit cone over any functor into `Pt`. -/
def ptLimitCone (F : J ⥤ Pt) : LimitCone F where
  cone :=
    { pt := ⟨⟨⟩⟩
      π :=
        { app := fun _ => default
          naturality := by intros; apply Subsingleton.elim } }
  isLimit := ptIsLimit _

/-- A chosen colimit cocone over any functor into `Pt`. -/
def ptColimitCocone (F : J ⥤ Pt) : ColimitCocone F where
  cocone :=
    { pt := ⟨⟨⟩⟩
      ι :=
        { app := fun _ => default
          naturality := by intros; apply Subsingleton.elim } }
  isColimit := ptIsColimit _

/-- The cartesian structure on `Pt`. -/
instance ptCart : CartesianMonoidalCategory Pt :=
  .ofChosenFiniteProducts (ptLimitCone _) (fun X Y => ptLimitCone (pair X Y))

/-- Any two endofunctors of `Pt` are adjoint, hom-sets being
singletons. -/
def ptAdj (F G : Pt ⥤ Pt) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => Equiv.ofUnique _ _
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by intros; apply Subsingleton.elim }

/-- `Pt` is monoidal closed: every endofunctor is a right adjoint. -/
instance : MonoidalClosed Pt where
  closed _ := { rightAdj := 𝟭 Pt, adj := ptAdj _ _ }

/-- The degenerate topos is an elementary topos. -/
instance : ElementaryTopos Pt where
  cartesian := ptCart
  closed := (inferInstance : @MonoidalClosed Pt _ ptCart.toMonoidalCategory)
  initialCocone := ptColimitCocone _
  binaryCoproductCocone X Y := ptColimitCocone (pair X Y)
  equalizerCone f g := ptLimitCone (parallelPair f g)
  coequalizerCocone f g := ptColimitCocone (parallelPair f g)
  classifier :=
    Subobject.Classifier.mkOfTerminalΩ₀ (𝟙_ Pt)
      CartesianMonoidalCategory.isTerminalTensorUnit ⟨⟨⟩⟩ default
      (fun _ => default)
      (fun _ => { toCommSq := ⟨Subsingleton.elim _ _⟩
                  isLimit' := ⟨ptIsLimit _⟩ })
      (by intros; apply Subsingleton.elim)

example : HasFiniteLimits Pt := inferInstance
example : HasFiniteColimits Pt := inferInstance
example : HasFiniteCoproducts Pt := inferInstance
example : HasEqualizers Pt := inferInstance
example : HasCoequalizers Pt := inferInstance
example : HasInitial Pt := inferInstance
example : HasBinaryCoproducts Pt := inferInstance

end Witness
