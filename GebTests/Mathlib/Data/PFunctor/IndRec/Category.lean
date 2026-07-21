/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Category

/-!
# Tests for the category of IR codes

A sample object, superscript, and `ι`-code over the Booleans
exercise the semantic tower: the iterated coproduct object and its
injection at the empty and singleton stacks and at a right-appended
superscript, the tower action on morphisms, the iterated Lemma 4
isomorphism at the empty stack, at a right-appended superscript,
and in the interpreted object, and the semantic pre-unit component
at the empty stack. The reductions of the two equivalences at an
`IR.mk`-built domain, the component of `IR.interpHom` at each shape
of domain code, the `σ`-injection square, and right-composition of
the `δ`-cotuple are exercised at the sample object. Named theorems
give the `GebMeta` axiom linter declarations to inspect.

## Tags

inductive-recursive, morphism, category
-/

@[expose] public section

open CategoryTheory
open IndRec IndRec.IR

/-- A sample object over the Boolean index type. -/
def sampleCategoryObj : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, fun b ↦ b⟩

/-- A sample superscript object over the Boolean index type. -/
def sampleCategorySup : SupObj.{0, 0} Bool :=
  ⟨Bool, fun b ↦ b⟩

/-- A sample `ι`-code over the Booleans. -/
def sampleCategoryCode : IR.{0, 0, 0, 0} Bool Bool :=
  iota Bool Bool true

/-- The tower object at a singleton stack, exercising `IR.mplus`. -/
def sampleMplusObj : FreeCoprodCompDisc.{0, 0} Bool :=
  mplus Bool [sampleCategorySup] sampleCategoryObj

/-- The tower at the empty stack is its base. -/
theorem sampleMplus_nil :
    mplus Bool [] sampleCategoryObj = sampleCategoryObj :=
  rfl

/-- The tower injection at a singleton stack is the right injection. -/
theorem sampleMplusInj_apply :
    (mplusInj Bool [sampleCategorySup] sampleCategoryObj).1 true =
      Sum.inr true :=
  rfl

/-- The tower action on morphisms fixes the stacked superscript. -/
theorem sampleMplusMorMap_apply :
    (mplusMorMap Bool [sampleCategorySup] sampleCategoryObj sampleCategoryObj
        (FreeCoprodCompDisc.Hom.id Bool sampleCategoryObj)).1 (Sum.inl true) =
      Sum.inl true :=
  rfl

/-- The tower isomorphism at the empty stack is the identity. -/
theorem sampleMprecompIso_nil :
    FreeCoprodCompDisc.Iso.hom Bool
        (mprecompIso Bool Bool [] sampleCategoryCode sampleCategoryObj) =
      FreeCoprodCompDisc.Hom.id Bool
        (interpObj Bool Bool sampleCategoryCode sampleCategoryObj) :=
  Subtype.ext rfl

/-- The semantic pre-unit component at the empty stack is the
identity. -/
theorem samplePreUnitComponent_nil :
    preUnitComponent Bool Bool sampleCategoryCode [] sampleCategoryObj =
      FreeCoprodCompDisc.Hom.id Bool
        (interpObj Bool Bool sampleCategoryCode sampleCategoryObj) :=
  preUnitComponent_nil Bool Bool sampleCategoryCode sampleCategoryObj

/-- The tower at a right-appended superscript. -/
theorem sampleMplus_snoc :
    mplus Bool ([sampleCategorySup] ++ [sampleCategorySup]) sampleCategoryObj =
      mplus Bool [sampleCategorySup]
        (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj) :=
  mplus_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj

/-- The tower injection at a right-appended superscript. -/
theorem sampleMplusInj_snoc :
    cast (congrArg (FreeCoprodCompDisc.Hom Bool sampleCategoryObj)
        (mplus_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj))
        (mplusInj Bool ([sampleCategorySup] ++ [sampleCategorySup]) sampleCategoryObj) =
      FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodPairInr Bool sampleCategorySup sampleCategoryObj)
        (mplusInj Bool [sampleCategorySup]
          (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj)) :=
  mplusInj_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj

/-- The forward component of the tower isomorphism at a right-appended
superscript. -/
theorem sampleMprecompIso_snoc_hom :
    FreeCoprodCompDisc.Iso.hom Bool
        (mprecompIso Bool Bool ([sampleCategorySup] ++ [sampleCategorySup])
          sampleCategoryCode sampleCategoryObj) =
      FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
            (congrArg (fun c => interpObj Bool Bool c sampleCategoryObj)
              (mprecomp_snoc Bool Bool [sampleCategorySup] sampleCategorySup
                sampleCategoryCode))))
          (FreeCoprodCompDisc.Iso.hom Bool
            (interpPrecompIso Bool Bool
              (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
              sampleCategorySup.1 sampleCategorySup.2 sampleCategoryObj)))
        (FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.hom Bool
            (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
              (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj)))
          (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
            (congrArg (interpObj Bool Bool sampleCategoryCode)
              (mplus_snoc Bool [sampleCategorySup] sampleCategorySup
                sampleCategoryObj).symm)))) :=
  mprecompIso_snoc_hom Bool Bool [sampleCategorySup] sampleCategorySup
    sampleCategoryCode sampleCategoryObj

/-- The inverse component of the tower isomorphism at a right-appended
superscript. -/
theorem sampleMprecompIso_snoc_invHom :
    FreeCoprodCompDisc.Iso.invHom Bool
        (mprecompIso Bool Bool ([sampleCategorySup] ++ [sampleCategorySup])
          sampleCategoryCode sampleCategoryObj) =
      FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
            (congrArg (interpObj Bool Bool sampleCategoryCode)
              (mplus_snoc Bool [sampleCategorySup] sampleCategorySup
                sampleCategoryObj))))
          (FreeCoprodCompDisc.Iso.invHom Bool
            (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
              (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj))))
        (FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.invHom Bool
            (interpPrecompIso Bool Bool
              (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
              sampleCategorySup.1 sampleCategorySup.2 sampleCategoryObj))
          (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
            (congrArg (fun c => interpObj Bool Bool c sampleCategoryObj)
              (mprecomp_snoc Bool Bool [sampleCategorySup] sampleCategorySup
                sampleCategoryCode).symm)))) :=
  mprecompIso_snoc_invHom Bool Bool [sampleCategorySup] sampleCategorySup
    sampleCategoryCode sampleCategoryObj

/-- Naturality of the tower isomorphism at a singleton stack. -/
theorem sampleMprecompIso_natural
    (h : FreeCoprodCompDisc.Hom Bool sampleCategoryObj sampleCategoryObj) :
    FreeCoprodCompDisc.Hom.comp Bool
        (interpMor Bool Bool
          (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
          sampleCategoryObj sampleCategoryObj h)
        (FreeCoprodCompDisc.Iso.hom Bool
          (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
            sampleCategoryObj)) =
      FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Iso.hom Bool
          (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
            sampleCategoryObj))
        (interpMor Bool Bool sampleCategoryCode
          (mplus Bool [sampleCategorySup] sampleCategoryObj)
          (mplus Bool [sampleCategorySup] sampleCategoryObj)
          (mplusMorMap Bool [sampleCategorySup] sampleCategoryObj sampleCategoryObj
            h)) :=
  mprecompIso_natural Bool Bool [sampleCategorySup] sampleCategoryCode
    sampleCategoryObj sampleCategoryObj h

/-- The component of `IR.interpHom` at the sample `ι`-domain. -/
theorem sampleInterpHomIota_component
    (f : InnerHom.{0, 0, 0, 0} Bool Bool true sampleCategoryCode) :
    (interpHom Bool Bool (iota Bool Bool true) sampleCategoryCode f).1
        sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((FreeCoprodCompDisc.homSingletonEquiv Bool true
            (interpObj Bool Bool sampleCategoryCode
              (FreeCoprodCompDisc.emptyObj Bool))).symm
          (innerHomEquiv Bool Bool true sampleCategoryCode f))
        (interpMor Bool Bool sampleCategoryCode
          (FreeCoprodCompDisc.emptyObj Bool) sampleCategoryObj
          (FreeCoprodCompDisc.emptyDesc Bool sampleCategoryObj)) :=
  interpHom_iota Bool Bool true sampleCategoryCode f sampleCategoryObj

/-- The `σ`-injection square at the sample object. -/
theorem sampleInterpMorSigmaInj (A' : Type)
    (K' : A' → IR.{0, 0, 0, 0} Bool Bool) (a' : A')
    (h : FreeCoprodCompDisc.Hom Bool sampleCategoryObj sampleCategoryObj) :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodInj Bool A'
          (fun a => interpObj Bool Bool (K' a) sampleCategoryObj) a')
        (interpMor Bool Bool (sigma Bool Bool A' K') sampleCategoryObj
          sampleCategoryObj h) =
      FreeCoprodCompDisc.Hom.comp Bool
        (interpMor Bool Bool (K' a') sampleCategoryObj sampleCategoryObj h)
        (FreeCoprodCompDisc.coprodInj Bool A'
          (fun a => interpObj Bool Bool (K' a) sampleCategoryObj) a') :=
  interpMor_sigma_inj Bool Bool A' K' a' sampleCategoryObj sampleCategoryObj h

/-- The reduction of the Theorem 3 equivalence at an `ι`-shaped
`IR.mk` domain. -/
theorem sampleInterpHomEquiv_mk
    (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
      IR.{0, 0, 0, 0} Bool Bool) :
    interpHomEquiv Bool Bool (mk Bool Bool (Sum.inl true) d) sampleCategoryCode =
      interpHomEquivStep Bool Bool (Sum.inl true) d
        (fun x => interpHomEquiv Bool Bool (d x)) sampleCategoryCode :=
  interpHomEquiv_mk Bool Bool (Sum.inl true) d sampleCategoryCode

/-- The reduction of the inner-hom equivalence at an `ι`-shaped
`IR.mk` domain. -/
theorem sampleInnerHomEquiv_mk
    (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
      IR.{0, 0, 0, 0} Bool Bool) :
    innerHomEquiv Bool Bool true (mk Bool Bool (Sum.inl true) d) =
      innerHomEquivStep Bool Bool true (Sum.inl true) d
        (fun x => innerHomEquiv Bool Bool true (d x)) :=
  innerHomEquiv_mk Bool Bool true (Sum.inl true) d

/-- The component of `IR.interpHom` at a `σ`-domain, at the sample
codomain and object. -/
theorem sampleInterpHom_sigma (A : Type) (K : A → IR.{0, 0, 0, 0} Bool Bool)
    (f : Hom.{0, 0, 0, 0} Bool Bool (sigma Bool Bool A K) sampleCategoryCode) :
    (interpHom Bool Bool (sigma Bool Bool A K) sampleCategoryCode f).1
        sampleCategoryObj =
      FreeCoprodCompDisc.coprodDesc Bool A
        (fun a => interpObj Bool Bool (K a) sampleCategoryObj)
        (interpObj Bool Bool sampleCategoryCode sampleCategoryObj)
        (fun a => (interpHom Bool Bool (K a) sampleCategoryCode (f a)).1
          sampleCategoryObj) :=
  interpHom_sigma Bool Bool A K sampleCategoryCode f sampleCategoryObj

/-- The component of `IR.interpHom` at a `δ`-domain, at the sample
codomain and object. -/
theorem sampleInterpHom_delta (B : Type)
    (c : (B → Bool) → IR.{0, 0, 0, 0} Bool Bool)
    (f : Hom.{0, 0, 0, 0} Bool Bool (delta Bool Bool B c) sampleCategoryCode) :
    (interpHom Bool Bool (delta Bool Bool B c) sampleCategoryCode f).1
        sampleCategoryObj =
      deltaDesc Bool Bool B c sampleCategoryObj
        (interpObj Bool Bool sampleCategoryCode sampleCategoryObj)
        (fun i => (interpHomDeltaSummand Bool Bool B c sampleCategoryCode i (f i)).1
          sampleCategoryObj) :=
  interpHom_delta Bool Bool B c sampleCategoryCode f sampleCategoryObj

/-- Right-composition of the `δ`-cotuple at the sample object. -/
theorem sampleDeltaDesc_comp (B : Type)
    (c : (B → Bool) → IR.{0, 0, 0, 0} Bool Bool)
    (Z W : FreeCoprodCompDisc.{0, 0} Bool)
    (m : (i : B → Bool) → FreeCoprodCompDisc.Hom Bool
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift Bool ⟨B, i⟩) (interpObj Bool Bool (c i))
        sampleCategoryObj) Z)
    (g : FreeCoprodCompDisc.Hom Bool Z W) :
    FreeCoprodCompDisc.Hom.comp Bool
        (deltaDesc Bool Bool B c sampleCategoryObj Z m) g =
      deltaDesc Bool Bool B c sampleCategoryObj W
        (fun i => FreeCoprodCompDisc.Hom.comp Bool (m i) g) :=
  deltaDesc_comp Bool Bool B c sampleCategoryObj Z W m g
