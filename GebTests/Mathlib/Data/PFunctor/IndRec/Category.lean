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
the `δ`-cotuple are exercised at the sample object. The
`IR.sigmaPush` characterization is exercised at the sample code.
The `IR.deltaEmptyPush` characterization is exercised at the sample
code.
Cancellation through an isomorphism, the tower navigation weight at
the empty stack, and the three navigation characterizations are
exercised over the Booleans.
Named theorems give the `GebMeta` axiom linter declarations to
inspect.
The identity-image equation and the tower factorization of the
semantic pre-unit component are exercised at the empty stack and at
a right-appended superscript.
Composition of code morphisms, its image under `IR.interpHom`, and
the three category laws are exercised at the sample code and, with
an explicit non-identity morphism, at a `σ`-shaped code over it.

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
            (congrArg (fun c ↦ interpObj Bool Bool c sampleCategoryObj)
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
            (congrArg (fun c ↦ interpObj Bool Bool c sampleCategoryObj)
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
          (fun a ↦ interpObj Bool Bool (K' a) sampleCategoryObj) a')
        (interpMor Bool Bool (sigma Bool Bool A' K') sampleCategoryObj
          sampleCategoryObj h) =
      FreeCoprodCompDisc.Hom.comp Bool
        (interpMor Bool Bool (K' a') sampleCategoryObj sampleCategoryObj h)
        (FreeCoprodCompDisc.coprodInj Bool A'
          (fun a ↦ interpObj Bool Bool (K' a) sampleCategoryObj) a') :=
  interpMor_sigma_inj Bool Bool A' K' a' sampleCategoryObj sampleCategoryObj h

/-- The reduction of the Theorem 3 equivalence at an `ι`-shaped
`IR.mk` domain. -/
theorem sampleInterpHomEquiv_mk
    (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
      IR.{0, 0, 0, 0} Bool Bool) :
    interpHomEquiv Bool Bool (mk Bool Bool (Sum.inl true) d) sampleCategoryCode =
      interpHomEquivStep Bool Bool (Sum.inl true) d
        (fun x ↦ interpHomEquiv Bool Bool (d x)) sampleCategoryCode :=
  interpHomEquiv_mk Bool Bool (Sum.inl true) d sampleCategoryCode

/-- The reduction of the inner-hom equivalence at an `ι`-shaped
`IR.mk` domain. -/
theorem sampleInnerHomEquiv_mk
    (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
      IR.{0, 0, 0, 0} Bool Bool) :
    innerHomEquiv Bool Bool true (mk Bool Bool (Sum.inl true) d) =
      innerHomEquivStep Bool Bool true (Sum.inl true) d
        (fun x ↦ innerHomEquiv Bool Bool true (d x)) :=
  innerHomEquiv_mk Bool Bool true (Sum.inl true) d

/-- The component of `IR.interpHom` at a `σ`-domain, at the sample
codomain and object. -/
theorem sampleInterpHom_sigma (A : Type) (K : A → IR.{0, 0, 0, 0} Bool Bool)
    (f : Hom.{0, 0, 0, 0} Bool Bool (sigma Bool Bool A K) sampleCategoryCode) :
    (interpHom Bool Bool (sigma Bool Bool A K) sampleCategoryCode f).1
        sampleCategoryObj =
      FreeCoprodCompDisc.coprodDesc Bool A
        (fun a ↦ interpObj Bool Bool (K a) sampleCategoryObj)
        (interpObj Bool Bool sampleCategoryCode sampleCategoryObj)
        (fun a ↦ (interpHom Bool Bool (K a) sampleCategoryCode (f a)).1
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
        (fun i ↦ (interpHomDeltaSummand Bool Bool B c sampleCategoryCode i (f i)).1
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
        (fun i ↦ FreeCoprodCompDisc.Hom.comp Bool (m i) g) :=
  deltaDesc_comp Bool Bool B c sampleCategoryObj Z W m g

/-- The `IR.sigmaPush` characterization at the sample code. -/
theorem sampleSigmaPushChar :
    InterpHomSigmaPushMotive Bool Bool sampleCategoryCode :=
  interpHom_sigmaPush Bool Bool sampleCategoryCode

/-- The `IR.sigmaPush` characterization at the sample code, applied
at the sample object. -/
theorem sampleSigmaPushChar_apply (A' : Type)
    (K' : A' → IR.{0, 0, 0, 0} Bool Bool) (a' : A')
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode (K' a')) :
    (interpHom Bool Bool sampleCategoryCode (sigma Bool Bool A' K')
        (sigmaPush Bool Bool sampleCategoryCode A' K' a' f)).1
        sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((interpHom Bool Bool sampleCategoryCode (K' a') f).1
          sampleCategoryObj)
        (FreeCoprodCompDisc.coprodInj Bool A'
          (fun a ↦ interpObj Bool Bool (K' a) sampleCategoryObj) a') :=
  interpHom_sigmaPush Bool Bool sampleCategoryCode A' K' a' f
    sampleCategoryObj

/-- The `IR.deltaEmptyPush` characterization at the sample code. -/
theorem sampleDeltaEmptyPushChar :
    InterpHomDeltaEmptyPushMotive Bool Bool sampleCategoryCode :=
  interpHom_deltaEmptyPush Bool Bool sampleCategoryCode

/-- The `IR.deltaEmptyPush` characterization at the sample code,
applied at `PEmpty` directions and the sample object. -/
theorem sampleDeltaEmptyPushChar_apply
    (M : (PEmpty.{1} → Bool) → IR.{0, 0, 0, 0} Bool Bool)
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      (M (fun x ↦ (_root_.id x).elim))) :
    (interpHom Bool Bool sampleCategoryCode
        (delta Bool Bool PEmpty.{1} M)
        (deltaEmptyPush Bool Bool sampleCategoryCode PEmpty.{1} _root_.id
          M f)).1 sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((interpHom Bool Bool sampleCategoryCode
          (M (fun x ↦ (_root_.id x).elim)) f).1 sampleCategoryObj)
        (deltaEmptyInj Bool Bool PEmpty.{1} _root_.id M
          sampleCategoryObj) :=
  interpHom_deltaEmptyPush Bool Bool sampleCategoryCode PEmpty.{1}
    _root_.id M f sampleCategoryObj

/-- The tower navigation weight at the empty stack is the graph of
the factorization into the appended superscript. -/
theorem sampleNavWeight_nil_apply :
    (navWeight Bool Bool (fun b ↦ b) Bool (fun b ↦ b) sampleCategoryObj
        []).1 (ULift.up true) =
      Sum.inl true :=
  rfl

/-- The `IR.msigmaPush` characterization at the sample code and a
singleton stack. -/
theorem sampleMsigmaPushChar (A' : Type) (K' : A' → IR.{0, 0, 0, 0} Bool Bool)
    (a' : A')
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      (mprecomp Bool Bool [sampleCategorySup] (K' a'))) :
    (interpHom Bool Bool sampleCategoryCode
        (mprecomp Bool Bool [sampleCategorySup] (sigma Bool Bool A' K'))
        (msigmaPush Bool Bool sampleCategoryCode A' K' a' [sampleCategorySup] f)).1
        sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((interpHom Bool Bool sampleCategoryCode
          (mprecomp Bool Bool [sampleCategorySup] (K' a')) f).1 sampleCategoryObj)
        (FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Iso.hom Bool
              (mprecompIso Bool Bool [sampleCategorySup] (K' a') sampleCategoryObj))
            (FreeCoprodCompDisc.coprodInj Bool A'
              (fun a ↦ interpObj Bool Bool (K' a)
                (mplus Bool [sampleCategorySup] sampleCategoryObj)) a'))
          (FreeCoprodCompDisc.Iso.invHom Bool
            (mprecompIso Bool Bool [sampleCategorySup] (sigma Bool Bool A' K')
              sampleCategoryObj))) :=
  interpHom_msigmaPush Bool Bool sampleCategoryCode A' K' a' [sampleCategorySup] f
    sampleCategoryObj

/-- The `IR.deltaNavBase` characterization at the sample code. -/
theorem sampleDeltaNavBaseChar (Bout : Type) (iout : Bout → Bool) (Bin : Type)
    (K : (Bin → Bool) → IR.{0, 0, 0, 0} Bool Bool) (g : Bin → Bout)
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      (precomp Bool Bool Bout iout (K (iout ∘ g)))) :
    (interpHom Bool Bool sampleCategoryCode
        (precomp Bool Bool Bout iout (delta Bool Bool Bin K))
        (deltaNavBase Bool Bool sampleCategoryCode Bout iout Bin K g f)).1
        sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((interpHom Bool Bool sampleCategoryCode
          (precomp Bool Bool Bout iout (K (iout ∘ g))) f).1 sampleCategoryObj)
        (FreeCoprodCompDisc.Hom.comp Bool
          (deltaEmptyInj Bool Bool
            {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ nomatch z.2)
            (fun j ↦ precomp Bool Bool Bout iout
              (K (precompMerge Bool Bout iout (fun b ↦ Sum.inl (g b)) j)))
            sampleCategoryObj)
          (FreeCoprodCompDisc.coprodInj Bool
            (ULift.{0} (Bin → Bout ⊕ PUnit.{1}))
            (fun cl ↦ interpObj Bool Bool
              (delta Bool Bool {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp Bool Bool Bout iout
                  (K (precompMerge Bool Bout iout cl.down j)))) sampleCategoryObj)
            (ULift.up (fun b ↦ Sum.inl (g b))))) :=
  interpHom_deltaNavBase Bool Bool sampleCategoryCode Bout iout Bin K g f
    sampleCategoryObj

/-- The `IR.deltaNav` characterization at the sample code and a
singleton stack. -/
theorem sampleDeltaNavChar (Bout : Type) (iout : Bout → Bool) (Bin : Type)
    (K : (Bin → Bool) → IR.{0, 0, 0, 0} Bool Bool) (g : Bin → Bout)
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      (mprecomp Bool Bool
        ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
        (K (iout ∘ g)))) :
    (interpHom Bool Bool sampleCategoryCode
        (mprecomp Bool Bool
          ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
          (delta Bool Bool Bin K))
        (deltaNav Bool Bool sampleCategoryCode Bout iout Bin K g [sampleCategorySup]
          f)).1 sampleCategoryObj =
      FreeCoprodCompDisc.Hom.comp Bool
        ((interpHom Bool Bool sampleCategoryCode
          (mprecomp Bool Bool
            ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
            (K (iout ∘ g))) f).1 sampleCategoryObj)
        (navInj Bool Bool Bout iout Bin K g [sampleCategorySup] sampleCategoryObj) :=
  interpHom_deltaNav Bool Bool sampleCategoryCode Bout iout Bin K g [sampleCategorySup]
    f sampleCategoryObj

/-- The identity-image equation at the sample code and the empty
stack. -/
theorem sampleInterpHomPreUnitStack_nil
    (X : FreeCoprodCompDisc.{0, 0} Bool) :
    (interpHom Bool Bool sampleCategoryCode
        (mprecomp Bool Bool [] sampleCategoryCode)
        (preUnitStack Bool Bool sampleCategoryCode [])).1 X =
      preUnitComponent Bool Bool sampleCategoryCode [] X :=
  interpHom_preUnitStack Bool Bool sampleCategoryCode [] X

/-- The identity-image equation at the sample code and a
right-appended superscript, exercising the snoc/`δ` half of
`IR.interpHom_preUnitStack`'s induction. -/
theorem sampleInterpHomPreUnitStack_snoc
    (X : FreeCoprodCompDisc.{0, 0} Bool) :
    (interpHom Bool Bool sampleCategoryCode
        (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
        (preUnitStack Bool Bool sampleCategoryCode [sampleCategorySup])).1 X =
      preUnitComponent Bool Bool sampleCategoryCode [sampleCategorySup] X :=
  interpHom_preUnitStack Bool Bool sampleCategoryCode [sampleCategorySup] X

/-- The semantic pre-unit component followed by the tower
isomorphism, at the sample code and the empty stack. -/
theorem samplePreUnitComponentCompHom :
    FreeCoprodCompDisc.Hom.comp Bool
        (preUnitComponent Bool Bool sampleCategoryCode []
          sampleCategoryObj)
        (FreeCoprodCompDisc.Iso.hom Bool
          (mprecompIso Bool Bool [] sampleCategoryCode
            sampleCategoryObj)) =
      interpMor Bool Bool sampleCategoryCode sampleCategoryObj
        (mplus Bool [] sampleCategoryObj)
        (mplusInj Bool [] sampleCategoryObj) :=
  preUnitComponent_comp_hom Bool Bool sampleCategoryCode []
    sampleCategoryObj

/-- The composite of the sample identity morphism with itself. -/
def sampleCompHom :
    Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode sampleCategoryCode :=
  comp Bool Bool sampleCategoryCode sampleCategoryCode
    sampleCategoryCode (IR.id Bool Bool sampleCategoryCode)
    (IR.id Bool Bool sampleCategoryCode)

/-- The composite of the sample identity with itself is that
identity. -/
theorem sampleCompHom_eq_id :
    sampleCompHom = IR.id Bool Bool sampleCategoryCode :=
  id_comp Bool Bool sampleCategoryCode sampleCategoryCode
    (IR.id Bool Bool sampleCategoryCode)

/-- `IR.interpHom` sends the sample identity to the identity
transformation. -/
theorem sampleInterpHomId :
    interpHom Bool Bool sampleCategoryCode sampleCategoryCode
        (IR.id Bool Bool sampleCategoryCode) =
      FreeCoprodCompDisc.NatTrans.id
        (interpObj Bool Bool sampleCategoryCode)
        (interpMor Bool Bool sampleCategoryCode) :=
  interpHom_id Bool Bool sampleCategoryCode

/-- `IR.interpHom` sends a composite at the sample code to the
vertical composite. -/
theorem sampleInterpHomComp
    (f g : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      sampleCategoryCode) :
    interpHom Bool Bool sampleCategoryCode sampleCategoryCode
        (comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode f g) =
      FreeCoprodCompDisc.NatTrans.vcomp
        (interpHom Bool Bool sampleCategoryCode sampleCategoryCode f)
        (interpHom Bool Bool sampleCategoryCode sampleCategoryCode g) :=
  interpHom_comp Bool Bool sampleCategoryCode sampleCategoryCode
    sampleCategoryCode f g

/-- The right identity law at the sample code. -/
theorem sampleCompIdHom
    (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      sampleCategoryCode) :
    comp Bool Bool sampleCategoryCode sampleCategoryCode
        sampleCategoryCode f (IR.id Bool Bool sampleCategoryCode) =
      f :=
  comp_id Bool Bool sampleCategoryCode sampleCategoryCode f

/-- Associativity at the sample code. -/
theorem sampleCompAssocHom
    (f g h : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
      sampleCategoryCode) :
    comp Bool Bool sampleCategoryCode sampleCategoryCode
        sampleCategoryCode
        (comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode f g) h =
      comp Bool Bool sampleCategoryCode sampleCategoryCode
        sampleCategoryCode f
        (comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode g h) :=
  comp_assoc Bool Bool sampleCategoryCode sampleCategoryCode
    sampleCategoryCode sampleCategoryCode f g h

/-- A `σ`-shaped code over the sample `ι`-code: its self-homset is
`∀ a : Bool, Σ a', Hom (iota true) (iota true)`, non-degenerate
(essentially a `Bool → Bool` selector), unlike the identity-only
self-homset of `sampleCategoryCode`. -/
def sampleSigmaCode : IR.{0, 0, 0, 0} Bool Bool :=
  sigma Bool Bool Bool (fun _ ↦ sampleCategoryCode)

/-- The branch-swapping selector: a self-morphism of
`sampleSigmaCode` distinct from `IR.id`, since it sends each `a` to
`!a` rather than to `a`. -/
def sampleSigmaSwapHom :
    Hom.{0, 0, 0, 0} Bool Bool sampleSigmaCode sampleSigmaCode :=
  fun a ↦ ⟨!a, ⟨⟨rfl⟩⟩⟩

/-- The composite of `IR.id` on the left with the swap selector, at
`sampleSigmaCode`. -/
def sampleSigmaIdCompHom :
    Hom.{0, 0, 0, 0} Bool Bool sampleSigmaCode sampleSigmaCode :=
  comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
    (IR.id Bool Bool sampleSigmaCode) sampleSigmaSwapHom

/-- `IR.id_comp` at the swap selector: a non-degenerate instance of
the left identity law. -/
theorem sampleSigmaIdCompHom_eq_swap :
    sampleSigmaIdCompHom = sampleSigmaSwapHom :=
  id_comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaSwapHom

/-- The composite of the swap selector with `IR.id` on the right, at
`sampleSigmaCode`. -/
def sampleSigmaCompIdHom :
    Hom.{0, 0, 0, 0} Bool Bool sampleSigmaCode sampleSigmaCode :=
  comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
    sampleSigmaSwapHom (IR.id Bool Bool sampleSigmaCode)

/-- `IR.comp_id` at the swap selector: a non-degenerate instance of
the right identity law. -/
theorem sampleSigmaCompIdHom_eq_swap :
    sampleSigmaCompIdHom = sampleSigmaSwapHom :=
  comp_id Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaSwapHom

/-- Associativity at `sampleSigmaCode`, with the swap selector
composed with itself: a non-degenerate instance. -/
theorem sampleSigmaCompAssocHom :
    comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
        (comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
          sampleSigmaSwapHom sampleSigmaSwapHom) sampleSigmaSwapHom =
      comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
        sampleSigmaSwapHom
        (comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
          sampleSigmaSwapHom sampleSigmaSwapHom) :=
  comp_assoc Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
    sampleSigmaCode sampleSigmaSwapHom sampleSigmaSwapHom sampleSigmaSwapHom

/-- `IR.interpHom` sends the swap selector composed with itself to
the vertical composite, at `sampleSigmaCode`: a non-degenerate
instance of functoriality. -/
theorem sampleSigmaInterpHomComp :
    interpHom Bool Bool sampleSigmaCode sampleSigmaCode
        (comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
          sampleSigmaSwapHom sampleSigmaSwapHom) =
      FreeCoprodCompDisc.NatTrans.vcomp
        (interpHom Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaSwapHom)
        (interpHom Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaSwapHom) :=
  interpHom_comp Bool Bool sampleSigmaCode sampleSigmaCode sampleSigmaCode
    sampleSigmaSwapHom sampleSigmaSwapHom
