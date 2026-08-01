/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.PresheafIRProto.Basic
public import Geb.Internal.PresheafIRProto.Codes
public import Mathlib.CategoryTheory.Yoneda

/-!
# Prototype: the p.r.a. formula with the presheaf hom bundled

Packages the choice-free core (`PresheafIRProto.Basic`) statement of the
p.r.a. formula `T Z ≃ Σ a, Hom(E(a), Z)` with its hom written as a
functor-category hom `arityPresheaf F a ⟶ Z`. Writing `⟶` between two objects
of a presheaf category invokes `CategoryTheory.Functor.category`, which is
`Classical.choice`-dependent, so this packaging is kept in a separate module
from the choice-free core.

Its content is `arityHomEquivNatTrans`, the bundling isomorphism: a
`CategoryTheory.NatTrans` is its `app` field together with `naturality`, and
`GebProto.ArityHom` is exactly that data unbundled, so the equivalence is the
identity on both sides. The formula itself is then transported along it from
the core `GebProto.objEquivSigmaArityHom`; no part of it is re-proved here.

## Main definitions

* `GebProto.arityHomEquivNatTrans` — the bundling isomorphism between the
  unbundled arity hom and the functor-category hom.
* `GebProto.objEquivSigmaHom` — the p.r.a. formula with the presheaf hom
  bundled.

## References

* [GhaniNordvallForsbergMalatesta2015]

## Tags

prototype, presheaf, parametric right adjoint, functor category
-/

@[expose] public section

universe uI uJ uA uB uZ vI vJ

open CategoryTheory

namespace GebProto

section CoproductOfRepresentables

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The bundling isomorphism: an unbundled arity hom is a natural
transformation `E(a) ⟶ Z`. Forward is `natTransOfArityHom`, backward reads off
the components and re-states naturality elementwise; both round trips are
definitional. -/
def arityHomEquivNatTrans (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uB) : ArityHom F a Z ≃ (arityPresheaf F a ⟶ Z) where
  toFun μ := natTransOfArityHom F a μ
  invFun α := ⟨fun i ↦ α.app ⟨i⟩, fun _ _ f b ↦ NatTrans.naturality_apply α f.op b⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The p.r.a. formula: the domain-restricted interpretation of `F` at `Z` is
the coproduct over shapes of the representables on the arity presheaves. The
core `objEquivSigmaArityHom` transported fibrewise along the bundling
isomorphism. -/
def objEquivSigmaHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (Z : Iᵒᵖ ⥤ Type uB) :
    F.toPresheafDomPFunctorData.obj Z ≃ Σ a : F.A, (arityPresheaf F a ⟶ Z) :=
  (objEquivSigmaArityHom F Z).trans
    (Equiv.sigmaCongrRight fun a ↦ arityHomEquivNatTrans F a Z)

/-- At `uZ := uB` the arity presheaf and the input presheaf are objects of one
category, so the hom the p.r.a. formula needs is formable with no transport. -/
def arityPresheafHomAtUB (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uB) : Type (max uI uB) :=
  arityPresheaf F a ⟶ Z

/-- At an unrelated `uZ` the hom is formable after `ULift`ing both sides into
`Type (max uB uZ)`; `max` is commutative on levels, so the two composites are
objects of one category. -/
def arityPresheafHomULifted (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type (max uI uB uZ) :=
  (arityPresheaf F a ⋙ uliftFunctor.{uZ, uB}) ⟶ (Z ⋙ uliftFunctor.{uB, uZ})

set_option linter.checkUnivs false in
/-- The representable case is definitionally the `P := yoneda.obj j₀` case: the
two shape types coincide on the nose. Kept here rather than in the choice-free
core because `yoneda` lands in a functor category, so naming it — which the
axiom linter requires — would import `Classical.choice` into that core. -/
theorem iotaPresheafData_A_eq_iotaConstData_yoneda (j₀ : J) :
    (iotaPresheafData.{uI, uJ, uB, vI, vJ} (I := I) j₀).A =
      (iotaConstData.{uI, uJ, vJ, vI, vJ} (I := I) (yoneda.obj j₀)).A := rfl


end CoproductOfRepresentables

/-- A functorial `BaseArity` is a functor from the output base to presheaves on
the input base — equivalently, to discrete fibrations over it. This is the
`δ` rule's arity datum in bundled form: `famPresheaf` is the object part,
`reindexHom` the morphism part, and the remaining two clauses of
`BaseArity.IsFunctorial` are the functor laws.

Kept here rather than in the choice-free core because the target
`Iᵒᵖ ⥤ Type uB` is a functor category, whose `Category` instance is
`Classical.choice`-dependent. -/
def BaseArity.functor {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (P : BaseArity.{uI, uJ, uB, vI, vJ} I J) (hP : P.IsFunctorial) :
    J ⥤ (Iᵒᵖ ⥤ Type uB) where
  obj j := P.famPresheaf hP j
  map g := P.reindexHom hP g
  map_id j := by
    ext i d
    exact congrFun (hP.reindex_id j i.unop) d
  map_comp g h := by
    ext i d
    exact congrFun (hP.reindex_comp h g i.unop) d

end GebProto
