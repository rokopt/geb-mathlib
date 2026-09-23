/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.Agreement
public import GebTests.Prototypes.QuotientPRA.Directions

set_option doc.verso true in
/-!
# The directions in commutative trees, presented

The quotient of directions in commutative trees over the walking arrow
({name}`GebProto.QuotientPRA.Directions.F`) has its presentation over the tree and direction
constructors, with one equation for each witness constructor. Its classes of directions are the
quotient's ({lit}`dirEquiv`), and the eliminator of the quotient into them sends the two leaf
directions of the tree of two leaves to the terms that build them, so the presentation identifies
those terms ({lit}`inL_here_eq_inR_here`).

## Main definitions

* {lit}`dirEquiv` — the classes of directions as the quotient's.
* {lit}`hereCls`, {lit}`leafCls` — the classes of the leaf's direction and of the leaf.

## Main statements

* {lit}`inL_here_eq_inR_here` — the presentation identifies the two leaf directions of the tree
  of two leaves.

## Tags

presheaf, equational presentation, quotient inductive-inductive type, walking arrow, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.PresheafAgreementTests

open CategoryTheory Limits GebProto.QuotientPRA GebProto.QuotientPRA.Directions Geb.Definition.Slice
  Geb.Definition.Presheaf Geb.Definition.Presheaf.QPRA

attribute [local instance] finEnumTermSig finEnumOps

/-- The classes of closed terms of the presentation over the directions are the quotient's. -/
def dirEquiv : (onestep freeArity).toSlice.Cls (noVar Bool) true ≃ (quotient F).obj ⟨true⟩ :=
  clsEquiv hasCongruences true

/-- The class of the leaf's direction. -/
def hereCls : (onestep freeArity).toSlice.Cls (noVar Bool) true :=
  (onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.here, rfl⟩) fun b ↦ nomatch b

/-- The class of the leaf. -/
def leafCls : (onestep freeArity).toSlice.Cls (noVar Bool) false :=
  (onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.leaf, rfl⟩) fun b ↦ nomatch b

/-- The eliminator sends the class of the leaf's direction to its class of terms. -/
theorem φ_here : (φ restr_id restr_comp reindex_id reindex_comp).app ⟨true⟩ (quotientMk F here) =
    hereCls :=
  (φ_quotientMk_freeNode hasCongruences ⟨.here, rfl⟩ _).trans
    (congrArg ((onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.here, rfl⟩))
      (funext fun b ↦ nomatch b))

/-- The eliminator sends the class of the leaf to its class of terms. -/
theorem φ_leaf : (φ restr_id restr_comp reindex_id reindex_comp).app ⟨false⟩ (quotientMk F leaf) =
    leafCls :=
  (φ_quotientMk_freeNode hasCongruences ⟨.leaf, rfl⟩ _).trans
    (congrArg ((onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.leaf, rfl⟩))
      (funext fun b ↦ nomatch b))

/-- The eliminator sends the class of the direction of the left leaf of the tree of two leaves to
its class of terms. -/
theorem φ_inL : (φ restr_id restr_comp reindex_id reindex_comp).app ⟨true⟩
    (quotientMk F (inL here leaf)) = (onestep freeArity).toSlice.op (noVar Bool)
      (.inl ⟨.inL, rfl⟩) (fun | false => hereCls | true => leafCls) := by
  refine (φ_quotientMk_freeNode hasCongruences ⟨.inL, rfl⟩ _).trans
    (congrArg ((onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.inL, rfl⟩))
      (funext fun b ↦ ?_))
  cases b
  exacts [φ_here, φ_leaf]

/-- The eliminator sends the class of the direction of the right leaf of the tree of two leaves
to its class of terms. -/
theorem φ_inR : (φ restr_id restr_comp reindex_id reindex_comp).app ⟨true⟩
    (quotientMk F (inR leaf here)) = (onestep freeArity).toSlice.op (noVar Bool)
      (.inl ⟨.inR, rfl⟩) (fun | false => leafCls | true => hereCls) := by
  refine (φ_quotientMk_freeNode hasCongruences ⟨.inR, rfl⟩ _).trans
    (congrArg ((onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.inR, rfl⟩))
      (funext fun b ↦ ?_))
  cases b
  exacts [φ_leaf, φ_here]

/-- The presentation identifies the direction of the left leaf of the tree of two leaves with
the direction of its right leaf, as the quotient does. -/
theorem inL_here_eq_inR_here :
    (onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.inL, rfl⟩)
        (fun | false => hereCls | true => leafCls) =
      (onestep freeArity).toSlice.op (noVar Bool) (.inl ⟨.inR, rfl⟩)
        (fun | false => leafCls | true => hereCls) :=
  φ_inL.symm.trans ((congrArg (fun q ↦ (φ restr_id restr_comp reindex_id reindex_comp).app
    ⟨true⟩ q) Directions.inL_here_eq_inR_here).trans φ_inR)

end Geb.Definition.PresheafAgreementTests

end
