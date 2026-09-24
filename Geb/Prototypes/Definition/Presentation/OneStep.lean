/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Free
public import Geb.Prototypes.QuotientPRA.Initial
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# One-step equations as presentations

A system of one-step equations ({name}`GebProto.QuotientPRA.Signature.Equations`), each side
one operation applied to variables, is the presentation whose sides are those operations as
terms of depth one ({lit}`Presentation.ofEquations`). An algebra satisfies the one as it
satisfies the other ({lit}`Presentation.satisfies_ofEquations_iff`).

For a finitary signature and equations with finitely many variables, the classes of closed
terms of the presentation and the quotient W-type of the system
({name}`GebProto.QuotientPRA.Signature.Cls`) are both initial among the algebras satisfying the
equations, so the value of classes in the other algebra is an isomorphism of algebras between
them ({lit}`Presentation.clsEquiv`, {lit}`Presentation.clsEquiv_op`).

## Main definitions

* {lit}`Presentation.ofEquations` — the presentation of a system of one-step equations.
* {lit}`Presentation.clsEquiv` — the isomorphism between the classes of closed terms and the
  quotient W-type.

## Main statements

* {lit}`Presentation.eval_liftObj` — the value of a term of depth one.
* {lit}`Presentation.satisfies_ofEquations_iff` — the two notions of satisfaction agree.
* {lit}`Presentation.clsEquiv_op` — the isomorphism is a morphism of algebras.

## References

* {cite}`FiorePittsSteenkamp2020`, for W-types with equations.

## Tags

equational presentation, quotient inductive type, initial algebra, one-step equation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presentation

open PFunctor GebProto GebProto.QuotientPRA

universe uA uB v

variable {P : PFunctor.{uA, uB}} (eqns : Signature.Equations P)

/-- The presentation of a system of one-step equations: each side, an operation applied to
variables, as a term of depth one. -/
abbrev ofEquations : Presentation.{uA, uA, uB} P where
  E := ⟨eqns.E, eqns.V⟩
  lhs e := FreeM.liftObj (eqns.lhs e)
  rhs e := FreeM.liftObj (eqns.rhs e)

/-- The value of a term of depth one is the algebra applied to the values of its variables. -/
theorem eval_liftObj {Γ : Type uB} {V : Type v} (alg : P.Obj V → V) (σ : Γ → V) (x : P.Obj Γ) :
    eval alg σ (FreeM.liftObj x) = alg (P.map σ x) := by
  obtain ⟨a, k⟩ := x
  rfl

/-- An algebra satisfies the presentation of a system of one-step equations exactly when it
satisfies the system. -/
theorem satisfies_ofEquations_iff {Y : Type (max uA uB)} (S : P.Obj Y → Y) :
    (ofEquations eqns).Satisfies S ↔ Signature.Satisfies (eqns := eqns) S := by
  simp only [Satisfies, Signature.Satisfies, eval_liftObj]

variable [∀ a, FinEnum (P.B a)] [∀ e, FinEnum (eqns.V e)]

/-- The classes of closed terms of the presentation, valued in the quotient W-type. -/
def toSig : (ofEquations eqns).Cls PEmpty → Signature.Cls P eqns :=
  (ofEquations eqns).lift (fun x ↦ Signature.opQ x.1 x.2)
    ((satisfies_ofEquations_iff eqns _).mpr Signature.satisfies_opQ) PEmpty.elim

/-- The classes of the quotient W-type, valued in the classes of closed terms of the
presentation. -/
def ofSig : Signature.Cls P eqns → (ofEquations eqns).Cls PEmpty :=
  (Signature.lift ((ofEquations eqns).clsAlg PEmpty)
    ((satisfies_ofEquations_iff eqns _).mp (ofEquations eqns).satisfies_clsAlg)).app ⟨⟨⟨⟩⟩⟩

/-- The value in the quotient W-type is a morphism of algebras. -/
theorem toSig_op (a : P.A) (f : P.B a → (ofEquations eqns).Cls PEmpty) :
    toSig eqns ((ofEquations eqns).op a f) = Signature.opQ a fun b ↦ toSig eqns (f b) :=
  (ofEquations eqns).lift_op _ _ a f

/-- The value in the classes of closed terms is a morphism of algebras. -/
theorem ofSig_opQ (a : P.A) (f : P.B a → Signature.Cls P eqns) :
    ofSig eqns (Signature.opQ a f) = (ofEquations eqns).op a fun b ↦ ofSig eqns (f b) :=
  Signature.lift_opQ _ a f

/-- The classes of closed terms of the presentation are isomorphic, as algebras, to the classes
of the quotient W-type: both are initial among the algebras satisfying the equations. -/
def clsEquiv : (ofEquations eqns).Cls PEmpty ≃ Signature.Cls P eqns where
  toFun := toSig eqns
  invFun := ofSig eqns
  left_inv q := by
    have hg := (ofEquations eqns).eq_lift (ofEquations eqns).satisfies_clsAlg PEmpty.elim
      (fun q ↦ ofSig eqns (toSig eqns q))
      (fun a f ↦ by rw [toSig_op, ofSig_opQ]; rfl) (fun x ↦ nomatch x) q
    have hid := (ofEquations eqns).eq_lift (ofEquations eqns).satisfies_clsAlg PEmpty.elim id
      (fun _ _ ↦ rfl) (fun x ↦ nomatch x) q
    exact hg.trans hid.symm
  right_inv q := by
    have hg := Signature.eq_lift Signature.satisfies_opQ (fun q ↦ toSig eqns (ofSig eqns q))
      (fun a f ↦ by rw [ofSig_opQ, toSig_op]) q
    have hid := Signature.eq_lift Signature.satisfies_opQ id (fun _ _ ↦ rfl) q
    exact hg.trans hid.symm

/-- The isomorphism is a morphism of algebras. -/
theorem clsEquiv_op (a : P.A) (f : P.B a → (ofEquations eqns).Cls PEmpty) :
    clsEquiv eqns ((ofEquations eqns).op a f) = Signature.opQ a fun b ↦ clsEquiv eqns (f b) :=
  toSig_op eqns a f

end Geb.Definition.Presentation

end
