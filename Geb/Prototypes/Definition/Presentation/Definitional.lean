/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Definitional presentations

Derived operations {lit}`δ : Derived P Q` present, over the signature {lit}`sum P Q`, the
equations {lit}`q(x⃗) = δ q (x⃗)`: each new operation, applied to its variables, equals its
body ({lit}`Presentation.ofDerived`). The presentation changes nothing: its classes of terms are
the terms of {lit}`P` ({lit}`Presentation.clsEquivBase`), which are the criteria for a
definition {cite}`Suppes1957`:

* eliminability: every term over {lit}`sum P Q` has the class of a term of {lit}`P`, its
  unfolding ({lit}`Presentation.cls_inlTerm_unfoldOps`), a single witness replacing each new
  operation by the instance of its equation;
* non-creativity: terms of {lit}`P` with one class are equal
  ({lit}`Presentation.eq_of_cls_inlTerm_eq`), since the value of classes in the terms of
  {lit}`P`, each new operation read as its body, is the unfolding.

In the terms of the analysis by coequalizers: the unfolding {lit}`Presentation.unfoldOps`, the
monad morphism of the handler sending each operation of {lit}`P` to itself and each new
operation to its body, coequalizes the two endpoint maps ({lit}`Presentation.unfoldOps_src`),
and the inclusion of the terms of {lit}`P` is a section of it
({lit}`Presentation.unfoldOps_inlTerm`). The models of the presentation are the algebras of
{lit}`P`, each expanded by {name}`Geb.Definition.derivedAlg` ({lit}`Presentation.modelEquiv`).

## Main definitions

* {lit}`Presentation.ofDerived` — the presentation of derived operations.
* {lit}`Presentation.inlTerm`, {lit}`Presentation.unfoldOps` — the inclusion of terms of
  {lit}`P` and the unfolding of the new operations.
* {lit}`Presentation.unfoldCls` — the unfolding of a class.
* {lit}`Presentation.clsEquivBase` — the classes as the terms of {lit}`P`.
* {lit}`Presentation.modelEquiv` — the models as the algebras of {lit}`P`.

## Main statements

* {lit}`Presentation.satisfies_derivedAlg` — every algebra of {lit}`P`, expanded, is a model.
* {lit}`Presentation.eq_derivedAlg_of_satisfies` — every model is such an expansion.
* {lit}`Presentation.unfoldOps_src`, {lit}`Presentation.unfoldOps_inlTerm` — the unfolding
  coequalizes the endpoints and has the inclusion as a section.
* {lit}`Presentation.cls_inlTerm_unfoldOps`, {lit}`Presentation.eq_of_cls_inlTerm_eq` —
  eliminability and non-creativity.

## References

* {cite}`Suppes1957`, pp. 153–154, for the criteria of eliminability and non-creativity.
* {cite}`KellyPower1993`, for presentations as coequalizers of free monads.

## Tags

definition, definitional extension, eliminability, non-creativity, equational presentation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presentation

open PFunctor

universe uA uQ u v

variable {P : PFunctor.{uA, u}} {Q : PFunctor.{uQ, u}} (δ : Derived P Q) {Γ : Type u}
  {V : Type v}

/-- The free algebra of {lit}`P` on {lit}`Γ`: an operation applied to terms. -/
def freeAlg (P : PFunctor.{uA, u}) (Γ : Type u) : P.Obj (P.FreeM Γ) → P.FreeM Γ :=
  fun x ↦ .liftBind x.1 x.2

/-- Evaluation in the free algebra is substitution. -/
theorem eval_freeAlg {Δ : Type u} (σ : Δ → P.FreeM Γ) (t : P.FreeM Δ) :
    eval (freeAlg P Γ) σ t = t.bind σ := by
  refine FreeM.rec (motive := fun t ↦ eval (freeAlg P Γ) σ t = t.bind σ) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact congrArg (FreeM.liftBind a) (funext ih)

/-- Derived operations expand in the free algebra to themselves: the expansion of a term is
its value in the free algebra with the new operations read as their bodies. -/
theorem eval_derivedAlg_freeAlg {R : PFunctor.{uQ, u}} (d : Derived P R) (t : R.FreeM Γ) :
    eval (derivedAlg (freeAlg P Γ) d) pure t = expandOps d t := by
  rw [eval_expandOps, eval_freeAlg, FreeM.bind_pure]

/-- The terms of {lit}`P` among those of {lit}`sum P Q`. -/
abbrev inlTerm (Q : PFunctor.{uQ, u}) : P.FreeM Γ → (sum P Q).FreeM Γ := expandOps (inlOps Q)

/-- The presentation of derived operations over the signature they extend: each new operation,
applied to its variables, equals its body. -/
abbrev ofDerived : Presentation.{max uA uQ, uQ, u} (sum P Q) where
  E := Q
  lhs q := FreeM.lift (P := sum P Q) (.inr q)
  rhs q := inlTerm Q (δ q)

/-- The unfolding of the new operations: each operation of {lit}`P` to itself and each new
operation to its body. -/
abbrev unfoldOps : (sum P Q).FreeM Γ → P.FreeM Γ := expandOps (handler δ)

/-- An algebra of {lit}`sum P Q` restricted to the operations of {lit}`P`. -/
abbrev restrict (alg : (sum P Q).Obj V → V) : P.Obj V → V := derivedAlg alg (inlOps Q)

/-- Expanding an algebra of {lit}`P` and restricting it recovers it. -/
theorem restrict_derivedAlg (alg : P.Obj V → V) : restrict (derivedAlg alg (handler δ)) = alg :=
  funext fun ⟨_, _⟩ ↦ rfl

/-- Every algebra of {lit}`P`, each new operation read as its body, satisfies the presentation
of derived operations. -/
theorem satisfies_derivedAlg (alg : P.Obj V → V) :
    (ofDerived δ).Satisfies (derivedAlg alg (handler δ)) := by
  intro q σ
  change eval alg σ (δ q) = eval (derivedAlg alg (handler δ)) σ (expandOps (inlOps Q) (δ q))
  rw [← eval_expandOps]
  exact congrArg (fun alg' ↦ eval alg' σ (δ q)) (restrict_derivedAlg δ alg).symm

/-- Every model of the presentation of derived operations is the expansion of its restriction
to the operations of {lit}`P`. -/
theorem eq_derivedAlg_of_satisfies (alg : (sum P Q).Obj V → V)
    (h : (ofDerived δ).Satisfies alg) : alg = derivedAlg (restrict alg) (handler δ) := by
  funext x
  obtain ⟨a | q, k⟩ := x
  · rfl
  · exact (h q k).trans (eval_expandOps alg (inlOps Q) k (δ q)).symm

/-- The models of the presentation of derived operations are the algebras of {lit}`P`. -/
def modelEquiv : {alg : (sum P Q).Obj V → V // (ofDerived δ).Satisfies alg} ≃ (P.Obj V → V) where
  toFun alg := restrict alg.1
  invFun alg := ⟨derivedAlg alg (handler δ), satisfies_derivedAlg δ alg⟩
  left_inv alg := Subtype.ext (eq_derivedAlg_of_satisfies δ alg.1 alg.2).symm
  right_inv := restrict_derivedAlg δ

/-- The unfolding coequalizes the two endpoint maps. -/
theorem unfoldOps_src (w : (sum (sum P Q) Q).FreeM Γ) :
    unfoldOps δ ((ofDerived δ).src w) = unfoldOps δ ((ofDerived δ).tgt w) :=
  (eval_derivedAlg_freeAlg (handler δ) _).symm.trans
    (((ofDerived δ).eval_src _ (satisfies_derivedAlg δ _) pure w).trans
      (eval_derivedAlg_freeAlg (handler δ) _))

/-- The inclusion of the terms of {lit}`P` is a section of the unfolding. -/
@[simp] theorem unfoldOps_inlTerm (t : P.FreeM Γ) : unfoldOps δ (inlTerm Q t) = t := by
  refine FreeM.rec (motive := fun t ↦ unfoldOps δ (inlTerm Q t) = t) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact congrArg (FreeM.liftBind a) (funext ih)

/-- Each operation of {lit}`P` as itself, and each new operation as its equation. -/
def unfoldWitnessOps : Derived (sum (sum P Q) Q) (sum P Q)
  | .inl a => FreeM.lift (P := sum (sum P Q) Q) (.inl (.inl a))
  | .inr q => FreeM.lift (P := sum (sum P Q) Q) (.inr q)

/-- The witness from a term to its unfolding: each new operation read as the instance of its
equation. -/
def unfoldWitness : (sum P Q).FreeM Γ → (sum (sum P Q) Q).FreeM Γ := expandOps unfoldWitnessOps

/-- The source of the witness from a term to its unfolding is the term. -/
theorem src_unfoldWitness (t : (sum P Q).FreeM Γ) : (ofDerived δ).src (unfoldWitness t) = t := by
  refine FreeM.rec (motive := fun t ↦ (ofDerived δ).src (unfoldWitness t) = t) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  rcases a with a | q
  · exact congrArg (FreeM.liftBind (P := sum P Q) (.inl a)) (funext ih)
  · exact congrArg (FreeM.liftBind (P := sum P Q) (.inr q)) (funext ih)

/-- The target of the witness from a term to its unfolding is the unfolding. -/
theorem tgt_unfoldWitness (t : (sum P Q).FreeM Γ) :
    (ofDerived δ).tgt (unfoldWitness t) = inlTerm Q (unfoldOps δ t) := by
  refine FreeM.rec (motive := fun t ↦
    (ofDerived δ).tgt (unfoldWitness t) = inlTerm Q (unfoldOps δ t)) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  rcases a with a | q
  · exact congrArg (FreeM.liftBind (P := sum P Q) (.inl a)) (funext ih)
  · refine (congrArg (FreeM.bind (inlTerm Q (δ q))) (funext ih)).trans ?_
    exact (expandOps_bind (inlOps Q) (δ q) fun b ↦ unfoldOps δ (ts b)).symm

/-- Eliminability: every term has the class of the inclusion of its unfolding. -/
theorem cls_inlTerm_unfoldOps (t : (sum P Q).FreeM Γ) :
    (ofDerived δ).cls (inlTerm Q (unfoldOps δ t)) = (ofDerived δ).cls t := by
  rw [← tgt_unfoldWitness δ t, ← (ofDerived δ).cls_src, src_unfoldWitness]

/-- The unfolding of a class: its value in the terms of {lit}`P`, each new operation read as its
body. -/
def unfoldCls : (ofDerived δ).Cls Γ → P.FreeM Γ :=
  (ofDerived δ).lift (derivedAlg (freeAlg P Γ) (handler δ)) (satisfies_derivedAlg δ _) pure

/-- The unfolding of the class of a term is the unfolding of the term. -/
@[simp] theorem unfoldCls_cls (t : (sum P Q).FreeM Γ) :
    unfoldCls δ ((ofDerived δ).cls t) = unfoldOps δ t :=
  eval_derivedAlg_freeAlg (handler δ) t

/-- Non-creativity: terms of {lit}`P` with one class are equal. -/
theorem eq_of_cls_inlTerm_eq {s t : P.FreeM Γ}
    (h : (ofDerived δ).cls (inlTerm Q s) = (ofDerived δ).cls (inlTerm Q t)) : s = t := by
  simpa only [unfoldCls_cls, unfoldOps_inlTerm] using congrArg (unfoldCls δ) h

/-- The classes of the presentation of derived operations are the terms of {lit}`P`. -/
def clsEquivBase : (ofDerived δ).Cls Γ ≃ P.FreeM Γ where
  toFun := unfoldCls δ
  invFun t := (ofDerived δ).cls (inlTerm Q t)
  left_inv q := Quot.ind (β := fun q ↦ (ofDerived δ).cls (inlTerm Q (unfoldCls δ q)) = q)
    (fun t ↦ (congrArg (fun s ↦ (ofDerived δ).cls (inlTerm Q s)) (unfoldCls_cls δ t)).trans
      (cls_inlTerm_unfoldOps δ t)) q
  right_inv t := (unfoldCls_cls δ _).trans (unfoldOps_inlTerm δ t)

end Geb.Definition.Presentation

end
