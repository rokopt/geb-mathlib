/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Solution
public import Mathlib.Logic.Function.Coequalizer
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equational presentations with free-monad sides

An equational presentation over a polynomial signature {lit}`P` is a polynomial {lit}`E` of
equations, whose shapes name the equations and whose directions at an equation are its
variables, with two derived operations {lit}`lhs rhs : Derived P E`: the two sides of every
equation, terms of the free monad of {lit}`P` of any depth in the equation's variables.
Finitary monads are presented by operations and equations between derived operations, as
coequalizers of free monads {cite}`KellyPower1993`.

A witness of a presentation over variables {lit}`Γ` is a term of the free monad of the sum
{lit}`sum P E`: an operation of {lit}`P` in it is a congruence, an operation of {lit}`E` an
instance of an equation whose arguments are witnesses, and a variable a reflexivity. The two
endpoints of a witness are its expansions by two handlers, each sending every operation of
{lit}`P` to itself and every equation to one of its sides. The endpoint maps are thereby the
monad morphisms that the two handlers induce, so each commutes with substitution, and a term,
included among the witnesses, is a witness between itself and itself ({lit}`src_refl`,
{lit}`tgt_refl`).

The classes of terms, {lit}`Cls`, are the coequalizer of the two endpoint maps: a
{name}`Function.Coequalizer`, whose {name}`Quot` takes the equivalence relation the witnesses
generate. An algebra satisfies a presentation when the two sides of every equation receive
equal values at every assignment of its variables ({lit}`Satisfies`). It does exactly when it
interprets the two handlers alike ({lit}`derivedAlg_handler_eq_iff`), so by
{name}`Geb.Definition.eval_expandOps` the two endpoints of every witness have equal values in
it ({lit}`eval_src`), and evaluation in it descends to the classes ({lit}`lift`).

## Main definitions

* {lit}`sum` — the sum of two polynomial functors.
* {lit}`Presentation` — equations with the two sides of each.
* {lit}`handler`, {lit}`Presentation.src`, {lit}`Presentation.tgt` — the endpoint handlers and
  the endpoints of a witness.
* {lit}`Presentation.refl`, {lit}`Presentation.inst` — a term as a witness, and the instance of
  an equation at a substitution.
* {lit}`Presentation.Linked` — two terms are the endpoints of a witness.
* {lit}`Presentation.Cls`, {lit}`Presentation.cls` — the classes of terms and the class of a term.
* {lit}`Presentation.Satisfies` — an algebra satisfies the equations.
* {lit}`Presentation.lift` — the value of a class in an algebra satisfying the equations.

## Main statements

* {lit}`Presentation.src_refl`, {lit}`Presentation.tgt_refl` — the endpoints of a term as a
  witness.
* {lit}`Presentation.cls_bind_lhs` — the two sides of an equation, substituted alike, have one
  class.
* {lit}`Presentation.cls_eq_iff` — two terms have one class exactly when the witnesses relate
  them by the equivalence relation they generate.
* {lit}`Presentation.derivedAlg_handler_eq_iff` — satisfaction is the agreement of the two
  handlers' interpretations.
* {lit}`Presentation.satisfies_iff` — an algebra satisfies the equations exactly when it
  gives the two endpoints of every witness equal values.

## References

* {cite}`KellyPower1993`, for finitary monads presented by operations and equations.

## Tags

equational presentation, free monad, coequalizer, quotient, derived operation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition

open PFunctor

universe uA uE u v

/-- The sum of two polynomial functors: the shapes of either, each with its own directions. -/
abbrev sum (P : PFunctor.{uA, u}) (E : PFunctor.{uE, u}) : PFunctor.{max uA uE, u} :=
  ⟨P.A ⊕ E.A, Sum.elim P.B E.B⟩

variable {P : PFunctor.{uA, u}} {E : PFunctor.{uE, u}}

/-- An endpoint handler: each operation of {lit}`P` to itself, and each equation to the side
{lit}`side` assigns it. -/
def handler (side : Derived P E) : Derived P (sum P E)
  | .inl a => FreeM.lift a
  | .inr e => side e

/-- The operations of {lit}`P` among those of {lit}`sum P E`. -/
def inlOps (E : PFunctor.{uE, u}) : Derived (sum P E) P :=
  fun a ↦ FreeM.lift (P := sum P E) (.inl a)

/-- An equational presentation over the signature {lit}`P`: a polynomial of equations, whose
shapes name the equations and whose directions are their variables, and the two sides of each
equation, terms of the free monad of {lit}`P` in its variables. -/
structure Presentation (P : PFunctor.{uA, u}) : Type (max uA (uE + 1) (u + 1)) where
  /-- The equations, with their variables as directions. -/
  E : PFunctor.{uE, u}
  /-- The left side of each equation. -/
  lhs : Derived P E
  /-- The right side of each equation. -/
  rhs : Derived P E

namespace Presentation

variable (p : Presentation.{uA, uE, u} P) {Γ Δ : Type u} {V : Type v}

/-- The source of a witness: its expansion with each equation read as its left side. -/
def src : (sum P p.E).FreeM Γ → P.FreeM Γ := expandOps (handler p.lhs)

/-- The target of a witness: its expansion with each equation read as its right side. -/
def tgt : (sum P p.E).FreeM Γ → P.FreeM Γ := expandOps (handler p.rhs)

/-- A term as a witness: its operations as congruences, its variables as reflexivities. -/
def refl : P.FreeM Γ → (sum P p.E).FreeM Γ := expandOps (inlOps p.E)

/-- The source of a term as a witness is the term. -/
@[simp] theorem src_refl (t : P.FreeM Γ) : p.src (p.refl t) = t := by
  refine FreeM.rec (motive := fun t ↦ p.src (p.refl t) = t) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact congrArg (FreeM.liftBind a) (funext ih)

/-- The target of a term as a witness is the term. -/
@[simp] theorem tgt_refl (t : P.FreeM Γ) : p.tgt (p.refl t) = t := by
  refine FreeM.rec (motive := fun t ↦ p.tgt (p.refl t) = t) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact congrArg (FreeM.liftBind a) (funext ih)

/-- The instance of an equation at a substitution of terms for its variables. -/
def inst (e : p.E.A) (σ : p.E.B e → P.FreeM Γ) : (sum P p.E).FreeM Γ :=
  .liftBind (Sum.inr e : (sum P p.E).A) fun v ↦ p.refl (σ v)

/-- The source of an instance is the left side, substituted. -/
theorem src_inst (e : p.E.A) (σ : p.E.B e → P.FreeM Γ) : p.src (p.inst e σ) = (p.lhs e).bind σ :=
  congrArg (FreeM.bind (p.lhs e)) (funext fun v ↦ p.src_refl (σ v))

/-- The target of an instance is the right side, substituted. -/
theorem tgt_inst (e : p.E.A) (σ : p.E.B e → P.FreeM Γ) : p.tgt (p.inst e σ) = (p.rhs e).bind σ :=
  congrArg (FreeM.bind (p.rhs e)) (funext fun v ↦ p.tgt_refl (σ v))

/-- Two terms are linked when they are the endpoints of a witness. -/
def Linked (s t : P.FreeM Γ) : Prop := ∃ w, p.src w = s ∧ p.tgt w = t

/-- The classes of terms over {lit}`Γ`: the coequalizer of the two endpoint maps. -/
abbrev Cls (Γ : Type u) : Type (max uA u) := Function.Coequalizer (p.src (Γ := Γ)) p.tgt

/-- The class of a term. -/
abbrev cls (t : P.FreeM Γ) : p.Cls Γ := Function.Coequalizer.mk _ _ t

/-- The two endpoints of a witness have one class. -/
theorem cls_src (w : (sum P p.E).FreeM Γ) : p.cls (p.src w) = p.cls (p.tgt w) :=
  Function.Coequalizer.condition _ _ w

/-- The two sides of an equation, substituted alike, have one class. -/
theorem cls_bind_lhs (e : p.E.A) (σ : p.E.B e → P.FreeM Γ) :
    p.cls ((p.lhs e).bind σ) = p.cls ((p.rhs e).bind σ) := by
  rw [← src_inst, ← tgt_inst]
  exact p.cls_src _

/-- Two terms have one class exactly when the witnesses relate them by the equivalence relation
they generate. -/
theorem cls_eq_iff (s t : P.FreeM Γ) : p.cls s = p.cls t ↔ Relation.EqvGen p.Linked s t := by
  refine ⟨fun h ↦ Relation.EqvGen.mono ?_ _ _ (Quot.eqvGen_exact h),
    fun h ↦ Quot.eqvGen_sound (Relation.EqvGen.mono ?_ _ _ h)⟩
  · rintro _ _ ⟨w⟩
    exact ⟨w, rfl, rfl⟩
  · rintro _ _ ⟨w, rfl, rfl⟩
    exact ⟨w⟩

/-- An algebra satisfies a presentation when the two sides of each equation receive the same
value at every assignment of its variables. -/
def Satisfies (alg : P.Obj V → V) : Prop :=
  ∀ (e : p.E.A) (σ : p.E.B e → V), eval alg σ (p.lhs e) = eval alg σ (p.rhs e)

/-- An algebra satisfies a presentation exactly when it interprets the two endpoint handlers
alike. -/
theorem derivedAlg_handler_eq_iff (alg : P.Obj V → V) :
    derivedAlg alg (handler p.lhs) = derivedAlg alg (handler p.rhs) ↔ p.Satisfies alg := by
  refine ⟨fun h e σ ↦ congrFun h ⟨.inr e, σ⟩, fun h ↦ funext fun x ↦ ?_⟩
  obtain ⟨a | e, σ⟩ := x
  · rfl
  · exact h e σ

/-- In an algebra satisfying a presentation, the two endpoints of every witness have equal
values. -/
theorem eval_src (alg : P.Obj V → V) (h : p.Satisfies alg) (env : Γ → V)
    (w : (sum P p.E).FreeM Γ) : eval alg env (p.src w) = eval alg env (p.tgt w) := by
  rw [src, tgt, ← eval_expandOps, ← eval_expandOps, (p.derivedAlg_handler_eq_iff alg).mpr h]

/-- An algebra satisfies a presentation exactly when it gives the two endpoints of every
witness equal values. -/
theorem satisfies_iff (alg : P.Obj V → V) :
    p.Satisfies alg ↔ ∀ (Γ : Type u) (env : Γ → V) (w : (sum P p.E).FreeM Γ),
      eval alg env (p.src w) = eval alg env (p.tgt w) := by
  refine ⟨fun h _ ↦ p.eval_src alg h, fun h e σ ↦ ?_⟩
  have := h _ σ (p.inst e pure)
  rwa [src_inst, tgt_inst, FreeM.bind_pure, FreeM.bind_pure] at this

/-- The value of a class in an algebra satisfying the presentation, at an assignment of the
variables: the value of any term of the class. -/
def lift (alg : P.Obj V → V) (h : p.Satisfies alg) (env : Γ → V) : p.Cls Γ → V :=
  Function.Coequalizer.desc _ _ (eval alg env) (funext (p.eval_src alg h env))

/-- The value of the class of a term is the value of the term. -/
@[simp] theorem lift_cls (alg : P.Obj V → V) (h : p.Satisfies alg) (env : Γ → V)
    (t : P.FreeM Γ) : p.lift alg h env (p.cls t) = eval alg env t := rfl

end Presentation

end Geb.Definition

end
