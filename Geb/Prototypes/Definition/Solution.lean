/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equations that are definitions

A family of equations defines its unknowns, relative to a class of models, when it has exactly
one solution in every model of the class. The equations of an equation block
({name}`Geb.Definition.Block`) are of this kind for the class of all algebras when the block
is well founded, and derived operations ({name}`Geb.Definition.Derived`) are of this kind
always.

Derived operations interpret uniquely in every algebra, each defining equation stating the
value of its operation, and evaluating a term of defined operations agrees with evaluating its
expansion. This is the definitional extension of the signature: every algebra of the signature
expands to exactly one model of the defining equations, and expansion preserves meaning.

A block is well founded when the body at each export refers only to imports and to exports
below it in a well-founded relation. The restriction is a typing of the bodies, which range
over the imports and the exports below their own. Such a block has exactly one solution in
every algebra and environment, constructed and characterized by well-founded recursion on the
exports.

A guarded block, none of whose bodies is a bare reference to an export of the block, has
exactly one solution in each completely iterative algebra, the M-type among them
{cite}`MiliusMoss2009`; {name}`Geb.Definition.coalgebra_solution_unique` treats the flat case.
An unguarded block need not have one, or may have many
({lit}`x = x` holds of every value), and is a constraint on its models rather than a
definition.

## Main definitions

* {lit}`derivedAlg` interprets derived operations in an algebra.
* {lit}`WFBlock` is a block whose references are bounded by a relation.
* {lit}`WFBlock.toBlock` forgets the bound.

## Main statements

* {lit}`eval_expandOps` states that expansion preserves meaning.
* {lit}`WFBlock.isSolution_iff` restates the equations with the bound retained.
* {lit}`WFBlock.existsUnique_isSolution` gives each well-founded block exactly one solution.

## References

* {cite}`MiliusMoss2009`, Sections 3 and 6, for equation morphisms, their solutions and the
  guardedness condition.

## Tags

definition, definitional extension, equation morphism, well-founded recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition

open PFunctor

universe uA uA' u v

variable {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}} {Γ E : Type u} {V : Type v}

/-- The operations of {lit}`Q` interpreted in an algebra of {lit}`P` by evaluating their
defining bodies at their arguments. -/
def derivedAlg (alg : P.Obj V → V) (d : Derived P Q) : Q.Obj V → V :=
  fun x ↦ eval alg x.2 (d x.1)

/-- Expansion preserves meaning: evaluating a term of defined operations agrees with evaluating
its expansion. -/
theorem eval_expandOps (alg : P.Obj V → V) (d : Derived P Q) (env : Γ → V) (t : Q.FreeM Γ) :
    eval (derivedAlg alg d) env t = eval alg env (expandOps d t) := by
  refine FreeM.rec (motive := fun t ↦
    eval (derivedAlg alg d) env t = eval alg env (expandOps d t)) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  refine (congrArg (fun k ↦ eval alg k (d a)) (funext ih)).trans ?_
  exact (eval_bind alg env (d a) fun b ↦ expandOps d (ts b)).symm

/-- A well-founded block: the body at each export refers to imports and to the exports below
it in {lit}`r`. -/
abbrev WFBlock (P : PFunctor.{uA, u}) (Γ : Type u) {E : Type u} (r : E → E → Prop) :
    Type (max uA u) :=
  (i : E) → P.FreeM (Γ ⊕ {j // r j i})

namespace WFBlock

variable {r : E → E → Prop}

/-- The equations of a well-founded block, forgetting the bound on each body's references. -/
def toBlock (d : WFBlock P Γ r) : Block P Γ E :=
  fun i ↦ (d i).map (Sum.map id Subtype.val)

/-- A solution of a well-founded block, stated with each body's references bounded. -/
theorem isSolution_iff (alg : P.Obj V → V) (env : Γ → V) (d : WFBlock P Γ r) (v : E → V) :
    IsSolution alg env d.toBlock v ↔
      ∀ i, eval alg (Sum.elim env fun j : {j // r j i} ↦ v j) (d i) = v i := by
  simp only [IsSolution, toBlock, eval_map, Sum.elim_comp_map, Function.comp_id]
  rfl

/-- A well-founded block has exactly one solution in every algebra and environment. -/
theorem existsUnique_isSolution (hr : WellFounded r) (alg : P.Obj V → V) (env : Γ → V)
    (d : WFBlock P Γ r) : ∃! v, IsSolution alg env d.toBlock v := by
  simp only [isSolution_iff]
  let F : ∀ i, (∀ j, r j i → V) → V := fun i rec ↦
    eval alg (Sum.elim env fun j ↦ rec j.1 j.2) (d i)
  refine ⟨hr.fix F, fun i ↦ (hr.fix_eq F i).symm, fun w hw ↦ funext fun i ↦ ?_⟩
  refine hr.induction (C := fun i ↦ w i = hr.fix F i) i fun i ih ↦ ?_
  rw [← hw i, hr.fix_eq F i]
  exact congrArg (fun k ↦ eval alg (Sum.elim env k) (d i)) (funext fun j ↦ ih j.1 j.2)

end WFBlock

end Geb.Definition

end
