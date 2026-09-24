/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Basic
public import Geb.Prototypes.FiniteChoice
public import Mathlib.Data.Fintype.Quotient
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The free model of a finitary presentation

For a presentation ({name}`Geb.Definition.Presentation`) whose operations and equations have
finitely many arguments and variables, enumerated by {name}`FinEnum`, the classes of terms over
{lit}`Γ` form an algebra of the signature ({lit}`Presentation.clsAlg`) that satisfies the
equations ({lit}`Presentation.satisfies_clsAlg`), and it is the free one on {lit}`Γ`: for every
algebra satisfying the equations and every assignment of {lit}`Γ`, the value of classes
({name}`Geb.Definition.Presentation.lift`) is the unique morphism of algebras extending the
assignment ({lit}`Presentation.existsUnique_lift`). At the empty {lit}`Γ` it is the initial
algebra satisfying the equations.

An operation applies to classes through representatives chosen by
{name}`Quotient.listChoice` along an enumeration of its arguments ({lit}`Presentation.op`).
It respects classes because the witnesses are closed under the operations: an operation applied
to reflexivities and one witness is a witness, and replacing the arguments one at a time
({name}`GebProto.eqvGen_of_update`) passes to the equivalence relation the witnesses generate
({lit}`Presentation.cls_liftBind_congr`).

## Main definitions

* {lit}`Presentation.op` — an operation applied to classes.
* {lit}`Presentation.clsAlg` — the algebra of classes.

## Main statements

* {lit}`Presentation.cls_liftBind_congr` — the operations respect classes.
* {lit}`Presentation.op_cls` — an operation applied to the classes of terms.
* {lit}`Presentation.eval_clsAlg` — the value of a term in the classes is the class of the term
  substituted.
* {lit}`Presentation.satisfies_clsAlg` — the classes satisfy the equations.
* {lit}`Presentation.lift_op` — the value of classes is a morphism of algebras.
* {lit}`Presentation.eq_lift`, {lit}`Presentation.existsUnique_lift` — it is the only one
  extending the assignment.

## Implementation notes

The finiteness of the arguments is used twice: to choose representatives for the arguments of
an operation, and for the variables of an equation when showing that the classes satisfy it.
mathlib's {lit}`Quotient.finChoice` depends on {lit}`Classical.choice`;
{name}`Quotient.listChoice` and {name}`GebProto.exists_forall_of_finEnum` do not.

## References

* {cite}`KellyPower1993`, for finitary monads presented by operations and equations.

## Tags

equational presentation, free algebra, initial algebra, quotient, finite choice
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presentation

open PFunctor GebProto

universe uA uE u v

variable {P : PFunctor.{uA, u}} (p : Presentation.{uA, uE, u} P) {Γ Δ : Type u} {V : Type v}

/-- An operation applied to reflexivities and one witness is a witness: replacing one argument
of an operation by a linked term links the applications. -/
theorem linked_liftBind_update (a : P.A) [DecidableEq (P.B a)] (ts : P.B a → P.FreeM Γ)
    (b : P.B a) {y : P.FreeM Γ} (h : p.Linked (ts b) y) :
    p.Linked (.liftBind a ts) (.liftBind a (Function.update ts b y)) := by
  obtain ⟨w, hs, ht⟩ := h
  refine ⟨FreeM.liftBind (P := sum P p.E) (.inl a)
      (Function.update (fun b ↦ p.refl (ts b)) b w : P.B a → (sum P p.E).FreeM Γ),
    congrArg (FreeM.liftBind a) (funext fun b' ↦ ?_),
    congrArg (FreeM.liftBind a) (funext fun b' ↦ ?_)⟩
  · change p.src (Function.update (fun b ↦ p.refl (ts b)) b w b') = ts b'
    by_cases hb : b' = b
    · subst hb
      rw [Function.update_self]
      exact hs
    · rw [Function.update_of_ne hb]
      exact p.src_refl (ts b')
  · change p.tgt (Function.update (fun b ↦ p.refl (ts b)) b w b') = Function.update ts b y b'
    by_cases hb : b' = b
    · subst hb
      rw [Function.update_self, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
      exact p.tgt_refl (ts b')

/-- The operations respect classes: arguments with equal classes give applications with equal
classes. -/
theorem cls_liftBind_congr (a : P.A) [FinEnum (P.B a)] {ts ts' : P.B a → P.FreeM Γ}
    (h : ∀ b, p.cls (ts b) = p.cls (ts' b)) : p.cls (.liftBind a ts) = p.cls (.liftBind a ts') :=
  (p.cls_eq_iff _ _).mpr (eqvGen_of_update (r := fun _ ↦ p.Linked) (R := p.Linked)
    (fun ts : P.B a → P.FreeM Γ ↦ FreeM.liftBind a ts)
    (fun ts b _ hy ↦ p.linked_liftBind_update a ts b hy) fun b ↦ (p.cls_eq_iff _ _).mp (h b))

/-- The kernel of the class map: two terms with one class. -/
abbrev kerSetoid (Γ : Type u) : Setoid (P.FreeM Γ) where
  r s t := p.cls s = p.cls t
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- A class as a class of the kernel of the class map. -/
def toKer : p.Cls Γ → Quotient (p.kerSetoid Γ) :=
  Quot.lift (Quotient.mk _) fun _ _ r ↦ Quotient.sound (Quot.sound r)

/-- An operation applied to classes: the class of its application to representatives, chosen
through {name}`Quotient.listChoice` along an enumeration of its arguments. -/
def op (a : P.A) [FinEnum (P.B a)] (f : P.B a → p.Cls Γ) : p.Cls Γ :=
  letI : Setoid (P.FreeM Γ) := p.kerSetoid Γ
  Quotient.lift (s := piSetoid)
    (fun g : (b : P.B a) → b ∈ FinEnum.toList (P.B a) → P.FreeM Γ ↦
      p.cls (.liftBind a fun b ↦ g b (FinEnum.mem_toList b)))
    (fun g g' hgg ↦ p.cls_liftBind_congr a fun b ↦
      (show ∀ hb : b ∈ FinEnum.toList (P.B a), p.cls (g b hb) = p.cls (g' b hb) from hgg b)
        (FinEnum.mem_toList b))
    (Quotient.listChoice fun b _ ↦ p.toKer (f b))

/-- An operation applied to the classes of terms is the class of its application to the
terms. -/
theorem op_cls (a : P.A) [FinEnum (P.B a)] (ts : P.B a → P.FreeM Γ) :
    p.op a (fun b ↦ p.cls (ts b)) = p.cls (.liftBind a ts) :=
  letI : Setoid (P.FreeM Γ) := p.kerSetoid Γ
  congrArg (Quotient.lift (s := piSetoid) _ _) (Quotient.listChoice_mk fun b _ ↦ ts b)

/-- Every finite family of classes is the family of classes of a family of terms. -/
theorem exists_cls {ι : Type u} [FinEnum ι] (f : ι → p.Cls Γ) :
    ∃ ts : ι → P.FreeM Γ, ∀ i, p.cls (ts i) = f i :=
  exists_forall_of_finEnum fun i ↦ Function.Coequalizer.mk_surjective _ _ (f i)

variable [∀ a, FinEnum (P.B a)]

/-- The algebra of classes: an operation applied to classes. -/
def clsAlg (Γ : Type u) : P.Obj (p.Cls Γ) → p.Cls Γ := fun x ↦ p.op x.1 x.2

/-- The value of a term in the classes, its variables assigned the classes of terms, is the
class of the term with those terms substituted. -/
theorem eval_clsAlg (σ : Δ → P.FreeM Γ) (t : P.FreeM Δ) :
    eval (p.clsAlg Γ) (fun x ↦ p.cls (σ x)) t = p.cls (t.bind σ) := by
  refine FreeM.rec (motive := fun t ↦
    eval (p.clsAlg Γ) (fun x ↦ p.cls (σ x)) t = p.cls (t.bind σ)) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact (congrArg (p.op a) (funext ih)).trans (p.op_cls a _)

/-- The classes satisfy the equations: an equation's instance at representatives of the
variables relates its two sides. -/
theorem satisfies_clsAlg [∀ e, FinEnum (p.E.B e)] : p.Satisfies (p.clsAlg Γ) := by
  intro e ρ
  obtain ⟨ts, hts⟩ := p.exists_cls ρ
  obtain rfl : ρ = fun v ↦ p.cls (ts v) := (funext hts).symm
  rw [eval_clsAlg, eval_clsAlg]
  exact p.cls_bind_lhs e ts

variable {alg : P.Obj V → V} (h : p.Satisfies alg) (env : Γ → V)

/-- The value of classes is a morphism of algebras. -/
theorem lift_op (a : P.A) (f : P.B a → p.Cls Γ) :
    p.lift alg h env (p.op a f) = alg ⟨a, fun b ↦ p.lift alg h env (f b)⟩ := by
  obtain ⟨ts, hts⟩ := p.exists_cls f
  obtain rfl : f = fun b ↦ p.cls (ts b) := (funext hts).symm
  rw [op_cls]
  rfl

/-- The value of classes is the only morphism of algebras extending the assignment: a morphism
of algebras agrees with it on the class of every term, by induction on the term. -/
theorem eq_lift (g : p.Cls Γ → V) (hg : ∀ a f, g (p.op a f) = alg ⟨a, fun b ↦ g (f b)⟩)
    (henv : ∀ x, g (p.cls (.pure x)) = env x) (q : p.Cls Γ) : g q = p.lift alg h env q := by
  refine Quot.ind (β := fun q ↦ g q = p.lift alg h env q) (fun t ↦ ?_) q
  refine FreeM.rec (motive := fun t ↦ g (p.cls t) = p.lift alg h env (p.cls t)) henv ?_ t
  intro a ts ih
  rw [← op_cls, hg, p.lift_op h env]
  exact congrArg (fun k ↦ alg ⟨a, k⟩) (funext ih)

include h in
/-- The classes over {lit}`Γ` are the free algebra satisfying the equations on {lit}`Γ`: every
assignment of {lit}`Γ` in an algebra satisfying them extends to exactly one morphism of
algebras. -/
theorem existsUnique_lift :
    ∃! g : p.Cls Γ → V, (∀ a f, g (p.op a f) = alg ⟨a, fun b ↦ g (f b)⟩) ∧
      ∀ x, g (p.cls (.pure x)) = env x :=
  ⟨p.lift alg h env, ⟨p.lift_op h env, fun _ ↦ rfl⟩,
    fun g hg ↦ funext (p.eq_lift h env g hg.1 hg.2)⟩

end Geb.Definition.Presentation

end
