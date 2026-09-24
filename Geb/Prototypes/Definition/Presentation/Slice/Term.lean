/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Cslib.Foundations.Data.PFunctor.Free
public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Geb.Prototypes.Definition.Presentation.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Well-sorted terms of a slice polynomial endofunctor

A slice polynomial endofunctor {lit}`F` over {lit}`I` assigns each operation an output sort,
{lit}`F.q`, and each of its arguments an input sort, {lit}`F.r`
({name}`SlicePFunctor`). A term of the free monad of its underlying polynomial functor, over
variables {lit}`Γ` sorted by {lit}`γ : Γ → I`, has the sort of its root: the variable's, or the
output sort of the root operation ({lit}`Slice.sort`). It is well sorted when every argument of
every operation in it has the input sort the operation assigns that argument
({lit}`Slice.WellSorted`). The well-sorted terms of sort {lit}`i` are the terms of sort {lit}`i`
of the free monad of {lit}`F` in the slice over {lit}`I`, as the slice W-type is the well-sorted
subtype of the W-type of the underlying polynomial functor.

Substitution of well-sorted terms of the substituted sorts preserves well-sortedness and sort
({lit}`Slice.wellSorted_bind`), and so does the expansion of derived operations whose bodies are
well sorted ({lit}`Slice.wellSorted_expandOps`). The sum of two slice polynomial endofunctors has
the sum of their underlying polynomial functors as its own ({lit}`Slice.sum`), so the handlers of
{name}`Geb.Definition.handler` are well sorted when their sides are
({lit}`Slice.derivedSorted_handler`).

A well-sorted term evaluates in an algebra of {lit}`F` over {lit}`I`, at an assignment of the
variables lying over their sorts, to a value lying over the term's sort
({lit}`Slice.evalS`). The evaluation recurses through the dependent recursor of the free monad,
whose motive carries the well-sortedness of the term, since an algebra of {lit}`F` over
{lit}`I` applies only to arguments of the sorts the operation assigns. It commutes with
substitution ({lit}`Slice.evalS_bind`).

## Main definitions

* {lit}`Slice.sort`, {lit}`Slice.WellSorted` — the sort of a term, and its well-sortedness.
* {lit}`Slice.IsSorted`, {lit}`Slice.DerivedSorted` — well-sorted substitutions and derived
  operations.
* {lit}`Slice.sum` — the sum of two slice polynomial endofunctors.
* {lit}`Slice.Alg` — an algebra over {lit}`I`.
* {lit}`Slice.evalS` — the value of a well-sorted term.

## Main statements

* {lit}`Slice.wellSorted_bind`, {lit}`Slice.wellSorted_expandOps` — substitution and expansion
  preserve well-sortedness and sort.
* {lit}`Slice.derivedSorted_handler`, {lit}`Slice.derivedSorted_inlOps` — the handlers and the
  inclusion of operations are well sorted.
* {lit}`Slice.p_evalS` — the value of a term lies over its sort.
* {lit}`Slice.evalS_bind` — evaluation commutes with substitution.

## Implementation notes

{lit}`Slice.evalS` recurses through {name}`PFunctor.FreeM.rec`, whose executable code
{lit}`Geb.Cslib.Foundations.Data.PFunctor.Free` supplies.

## References

* {cite}`GambinoKock2013`, for polynomial functors between slices.

## Tags

slice polynomial functor, many-sorted term, free monad, well-sortedness, algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Slice

open PFunctor

universe uA uE uI u v

variable {I : Type uI}

section Term

variable {F : SlicePFunctor.{uA, u, uI, uI} I I} {Γ Δ : Type u}

/-- The sort of a term: that of its variable, or the output sort of its root operation. -/
def sort (γ : Γ → I) : F.toPFunctor.FreeM Γ → I
  | .pure x => γ x
  | .liftBind a _ => F.q a

/-- A term is well sorted when every argument of every operation in it has the input sort the
operation assigns that argument. -/
def WellSorted (γ : Γ → I) (t : F.toPFunctor.FreeM Γ) : Prop :=
  FreeM.rec (motive := fun _ ↦ Prop) (fun _ ↦ True)
    (fun a k ih ↦ ∀ b, sort γ (k b) = F.r ⟨a, b⟩ ∧ ih b) t

/-- An operation applied to terms is well sorted exactly when every argument has the input sort
of its place and is well sorted. -/
theorem wellSorted_liftBind_iff (γ : Γ → I) (a : F.A) (k : F.B a → F.toPFunctor.FreeM Γ) :
    WellSorted γ (.liftBind a k) ↔ ∀ b, sort γ (k b) = F.r ⟨a, b⟩ ∧ WellSorted γ (k b) :=
  Iff.rfl

/-- A substitution of terms for variables is well sorted when it substitutes for each variable
a well-sorted term of the variable's sort. -/
def IsSorted (γ : Γ → I) (δ : Δ → I) (σ : Γ → F.toPFunctor.FreeM Δ) : Prop :=
  ∀ x, WellSorted δ (σ x) ∧ sort δ (σ x) = γ x

/-- Substitution by a well-sorted substitution preserves well-sortedness and sort. -/
theorem wellSorted_bind {γ : Γ → I} {δ : Δ → I} {σ : Γ → F.toPFunctor.FreeM Δ}
    (hσ : IsSorted γ δ σ) (t : F.toPFunctor.FreeM Γ) (ht : WellSorted γ t) :
    WellSorted δ (t.bind σ) ∧ sort δ (t.bind σ) = sort γ t := by
  refine FreeM.rec (motive := fun t ↦
    WellSorted γ t → WellSorted δ (t.bind σ) ∧ sort δ (t.bind σ) = sort γ t)
    (fun x _ ↦ hσ x) ?_ t ht
  intro a k ih h
  exact ⟨fun b ↦ ⟨(ih b (h b).2).2.trans (h b).1, (ih b (h b).2).1⟩, rfl⟩

end Term

section Derived

variable {F : SlicePFunctor.{uA, u, uI, uI} I I} {Q : SlicePFunctor.{uE, u, uI, uI} I I}
  {Γ : Type u}

/-- Derived operations are well sorted when the body of each operation of {lit}`Q` is a
well-sorted term of its output sort, in its arguments sorted by their input sorts. -/
def DerivedSorted (d : Derived F.toPFunctor Q.toPFunctor) : Prop :=
  ∀ a, WellSorted (fun b ↦ Q.r ⟨a, b⟩) (d a) ∧ sort (fun b ↦ Q.r ⟨a, b⟩) (d a) = Q.q a

/-- Expanding well-sorted derived operations preserves well-sortedness and sort. -/
theorem wellSorted_expandOps {d : Derived F.toPFunctor Q.toPFunctor} (hd : DerivedSorted d)
    {γ : Γ → I} (t : Q.toPFunctor.FreeM Γ) (ht : WellSorted γ t) :
    WellSorted γ (expandOps d t) ∧ sort γ (expandOps d t) = sort γ t := by
  refine FreeM.rec (motive := fun t ↦
    WellSorted γ t → WellSorted γ (expandOps d t) ∧ sort γ (expandOps d t) = sort γ t)
    (fun _ _ ↦ ⟨trivial, rfl⟩) ?_ t ht
  intro a k ih h
  have hσ : IsSorted (fun b ↦ Q.r ⟨a, b⟩) γ fun b ↦ expandOps d (k b) := fun b ↦
    ⟨(ih b (h b).2).1, (ih b (h b).2).2.trans (h b).1⟩
  exact ⟨(wellSorted_bind hσ (d a) (hd a).1).1,
    (wellSorted_bind hσ (d a) (hd a).1).2.trans (hd a).2⟩

end Derived

section Sum

/-- The sum of two slice polynomial endofunctors: the sum of their underlying polynomial
functors, each shape keeping its sorts. -/
def sum (F : SlicePFunctor.{uA, u, uI, uI} I I) (E : SlicePFunctor.{uE, u, uI, uI} I I) :
    SlicePFunctor.{max uA uE, u, uI, uI} I I where
  toPFunctor := Geb.Definition.sum F.toPFunctor E.toPFunctor
  r x := match x with
    | ⟨.inl a, b⟩ => F.r ⟨a, b⟩
    | ⟨.inr e, b⟩ => E.r ⟨e, b⟩
  q := Sum.elim F.q E.q

variable {F : SlicePFunctor.{uA, u, uI, uI} I I} {E : SlicePFunctor.{uE, u, uI, uI} I I}

/-- The endpoint handler of well-sorted sides is well sorted. -/
theorem derivedSorted_handler {side : Derived F.toPFunctor E.toPFunctor}
    (hside : DerivedSorted side) :
    DerivedSorted (Q := sum F E) (handler (P := F.toPFunctor) side)
  | .inl _ => ⟨fun _ ↦ ⟨rfl, trivial⟩, rfl⟩
  | .inr e => hside e

/-- The inclusion of the operations of {lit}`F` among those of {lit}`sum F E` is well sorted. -/
theorem derivedSorted_inlOps : DerivedSorted (F := sum F E) (Q := F) (inlOps E.toPFunctor) :=
  fun _ ↦ ⟨fun _ ↦ ⟨rfl, trivial⟩, rfl⟩

end Sum

section Eval

/-- An algebra of a slice polynomial endofunctor over {lit}`I`: a carrier over {lit}`I` and a
structure map lying over {lit}`I`, in the form of the eliminator of the slice W-type. -/
structure Alg (F : SlicePFunctor.{uA, u, uI, uI} I I) : Type (max uA u uI (v + 1)) where
  /-- The carrier. -/
  carrier : Type v
  /-- The sort of each element of the carrier. -/
  p : carrier → I
  /-- The structure map, on operations applied to elements of the sorts of their arguments. -/
  g : F.toSliceDomPFunctor.Obj p → carrier
  /-- The structure map lies over {lit}`I`. -/
  hg : p ∘ g = F.obj p

variable {F : SlicePFunctor.{uA, u, uI, uI} I I} (A : Alg.{uA, uI, u, v} F) {Γ Δ : Type u}

/-- The value of a well-sorted term, with the proof that it lies over the term's sort. -/
def evalSub (γ : Γ → I) (env : Γ → A.carrier) (henv : A.p ∘ env = γ) :
    (t : F.toPFunctor.FreeM Γ) → WellSorted γ t → {y : A.carrier // A.p y = sort γ t} :=
  fun t ↦ FreeM.rec (motive := fun t ↦ WellSorted γ t → {y : A.carrier // A.p y = sort γ t})
    (fun x _ ↦ ⟨env x, congrFun henv x⟩)
    (fun a _ ih h ↦ ⟨A.g ⟨⟨a, fun b ↦ (ih b (h b).2).1⟩,
      funext fun b ↦ (ih b (h b).2).2.trans (h b).1⟩, congrFun A.hg _⟩) t

/-- The value of a well-sorted term in an algebra over {lit}`I`, at an assignment of the
variables lying over their sorts. -/
def evalS (γ : Γ → I) (env : Γ → A.carrier) (henv : A.p ∘ env = γ) (t : F.toPFunctor.FreeM Γ)
    (ht : WellSorted γ t) : A.carrier :=
  (evalSub A γ env henv t ht).1

variable {A}

/-- The value of a term lies over its sort. -/
theorem p_evalS (γ : Γ → I) (env : Γ → A.carrier) (henv : A.p ∘ env = γ)
    (t : F.toPFunctor.FreeM Γ) (ht : WellSorted γ t) : A.p (evalS A γ env henv t ht) = sort γ t :=
  (evalSub A γ env henv t ht).2

/-- The value of a variable is its assigned value. -/
theorem evalS_pure (γ : Γ → I) (env : Γ → A.carrier) (henv : A.p ∘ env = γ) (x : Γ)
    (h : WellSorted γ (.pure x)) : evalS A γ env henv (.pure x) h = env x := rfl

/-- The value of an operation applied to terms is the structure map applied to their values. -/
theorem evalS_liftBind (γ : Γ → I) (env : Γ → A.carrier) (henv : A.p ∘ env = γ) (a : F.A)
    (k : F.B a → F.toPFunctor.FreeM Γ) (h : WellSorted γ (.liftBind a k)) :
    evalS A γ env henv (.liftBind a k) h = A.g ⟨⟨a, fun b ↦ evalS A γ env henv (k b) (h b).2⟩,
      funext fun b ↦ (p_evalS γ env henv (k b) (h b).2).trans (h b).1⟩ := rfl

/-- The value of a term depends on the assignment only through its values. -/
theorem evalS_congr_env (γ : Γ → I) {env env' : Γ → A.carrier} (henv : A.p ∘ env = γ)
    (henv' : A.p ∘ env' = γ) (he : env = env') (t : F.toPFunctor.FreeM Γ)
    (ht : WellSorted γ t) : evalS A γ env henv t ht = evalS A γ env' henv' t ht := by
  subst he
  rfl

/-- Evaluation commutes with substitution: the value of a substituted term is the value of the
term, each variable assigned the value of its substituted term. -/
theorem evalS_bind {γ : Γ → I} {δ : Δ → I} {σ : Γ → F.toPFunctor.FreeM Δ} (hσ : IsSorted γ δ σ)
    (env : Δ → A.carrier) (henv : A.p ∘ env = δ) (t : F.toPFunctor.FreeM Γ)
    (ht : WellSorted γ t) :
    evalS A δ env henv (t.bind σ) (wellSorted_bind hσ t ht).1 =
      evalS A γ (fun x ↦ evalS A δ env henv (σ x) (hσ x).1)
        (funext fun x ↦ (p_evalS δ env henv (σ x) (hσ x).1).trans (hσ x).2) t ht := by
  refine FreeM.rec (motive := fun t ↦ ∀ ht : WellSorted γ t,
    evalS A δ env henv (t.bind σ) (wellSorted_bind hσ t ht).1 =
      evalS A γ (fun x ↦ evalS A δ env henv (σ x) (hσ x).1)
        (funext fun x ↦ (p_evalS δ env henv (σ x) (hσ x).1).trans (hσ x).2) t ht)
    (fun _ _ ↦ rfl) ?_ t ht
  intro a k ih h
  exact congrArg A.g (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦ ih b (h b).2))))

end Eval

end Geb.Definition.Slice

end
