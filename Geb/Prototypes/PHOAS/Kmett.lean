/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Term
public import Geb.Prototypes.PHOAS.Algebra
public import Mathlib.Logic.Function.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Kmett's application and abstraction signature

The signature from {cite}`Kmett2013` has interpretation {lit}`Y × Y ⊕ (X → Y)`.
Variables belong to its free monad, rather than to the signature. The closed examples
satisfy the end's wedge condition explicitly.

## Main definitions

* {lit}`signature` gives polynomial directions for application and abstraction.
* {lit}`appObj` and {lit}`lamObj` introduce the two operations.
* {lit}`exampleTerm` is the closed term binding two variables and applying them.
* {lit}`exampleTree` builds that full term using only extended-context tree constructors.

## Main statements

* {lit}`closedUnfold` identifies closed syntax with either two closed children or a
  one-variable scoped child.
* {lit}`exampleTree_toScoped` identifies the tree's interpretation with the PHOAS family.
* {lit}`no_fixed_point` excludes a diagonal fixed-point isomorphism on every type.
* {lit}`no_weakly_initial` and {lit}`no_weakly_terminal` exclude the nLab universal objects.
* {lit}`no_initial_algebra` also excludes initiality for the derived profunctor
  {lit}`H(X, Y) = P(Y, X) → Y`.

## Implementation notes

The categorical wrapper's {lit}`PProfunctor.scopedIsInitial` specializes to this signature,
characterizing the whole scoped family as an initial binding-signature algebra. The
closed end is its empty-context component. The diagonal obstructions concern different
categories of algebras and coalgebras.

## References

* {cite}`Kmett2013`

## Tags

PHOAS, lambda calculus, polynomial profunctor, diagonal argument
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.Kmett

open PFunctor PProfunctor

universe u v

/-- False denotes application, with constant two-element directions; true denotes
abstraction, whose direction polynomial is the identity. -/
def signature : PProfunctor.{0, 0, 0} where
  A := Bool
  B
    | false => ⟨Bool, fun _ ↦ PEmpty⟩
    | true => ⟨PUnit, fun _ ↦ PUnit⟩

/-- Application's two children, without recursive closure. -/
def appObj {X : Type u} {Y : Type v} (s t : Y) : signature.Obj X Y :=
  .mk false (fun d ↦ cond d.fst t s)

/-- Abstraction's child, parameterized by the bound-variable input. -/
def lamObj {X : Type u} {Y : Type v} (f : X → Y) : signature.Obj X Y :=
  .mk true (fun d ↦ f (d.snd PUnit.unit))

/-- Project an abstraction's function; an application projects its first child constantly. -/
def unlam {X : Type u} {Y : Type v} : signature.Obj X Y → X → Y
  | ⟨false, k⟩, _ => k (.mk false PEmpty.elim)
  | ⟨true, k⟩, x => k (.mk PUnit.unit (fun _ ↦ x))

/-- The function summand is a retract of the interpretation. -/
@[simp] theorem unlam_lamObj {X : Type u} {Y : Type v} (f : X → Y) :
    unlam (lamObj f) = f := rfl

/-- The polynomial interpretation is the application pair plus the abstraction function. -/
def objEquiv (X : Type u) (Y : Type v) : signature.Obj X Y ≃ ((Y × Y) ⊕ (X → Y)) where
  toFun := fun
    | ⟨false, k⟩ => .inl (k (.mk false PEmpty.elim), k (.mk true PEmpty.elim))
    | ⟨true, k⟩ => .inr (fun x ↦ k (.mk PUnit.unit (fun _ ↦ x)))
  invFun := Sum.elim (fun t ↦ appObj t.1 t.2) lamObj
  left_inv := by
    rintro ⟨a, k⟩
    cases a
    · apply congrArg (PFunctor.Obj.mk (P := signature.apply X) false)
      funext ⟨b, env⟩
      have h : env = PEmpty.elim := funext fun x ↦ x.elim
      subst env
      cases b <;> rfl
    · rfl
  right_inv := by rintro (⟨s, t⟩ | f) <;> rfl

/-- Application in the pointwise free monad. -/
def app {X : Type u} {Y : Type v} (s t : signature.Free X Y) : signature.Free X Y :=
  .liftBind false (fun d ↦ cond d.fst t s)

/-- Abstraction binds an input variable while the free-variable type remains separate. -/
def lam {X : Type u} {Y : Type v} (f : X → signature.Free X Y) : signature.Free X Y :=
  .liftBind true (fun d ↦ f (d.snd PUnit.unit))

/-- Output renaming distributes through application. -/
@[simp] theorem map_app {X : Type u} {Y Z : Type v} (f : Y → Z)
    (s t : signature.Free X Y) : (app s t).map f = app (s.map f) (t.map f) := by
  apply congrArg (FreeM.liftBind (P := signature.apply X) false)
  funext d
  change (cond d.fst t s).map f = cond d.fst (t.map f) (s.map f)
  cases d.fst <;> rfl

/-- Output renaming distributes through abstraction. -/
@[simp] theorem map_lam {X : Type u} {Y Z : Type v} (f : Y → Z)
    (k : X → signature.Free X Y) : (lam k).map f = lam (fun x ↦ (k x).map f) := rfl

/-- Input renaming distributes through application. -/
@[simp] theorem comap_app {X X' : Type u} {Y : Type v} (f : X' → X)
    (s t : signature.Free X Y) : Free.comap f (app s t) =
      app (Free.comap f s) (Free.comap f t) := by
  apply congrArg (FreeM.liftBind (P := signature.apply X') false)
  funext d
  change Free.comap f (cond d.fst t s) = cond d.fst (Free.comap f t) (Free.comap f s)
  cases d.fst <;> rfl

/-- Input renaming precomposes the bound-variable input of abstraction. -/
@[simp] theorem comap_lam {X X' : Type u} {Y : Type v} (f : X' → X)
    (k : X → signature.Free X Y) :
    Free.comap f (lam k) = lam (fun x ↦ Free.comap f (k (f x))) := rfl

/-- The closed identity term is a compatible family. -/
def identity : signature.End.{0, 0, 0, u} :=
  End.mk (fun _ ↦ lam FreeM.pure) (by intros; rfl)

/-- Kmett's example, binding two variables and applying the first to the second. -/
def exampleTerm : signature.End.{0, 0, 0, u} :=
  End.mk (fun _ ↦ lam (fun x ↦ lam (fun y ↦ app (.pure x) (.pure y)))) (by
    intro X Y f
    simp only [map_lam, map_app, comap_lam, comap_app]
    rfl)

/-- The full expression {lit}`λ x. λ y. x y`, built without a compatibility proof. -/
def exampleTree : signature.Term PEmpty :=
  Term.node true (fun _ ↦
    Term.node true (fun _ ↦
      Term.node false (fun b ↦
        Term.var (.inl (cond b (.inr PUnit.unit) (.inl (.inr PUnit.unit)))))))

/-- The tree representation gives the same full expression as the explicit PHOAS family. -/
theorem exampleTree_toScoped : Scoped.emptyEquivEnd exampleTree.toScoped = exampleTerm := by
  apply Subtype.ext
  funext X
  apply congrArg (FreeM.liftBind (P := signature.apply X) true)
  funext x
  apply congrArg (FreeM.liftBind (P := signature.apply X) true)
  funext y
  apply congrArg (FreeM.liftBind (P := signature.apply X) false)
  funext d
  cases d.fst <;> rfl

/-- A fold counting application and abstraction nodes, instantiating inputs at zero. -/
def countAlgebra : signature.Obj ℕ ℕ → ℕ
  | ⟨false, k⟩ => k (.mk false PEmpty.elim) + k (.mk true PEmpty.elim) + 1
  | ⟨true, k⟩ => k (.mk PUnit.unit (fun _ ↦ 0)) + 1

/-- The two abstractions and the application in Kmett's example are interpreted. -/
theorem iter_exampleTerm : End.iter countAlgebra exampleTerm = 3 := rfl

/-- Kmett's closed syntax unfolds into two closed children for application, or one
one-variable scoped child for abstraction. -/
def closedUnfold : signature.End.{0, 0, 0, u} ≃
    ((signature.End.{0, 0, 0, u} × signature.End.{0, 0, 0, u}) ⊕
      signature.Scoped.{0, 0, 0, u, 0} PUnit) :=
  End.unfoldScoped.trans
    { toFun := fun
        | ⟨false, k⟩ => .inl (Scoped.emptyEquivEnd (k false), Scoped.emptyEquivEnd (k true))
        | ⟨true, k⟩ => .inr (k PUnit.unit)
      invFun := fun
        | .inl (s, t) => ⟨false, fun b ↦ Scoped.emptyEquivEnd.symm (cond b t s)⟩
        | .inr k => ⟨true, fun _ ↦ k⟩
      left_inv := by
        rintro ⟨a, k⟩
        cases a
        · dsimp only
          refine Sigma.ext (by rfl) ?_
          apply heq_of_eq
          funext b
          cases b <;> exact Scoped.emptyEquivEnd.symm_apply_apply _
        · rfl
      right_inv := by
        rintro (⟨s, t⟩ | k)
        · simp only [Bool.cond_false, Bool.cond_true, Equiv.apply_symm_apply]
        · rfl }

/-- Kmett's polynomial profunctor has no diagonal fixed point on any type. The function
summand and the distinguishable application constructor give a diagonal contradiction. -/
theorem no_fixed_point (X : Type u) : ¬Nonempty (signature.Obj X X ≃ X) := by
  rintro ⟨e⟩
  let b : X := e (lamObj id)
  let a : X := e (appObj b b)
  let flip : X → X := fun x ↦ cond (e.symm x).fst a b
  have ha : (e.symm a).fst = false :=
    congrArg PFunctor.Obj.fst (e.symm_apply_apply (appObj b b))
  have hb : (e.symm b).fst = true :=
    congrArg PFunctor.Obj.fst (e.symm_apply_apply (lamObj id))
  have hn : ∀ x, flip x ≠ x := by
    intro x h
    have he := congrArg (fun y ↦ (e.symm y).fst) h
    cases hx : (e.symm x).fst <;> simp [flip, hx, ha, hb] at he
  have hs : Function.Surjective (fun x ↦ unlam (e.symm x)) := by
    intro f
    exact ⟨e (lamObj f), by simp⟩
  obtain ⟨x, hx⟩ := Function.exists_fixed_point_of_surjective _ hs flip
  exact hn x hx

/-- The end of the free monad is in particular not a diagonal fixed point. -/
theorem end_not_fixed_point :
    let E := signature.End.{0, 0, 0, u}
    ¬Nonempty (signature.Obj E E ≃ E) :=
  no_fixed_point _

/-- No diagonal element of this signature is even weakly initial in the nLab sense. -/
theorem no_weakly_initial (s : signature.Diagonal.{0, 0, 0, u}) :
    ¬(∀ t : signature.Diagonal.{0, 0, 0, u}, Nonempty (Diagonal.Hom s t)) := by
  intro h
  exact Bool.false_ne_true (Diagonal.positions_eq_of_weakly_initial s h false true)

/-- No diagonal element of this signature is even weakly terminal. -/
theorem no_weakly_terminal (s : signature.Diagonal.{0, 0, 0, u}) :
    ¬(∀ t : signature.Diagonal.{0, 0, 0, u}, Nonempty (Diagonal.Hom t s)) := by
  intro h
  exact Bool.false_ne_true (Diagonal.positions_eq_of_weakly_terminal s h false true)

/-- Select one inner position for each operation, as required by the tag construction. -/
def chooseInner : (a : signature.A) → (signature.B a).A
  | false => false
  | true => PUnit.unit

/-- The derived profunctor has no initial algebra either. Abstraction of the identity
supplies a point of every algebra, and the two tag inclusions violate uniqueness. -/
theorem no_initial_algebra (s : signature.Algebra.{0, 0, 0, u}) :
    ¬(∀ t : signature.Algebra.{0, 0, 0, u}, Nonempty (Unique (Algebra.Hom s t))) :=
  Algebra.not_initial_of_point chooseInner s (s.2 (lamObj id))

end Geb.PHOAS.Kmett
