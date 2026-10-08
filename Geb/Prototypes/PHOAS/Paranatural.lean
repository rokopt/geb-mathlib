/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Scoped
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Paranatural families for polynomial profunctors

The compatibility condition defining scoped terms is strong dinaturality from the
covariant representable {lit}`Hom(Γ, -)` to the pointwise free monad. For a covariant
source, ordinary dinaturality and strong dinaturality coincide, as in
{cite}`Neumann2023`, Definition 3 and Note 6.

For the polynomial profunctor itself, each compatible family chooses one operation
and, at each inner position, either a context variable or a bound variable.
The pointwise free monad cannot in general replace a scoped family: for the signature
consisting only of unary abstraction, the empty diagonal of the free monad is a
singleton, whereas closed scoped terms distinguish one abstraction from two.
Writing {lit}`H` for the context-extension node operator {lit}`BindingNode`, the one-layer
representation is {lit}`ScopedObj Γ ≃ H(Id)(Γ)`. For full expressions,
{lit}`Scoped.equivTerm` in {lit}`PHOAS.Term` gives a tree representation of the existing
{lit}`Scoped` family, which already targets the pointwise free monad.

## Main definitions

* {lit}`ScopedObj` is the family of paranatural transformations into the signature.
* {lit}`ScopedObj.equiv` gives its representation by variable selections.

## Main statements

* {lit}`ScopedObj.body_eq` reconstructs each continuation by substitution.
* {lit}`UnaryBinding.not_equiv_free_empty` excludes a pointwise free-monad formula for
  closed scoped terms, for every choice of the negative parameter.

## Implementation notes

The representation uses the context and binder arities in the universe over which
the families quantify. It imposes no finiteness assumption on the signature.
For the pointwise free monad, {lit}`Scoped.recOn` and {lit}`Scoped.fold_unique` in
{lit}`PHOAS.Initial` characterize the corresponding syntax with context extension.

## References

* {cite}`Neumann2023`

## Tags

PHOAS, paranatural transformation, polynomial profunctor, binding signature
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

open PFunctor

universe uA uB u

variable (P : PProfunctor.{uA, uB, u})

/-- Strong dinatural transformations from the covariant representable at a context
to the signature, with its contravariant argument ignored in the source. -/
abbrev ScopedObj (Γ : Type u) : Type (max uA uB (u + 1)) :=
  { t : (X : Type u) → (Γ → X) → P.Obj X X //
    ∀ {X Y : Type u} (f : X → Y) (env : Γ → X),
      P.dimap id f (t X env) = P.dimap f id (t Y (f ∘ env)) }

namespace ScopedObj

variable {P} {Γ : Type u}

/-- The operation position is independent of the interpretation of context variables. -/
theorem position_eq (t : P.ScopedObj Γ) (X : Type u) (env : Γ → X) :
    (t.val X env).fst = (t.val Γ id).fst :=
  (congrArg PFunctor.Obj.fst (t.property env id)).symm

/-- Express each component's continuation at the common operation position. -/
def body (t : P.ScopedObj Γ) (X : Type u) (env : Γ → X) :
    (P.B (t.val Γ id).fst).Obj X → X :=
  t.position_eq X env ▸ (t.val X env).snd

/-- The common position and its transported continuation reconstruct each component. -/
theorem mk_body (t : P.ScopedObj Γ) (X : Type u) (env : Γ → X) :
    PFunctor.Obj.mk (P := P.apply X) (t.val Γ id).fst (t.body X env) = t.val X env :=
  Sigma.ext (t.position_eq X env).symm
    (eqRec_heq (φ := fun a ↦ (P.B a).Obj X → X) (t.position_eq X env) _)

/-- The continuation is natural under simultaneous renaming of both environments. -/
theorem body_natural (t : P.ScopedObj Γ) {X Y : Type u} (f : X → Y)
    (env : Γ → X) (d : (P.B (t.val Γ id).fst).Obj X) :
    f (t.body X env d) = t.body Y (f ∘ env) ((P.B (t.val Γ id).fst).map f d) := by
  have h := t.property f env
  rw [← t.mk_body X env, ← t.mk_body Y (f ∘ env)] at h
  exact congrFun (sigma_mk_injective h) d

/-- Choose the variable returned at each inner position by supplying distinct variables
for the context and the binder arity. -/
def choices (t : P.ScopedObj Γ) (b : (P.B (t.val Γ id).fst).A) :
    Γ ⊕ (P.B (t.val Γ id).fst).B b :=
  t.body _ Sum.inl (.mk b Sum.inr)

/-- Every continuation substitutes its two environments into the selected variable. -/
theorem body_eq (t : P.ScopedObj Γ) (X : Type u) (env : Γ → X)
    (d : (P.B (t.val Γ id).fst).Obj X) :
    t.body X env d = Sum.elim env d.snd (t.choices d.fst) :=
  (t.body_natural (Sum.elim env d.snd) Sum.inl (.mk d.fst Sum.inr)).symm

/-- An operation and a choice of context or bound variable at each inner position
determine a paranatural family. -/
def ofChoices (a : P.A) (k : (b : (P.B a).A) → Γ ⊕ (P.B a).B b) : P.ScopedObj Γ :=
  ⟨fun _ env ↦ .mk a (fun d ↦ Sum.elim env d.snd (k d.fst)), by
    intro X Y f env
    apply congrArg (PFunctor.Obj.mk (P := P.apply X) a)
    funext d
    change f (Sum.elim env d.snd (k d.fst)) =
      Sum.elim (f ∘ env) (f ∘ d.snd) (k d.fst)
    cases k d.fst <;> rfl⟩

/-- Paranatural families into a polynomial signature are operations whose continuations
select context or bound variables. -/
def equiv : P.ScopedObj Γ ≃ P.BindingNode id Γ where
  toFun t := ⟨(t.val Γ id).fst, t.choices⟩
  invFun n := ofChoices n.1 n.2
  left_inv t := by
    apply Subtype.ext
    funext X env
    calc
      _ = PFunctor.Obj.mk (P := P.apply X) (t.val Γ id).fst (t.body X env) :=
        congrArg (PFunctor.Obj.mk (P := P.apply X) _) (funext fun d ↦ (t.body_eq X env d).symm)
      _ = _ := t.mk_body X env
  right_inv n := by
    rcases n with ⟨a, k⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    funext b
    change Sum.elim Sum.inl Sum.inr (k b) = k b
    cases k b <;> rfl

end ScopedObj

end Geb.PHOAS.PProfunctor

namespace Geb.PHOAS.UnaryBinding

open PFunctor PProfunctor

universe u v

/-- One operation with one child and one bound variable, interpreting {lit}`X → Y`. -/
def signature : PProfunctor.{0, 0, 0} :=
  ⟨PUnit, fun _ ↦ ⟨PUnit, fun _ ↦ PUnit⟩⟩

/-- The closed term {lit}`λ x. x`. -/
def identity : signature.Scoped.{0, 0, 0, 0, 0} PEmpty :=
  Scoped.node PUnit.unit (fun _ ↦ Scoped.var (.inr PUnit.unit))

/-- The closed term {lit}`λ x. λ y. x`. -/
def constant : signature.Scoped.{0, 0, 0, 0, 0} PEmpty :=
  Scoped.node PUnit.unit (fun _ ↦
    Scoped.node PUnit.unit (fun _ ↦ Scoped.var (.inl (.inr PUnit.unit))))

/-- Interpreting at the singleton distinguishes one abstraction from two abstractions. -/
theorem identity_ne_constant : identity ≠ constant := by
  intro h
  let observe (t : signature.Scoped.{0, 0, 0, 0, 0} PEmpty) : ℕ :=
    Free.fold (fun _ ↦ 0) (fun n ↦ n.snd (.mk PUnit.unit (fun _ ↦ PUnit.unit)) + 1)
      (t.val PUnit PEmpty.elim)
  have hn : (1 : ℕ) = 2 := congrArg observe h
  cases hn

/-- With no free variables, a raw unary term forces its input type to be empty,
so there is at most one such term for any fixed input type. -/
theorem free_empty_subsingleton (X : Type u) :
    Subsingleton (signature.Free X PEmpty.{v + 1}) := by
  constructor
  intro s t
  have hx (x : X) : PEmpty.{v + 1} :=
    Free.fold id (fun n ↦ n.snd (.mk PUnit.unit (fun _ ↦ x))) s
  cases s with
  | pure x => exact x.elim
  | liftBind a k =>
    cases t with
    | pure y => exact y.elim
    | liftBind b l =>
      exact congrArg (FreeM.liftBind (P := signature.apply X) PUnit.unit)
        (funext fun d ↦ (hx (d.snd PUnit.unit)).elim)

/-- Closed scoped syntax is not the pointwise free monad on an empty type of free
variables, for any choice of the negative parameter. -/
theorem not_equiv_free_empty (X : Type u) :
    ¬Nonempty (signature.Scoped.{0, 0, 0, 0, 0} PEmpty ≃
      signature.Free X PEmpty.{v + 1}) := by
  rintro ⟨e⟩
  exact identity_ne_constant (e.injective ((free_empty_subsingleton X).elim _ _))

end Geb.PHOAS.UnaryBinding
