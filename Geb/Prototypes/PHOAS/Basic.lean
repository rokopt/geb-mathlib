/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Polynomial profunctors and parametric higher-order syntax

A polynomial profunctor has a type of positions and a polynomial functor of directions
at each position. Interpreting the directions at the negative parameter gives an ordinary
polynomial functor in the positive parameter. Its free monad represents syntax with
separate types for bound-variable inputs and free-variable outputs.

## Main definitions

* {lit}`PProfunctor` specifies polynomial directions at each position.
* {lit}`PProfunctor.Free` is the pointwise free monad.
* {lit}`PProfunctor.End` consists of diagonal families satisfying the wedge condition.
* {lit}`PProfunctor.Diagonal` is the nLab's one-object profunctor algebra.

## Main statements

* {lit}`Free.unfold` gives the fixed-point equation with the negative parameter held fixed.
* {lit}`Free.fold_unique` gives the corresponding initial-algebra universal property.
* {lit}`End.unfold` recovers a uniform operation and its coherent family of children.
* {lit}`Diagonal.positions_eq_of_weakly_initial` and its terminal counterpart obstruct
  initial and terminal diagonal elements when the signature has distinct positions.

## Implementation notes

Ends quantify over one specified universe of types; their carriers live in a higher
universe. The core uses explicit compatible families, and the categorical companion
identifies these with mathlib's explicit end. No relational parametricity axiom is used.

## References

* {cite}`Kmett2013`
* {cite}`NLabProfunctorAlgebra`

## Tags

polynomial profunctor, free monad, end, higher-order abstract syntax
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS

open PFunctor

universe uA uB uC u v w z

/-- Positions with polynomial directions. The interpretation at {lit}`X, Y` is
{lit}`Σ a, (B a).Obj X → Y`. -/
@[ext]
structure PProfunctor : Type (max (uA + 1) (uB + 1) (uC + 1)) where
  /-- The operation positions. -/
  A : Type uA
  /-- The polynomial of directions at each position. -/
  B : A → PFunctor.{uB, uC}

namespace PProfunctor

variable (P : PProfunctor.{uA, uB, uC})

/-- Fixing the negative parameter produces an ordinary polynomial functor. -/
def apply (X : Type u) : PFunctor.{uA, max uB uC u} := ⟨P.A, fun a ↦ (P.B a).Obj X⟩

/-- The interpretation, contravariant in its first argument and covariant in its second. -/
abbrev Obj (X : Type u) (Y : Type v) : Type (max uA uB uC u v) := (P.apply X).Obj Y

/-- Change both parameters by mapping directions and results. -/
def dimap {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
    (f : X' → X) (g : Y → Y') (t : P.Obj X Y) : P.Obj X' Y' :=
  .mk t.fst (g ∘ t.snd ∘ (P.B t.fst).map f)

/-- Identity maps leave the interpretation unchanged. -/
@[simp] theorem dimap_id {X : Type u} {Y : Type v} (t : P.Obj X Y) :
    P.dimap id id t = t := rfl

/-- A diagonal element in the one-object sense of {cite}`NLabProfunctorAlgebra`.
The structure is an element of the profunctor, rather than a map out of it. -/
abbrev Diagonal : Type (max uA uB uC (u + 1)) := (X : Type u) × P.Obj X X

namespace Diagonal

variable {P}

/-- A morphism of diagonal elements satisfies the profunctor compatibility equation. -/
abbrev Hom (s : P.Diagonal.{uA, uB, uC, u}) (t : P.Diagonal.{uA, uB, uC, v}) :=
  { f : s.1 → t.1 // P.dimap id f s.2 = P.dimap f id t.2 }

/-- Every diagonal morphism preserves the outer position. -/
theorem position_eq {s : P.Diagonal.{uA, uB, uC, u}}
    {t : P.Diagonal.{uA, uB, uC, v}} (f : Hom s t) : s.2.fst = t.2.fst :=
  congrArg PFunctor.Obj.fst f.property

/-- Each position supplies a diagonal element with a one-point carrier. -/
def point (a : P.A) : P.Diagonal.{uA, uB, uC, u} :=
  ⟨PUnit, .mk a (fun _ ↦ PUnit.unit)⟩

/-- A weakly initial diagonal element forces all positions to be equal. -/
theorem positions_eq_of_weakly_initial (s : P.Diagonal.{uA, uB, uC, u})
    (h : ∀ t : P.Diagonal.{uA, uB, uC, u}, Nonempty (Hom s t)) (a b : P.A) : a = b := by
  obtain ⟨fa⟩ := h (point a)
  obtain ⟨fb⟩ := h (point b)
  exact (position_eq fa).symm.trans (position_eq fb)

/-- A weakly terminal diagonal element also forces all positions to be equal. -/
theorem positions_eq_of_weakly_terminal (s : P.Diagonal.{uA, uB, uC, u})
    (h : ∀ t : P.Diagonal.{uA, uB, uC, u}, Nonempty (Hom t s)) (a b : P.A) : a = b := by
  obtain ⟨fa⟩ := h (point a)
  obtain ⟨fb⟩ := h (point b)
  exact (position_eq fa).trans (position_eq fb).symm

end Diagonal

/-- The pointwise free monad, using CSLib's polynomial free monad. -/
abbrev Free (X : Type u) (Y : Type v) : Type (max uA uB uC u v) := (P.apply X).FreeM Y

namespace Free

variable {P} {X : Type u} {Y : Type v} {Z : Type w}

/-- Observe whether a term is a variable or an operation, retaining only its position. -/
def root (t : P.Free X Y) : Option P.A :=
  FreeM.casesOn t (fun _ ↦ none) (fun a _ ↦ some a)

/-- Recover the children when the root is a specified operation position. -/
def childrenAt (a : P.A) (t : P.Free X Y) (h : root t = some a) :
    (P.B a).Obj X → P.Free X Y := by
  cases t with
  | pure y => cases h
  | liftBind b k => exact (Option.some.inj h) ▸ k

/-- Reconstructing an operation from its recovered children returns the original term. -/
theorem liftBind_childrenAt (a : P.A) (t : P.Free X Y) (h : root t = some a) :
    FreeM.liftBind a (childrenAt a t h) = t := by
  cases t with
  | pure y => cases h
  | liftBind b k =>
    cases Option.some.inj h
    rfl

/-- Children at a fixed operation position are determined by their constructed term. -/
theorem liftBind_injective (a : P.A) :
    Function.Injective (FreeM.liftBind (P := P.apply X) (α := Y) a) := by
  intro k l h
  obtain ⟨ha, hk⟩ := (FreeM.liftBind_inj (P := P.apply X) a a k l).mp h
  exact hk

/-- The genuine fixed-point equation holds with the negative parameter fixed and with
the free-variable summand retained. -/
def unfold : P.Free X Y ≃ (Y ⊕ P.Obj X (P.Free X Y)) where
  toFun t := FreeM.casesOn t Sum.inl (fun a k ↦ .inr (.mk a k))
  invFun := Sum.elim FreeM.pure (fun t ↦ .liftBind t.fst t.snd)
  left_inv t := by cases t <;> rfl
  right_inv t := by cases t <;> rfl

/-- Interpret leaves and operation nodes by the free-monad recursor. -/
def fold (var : Y → Z) (alg : P.Obj X Z → Z) : P.Free X Y → Z :=
  FreeM.rec var (fun a _ ih ↦ alg (.mk a ih))

/-- The fold sends a variable to its interpretation. -/
@[simp] theorem fold_pure (var : Y → Z) (alg : P.Obj X Z → Z) (y : Y) :
    fold var alg (pure y) = var y := rfl

/-- The fold interprets an operation after interpreting its children. -/
@[simp] theorem fold_liftBind (var : Y → Z) (alg : P.Obj X Z → Z)
    (a : P.A) (k : (P.B a).Obj X → P.Free X Y) :
    fold var alg (.liftBind a k) = alg (.mk a (fun d ↦ fold var alg (k d))) := rfl

/-- The universal property at a fixed negative parameter: an interpretation is uniquely
determined by its values on variables and operations. -/
theorem fold_unique (var : Y → Z) (alg : P.Obj X Z → Z) (h : P.Free X Y → Z)
    (hp : ∀ y, h (.pure y) = var y)
    (hr : ∀ a k, h (.liftBind a k) = alg (.mk a (h ∘ k))) : h = fold var alg := by
  funext t
  refine FreeM.rec hp (fun a k ih ↦ ?_) t
  exact (hr a k).trans (congrArg (fun q ↦ alg (.mk a q)) (funext ih))

/-- Contravariance of the free monad: rename inputs at every operation. -/
def comap {X' : Type w} (f : X' → X) : P.Free X Y → P.Free X' Y :=
  fold FreeM.pure (fun t ↦ .liftBind t.fst (t.snd ∘ (P.B t.fst).map f))

/-- Input renaming preserves variables. -/
@[simp] theorem comap_pure {X' : Type w} (f : X' → X) (y : Y) :
    comap (P := P) f (pure y) = pure y := rfl

/-- Input renaming precomposes the direction polynomial at an operation. -/
@[simp] theorem comap_liftBind {X' : Type w} (f : X' → X)
    (a : P.A) (k : (P.B a).Obj X → P.Free X Y) :
    comap f (.liftBind a k) =
      .liftBind a (fun d ↦ comap f (k ((P.B a).map f d))) := rfl

/-- Identity input renaming changes no term. -/
@[simp] theorem comap_id (t : P.Free X Y) : comap id t = t := by
  refine FreeM.rec (fun _ ↦ rfl) (fun a k ih ↦ ?_) t
  exact congrArg (FreeM.liftBind a) (funext ih)

/-- Input renaming reverses composition. -/
theorem comap_comp {X' : Type w} {X'' : Type z} (f : X' → X) (g : X'' → X')
    (t : P.Free X Y) : comap g (comap f t) = comap (f ∘ g) t := by
  refine FreeM.rec (fun _ ↦ rfl) (fun a k ih ↦ ?_) t
  exact congrArg (FreeM.liftBind (P := P.apply X'') a)
    (funext fun d ↦ ih ((P.B a).map (f ∘ g) d))

/-- Input and output renaming commute, giving the profunctor interchange law. -/
theorem comap_map {X' : Type w} {Y' : Type z} (f : X' → X) (g : Y → Y')
    (t : P.Free X Y) : comap f (t.map g) = (comap f t).map g := by
  refine FreeM.rec (fun _ ↦ rfl) (fun a k ih ↦ ?_) t
  exact congrArg (FreeM.liftBind (P := P.apply X') a)
    (funext fun d ↦ ih ((P.B a).map f d))

/-- Input renaming preserves substitution, so its components are monad morphisms. -/
theorem comap_bind {X' : Type z} (f : X' → X) (t : P.Free X Y)
    (k : Y → P.Free X Z) :
    comap f (t.bind k) = (comap f t).bind (fun y ↦ comap f (k y)) := by
  refine FreeM.rec (fun _ ↦ rfl) (fun a ts ih ↦ ?_) t
  exact congrArg (FreeM.liftBind (P := P.apply X') a)
    (funext fun d ↦ ih ((P.B a).map f d))

/-- Output renaming preserves the root. -/
@[simp] theorem root_map (f : Y → Z) (t : P.Free X Y) : root (t.map f) = root t := by
  cases t <;> rfl

/-- Input renaming preserves the root. -/
@[simp] theorem root_comap {X' : Type w} (f : X' → X) (t : P.Free X Y) :
    root (comap f t) = root t := by
  cases t <;> rfl

end Free

/-- The compatible families forming the end of the pointwise free monad. Its categorical
universal property is supplied by mathlib in the category-theoretic companion module. -/
abbrev End : Type (max uA uB uC (u + 1)) :=
  { e : (X : Type u) → P.Free X X //
    ∀ {X Y : Type u} (f : X → Y), (e X).map f = Free.comap f (e Y) }

namespace End

variable {P}

/-- Instantiate an end element at a type. -/
def eval (e : P.End) (X : Type u) : P.Free X X := e.val X

/-- The wedge condition compares output renaming with input renaming. -/
theorem wedge (e : P.End) {X Y : Type u} (f : X → Y) :
    (e.eval X).map f = Free.comap f (e.eval Y) :=
  e.property f

/-- Package a family with a proved wedge condition as an end element. -/
def mk (e : (X : Type u) → P.Free X X)
    (he : ∀ {X Y : Type u} (f : X → Y), (e X).map f = Free.comap f (e Y)) : P.End :=
  ⟨e, he⟩

/-- Kmett's interpreter: instantiate at the algebra's carrier and fold. -/
def iter {X : Type u} (alg : P.Obj X X → X) (e : P.End) : X :=
  Free.fold id alg (e.eval X)

/-- Read the uniform root at the empty type, where a variable is impossible. -/
def head (e : P.End.{uA, uB, uC, u}) : P.A :=
  FreeM.casesOn (e.eval PEmpty.{u + 1}) PEmpty.elim (fun a _ ↦ a)

/-- Every component has the root read at the empty type. -/
theorem root_eval (e : P.End.{uA, uB, uC, u}) (X : Type u) :
    Free.root (e.eval X) = some e.head := by
  have hw := congrArg Free.root (e.wedge (PEmpty.elim : PEmpty.{u + 1} → X))
  simp only [Free.root_map, Free.root_comap] at hw
  rw [← hw]
  cases h : e.eval PEmpty.{u + 1} with
  | pure x => exact x.elim
  | liftBind a k => simp only [head, h]; rfl

/-- Recover the children of an end element with its uniform root. -/
def children (e : P.End.{uA, uB, uC, u}) (X : Type u) :
    (P.B e.head).Obj X → P.Free X X :=
  Free.childrenAt e.head (e.eval X) (e.root_eval X)

/-- A component is reconstructed from the uniform root and its children. -/
theorem liftBind_children (e : P.End.{uA, uB, uC, u}) (X : Type u) :
    FreeM.liftBind e.head (e.children X) = e.eval X :=
  Free.liftBind_childrenAt _ _ _

/-- A closed end element has one operation position shared by every type instance. -/
theorem exists_root (e : P.End.{uA, uB, uC, u}) :
    ∃ a : P.A, ∀ X : Type u, ∃ k, e.eval X = FreeM.liftBind a k :=
  ⟨e.head, fun X ↦ ⟨e.children X, (e.liftBind_children X).symm⟩⟩

/-- The children satisfy the wedge condition with the direction input renamed too. -/
theorem children_wedge (e : P.End.{uA, uB, uC, u}) {X Y : Type u} (f : X → Y)
    (d : (P.B e.head).Obj X) :
    (e.children X d).map f = Free.comap f (e.children Y ((P.B e.head).map f d)) := by
  have h := e.wedge f
  rw [← e.liftBind_children X, ← e.liftBind_children Y] at h
  exact congrFun (Free.liftBind_injective e.head h) d

/-- A uniform operation with a compatible family of children. Currying the direction
polynomial exposes one open child for each inner position, with its directions as binders. -/
abbrev Layer : Type (max uA uB uC (u + 1)) :=
  (a : P.A) × { k : (X : Type u) → (P.B a).Obj X → P.Free X X //
    ∀ {X Y : Type u} (f : X → Y) (d : (P.B a).Obj X),
      (k X d).map f = Free.comap f (k Y ((P.B a).map f d)) }

/-- Construct a closed end element from a uniform operation and coherent open children. -/
def roll (n : Layer.{uA, uB, uC, u} (P := P)) : P.End.{uA, uB, uC, u} :=
  mk (fun X ↦ .liftBind n.1 (n.2.val X)) (by
    intro X Y f
    exact congrArg (FreeM.liftBind (P := P.apply X) n.1) (funext (n.2.property f)))

/-- Decompose a closed end element into its uniform operation and coherent open children. -/
def unroll (e : P.End.{uA, uB, uC, u}) : Layer.{uA, uB, uC, u} (P := P) :=
  ⟨e.head, e.children, e.children_wedge⟩

/-- The end unfolds into a uniform position and compatible open subterms. The children
are families depending on input variables, rather than arbitrary functions on the end. -/
def unfold : P.End.{uA, uB, uC, u} ≃ Layer.{uA, uB, uC, u} (P := P) where
  toFun := unroll
  invFun := roll
  left_inv e := Subtype.ext (funext (e.liftBind_children))
  right_inv n := by cases n; rfl

end End

end PProfunctor

end Geb.PHOAS
