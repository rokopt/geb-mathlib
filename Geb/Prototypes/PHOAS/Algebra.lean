/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Derived algebra and coalgebra profunctors

The derived profunctor {lit}`H(X, Y) = P(Y, X) → Y` turns diagonal elements into
structure maps {lit}`P(X, X) → X`, in the one-object sense of
{cite}`NLabProfunctorAlgebra`. A morphism satisfies the mixed-variance compatibility
equation on {lit}`P(Y, X)`.
The coalgebra counterpart is {lit}`K(X, Y) = X → P(X, Y)`, with diagonal elements
{lit}`X → P(X, X)`.

## Main definitions

* {lit}`AlgebraObj` and {lit}`algebraDimap` give the derived profunctor.
* {lit}`Algebra` and {lit}`Algebra.Hom` give its diagonal elements and morphisms.
* {lit}`CoalgebraObj`, {lit}`Coalgebra`, and {lit}`Coalgebra.Hom` give the counterpart.

## Main statements

* {lit}`Algebra.not_initial_of_point` excludes initiality for inhabited algebras when
  an inner position can be selected at every operation. The proof constructs two distinct
  morphisms into one algebra with two tags.

## References

* {cite}`NLabProfunctorAlgebra`

## Tags

profunctor algebra, mixed variance, initiality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

universe uA uB uC u v w z

variable (P : PProfunctor.{uA, uB, uC})

/-- The derived profunctor's carrier: structure maps with their parameters separated. -/
abbrev AlgebraObj (X : Type u) (Y : Type v) : Type (max uA uB uC u v) := P.Obj Y X → Y

/-- Reversing the polynomial's parameters and mapping into the output gives the variance. -/
def algebraDimap {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
    (f : X' → X) (g : Y → Y') (α : P.AlgebraObj X Y) : P.AlgebraObj X' Y' :=
  g ∘ α ∘ P.dimap g f

/-- An algebra is a carrier equipped with a map from the original profunctor's diagonal. -/
abbrev Algebra : Type (max uA uB uC (u + 1)) := (X : Type u) × P.AlgebraObj X X

namespace Algebra

variable {P}

/-- Compatibility in the derived profunctor compares the maps on {lit}`P(Y, X)`. -/
abbrev Hom (s : P.Algebra.{uA, uB, uC, u}) (t : P.Algebra.{uA, uB, uC, v}) :=
  { f : s.1 → t.1 // P.algebraDimap id f s.2 = P.algebraDimap f id t.2 }

/-- Duplicate a pointed algebra with two tags. A chosen inner position lets each operation
read a tag from one child and interpret all its children using that same tag. -/
def doubled (choose : (a : P.A) → (P.B a).A) (s : P.Algebra.{uA, uB, uC, u})
    (x₀ : s.1) : P.Algebra.{uA, uB, uC, u} :=
  ⟨s.1 × Bool, fun t ↦
    let tag := (t.snd (.mk (choose t.fst) (fun _ ↦ (x₀, false)))).2
    (s.2 (P.dimap (fun x ↦ (x, tag)) Prod.fst t), tag)⟩

/-- Either constant tag gives an algebra morphism into the duplicated algebra. -/
def inclusion (choose : (a : P.A) → (P.B a).A) (s : P.Algebra.{uA, uB, uC, u})
    (x₀ : s.1) (tag : Bool) : Hom s (doubled choose s x₀) :=
  ⟨fun x ↦ (x, tag), rfl⟩

/-- The two tag inclusions are distinct, witnessed at the chosen point. -/
theorem inclusion_ne (choose : (a : P.A) → (P.B a).A)
    (s : P.Algebra.{uA, uB, uC, u}) (x₀ : s.1) :
    inclusion choose s x₀ false ≠ inclusion choose s x₀ true := by
  intro h
  exact Bool.false_ne_true (congrArg (fun f ↦ (f.val x₀).2) h)

/-- With an inner position at every operation, no inhabited algebra can have a unique
morphism to every algebra: its two tag inclusions give a counterexample. -/
theorem not_initial_of_point (choose : (a : P.A) → (P.B a).A)
    (s : P.Algebra.{uA, uB, uC, u}) (x₀ : s.1) :
    ¬(∀ t : P.Algebra.{uA, uB, uC, u}, Nonempty (Unique (Hom s t))) := by
  intro h
  obtain ⟨ht⟩ := h (doubled choose s x₀)
  exact inclusion_ne choose s x₀ ((ht.uniq _).trans (ht.uniq _).symm)

end Algebra

/-- The coalgebra counterpart, specializing to {lit}`Hom(X, F(Y))` for an endofunctor. -/
abbrev CoalgebraObj (X : Type u) (Y : Type v) : Type (max uA uB uC u v) := X → P.Obj X Y

/-- Map a coalgebra component by precomposing its input and mapping the polynomial output. -/
def coalgebraDimap {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
    (f : X' → X) (g : Y → Y') (c : P.CoalgebraObj X Y) : P.CoalgebraObj X' Y' :=
  P.dimap f g ∘ c ∘ f

/-- A carrier equipped with a map into the original profunctor's diagonal. -/
abbrev Coalgebra : Type (max uA uB uC (u + 1)) := (X : Type u) × P.CoalgebraObj X X

namespace Coalgebra

variable {P}

/-- The derived profunctor's compatibility equation for coalgebra maps. -/
abbrev Hom (s : P.Coalgebra.{uA, uB, uC, u}) (t : P.Coalgebra.{uA, uB, uC, v}) :=
  { f : s.1 → t.1 // P.coalgebraDimap id f s.2 = P.coalgebraDimap f id t.2 }

/-- A coalgebra morphism preserves the operation observed at each state. -/
theorem Hom.position_eq {s : P.Coalgebra.{uA, uB, uC, u}}
    {t : P.Coalgebra.{uA, uB, uC, v}} (f : Hom s t) (x : s.1) :
    (s.2 x).fst = (t.2 (f.val x)).fst :=
  congrArg PFunctor.Obj.fst (congrFun f.property x)

/-- Coalgebra morphisms compose by composing their underlying functions. -/
def Hom.comp {s : P.Coalgebra.{uA, uB, uC, u}} {t : P.Coalgebra.{uA, uB, uC, v}}
    {r : P.Coalgebra.{uA, uB, uC, w}} (f : Hom s t) (g : Hom t r) : Hom s r :=
  ⟨g.val ∘ f.val, by
    calc
      P.coalgebraDimap id (g.val ∘ f.val) s.2 =
          P.coalgebraDimap id g.val (P.coalgebraDimap id f.val s.2) := rfl
      _ = P.coalgebraDimap id g.val (P.coalgebraDimap f.val id t.2) :=
        congrArg (P.coalgebraDimap id g.val) f.property
      _ = P.coalgebraDimap f.val id (P.coalgebraDimap id g.val t.2) := rfl
      _ = P.coalgebraDimap f.val id (P.coalgebraDimap g.val id r.2) :=
        congrArg (P.coalgebraDimap f.val id) g.property
      _ = P.coalgebraDimap (g.val ∘ f.val) id r.2 := rfl⟩

end Coalgebra

end Geb.PHOAS.PProfunctor
