/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Geb.Mathlib.Data.PFunctor.IndRec.Slice
public import Geb.Mathlib.Data.PFunctor.IndRec.Hom
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

/-!
# Prototype: IR code constructors at the presheaf p.r.a. level

Throwaway exploration, not upstream-eligible content. It tests the
load-bearing claims of the presheaf-generalized IR brainstorm:

1. `iotaPresheaf` — the constant (`iota`) case generalizes to the functor
   constant at the representable `y j₀`, whose shape type is the total space
   `Σ j', (j' ⟶ j₀)` of that representable rather than a single shape.
2. `iotaDiscreteShapeEquiv` — for a discrete `J` that shape type collapses to
   `PUnit`, recovering `IR.toSlicePFunctorIota`'s single shape.
3. `iotaConst` — the constant functor at an *arbitrary* presheaf on `J`, which
   is what a Lemma-1-style completeness result needs and which `iota` + `sigma`
   cannot reach (they generate only coproducts of representables).
4. `Functoriality` — that a witness family over pre-codes is definable by
   `IR.rec`. It establishes the attachment mechanism only; the witness type it
   uses is built from `IR.Hom`, whose `ι`-clause is propositional equality of
   indices rather than a `C₀`-morphism, and is therefore the wrong type at a
   non-discrete `C₀`.
5. `arityVaries` — a functor whose shape presheaf is terminal and whose
   `reindex` is not invertible.

## Main definitions

* `GebProto.iotaPresheaf` / `iotaPresheafData` — the constant functor at a
  representable, and its operations.
* `GebProto.iotaDiscreteShapeEquiv` — the discrete degeneracy of its shape type.
* `GebProto.iotaConst` / `iotaConstData` — the constant functor at an arbitrary
  presheaf, and its operations.
* `GebProto.Functoriality` — the witness family attached over pre-codes.
* `GebProto.arityB`, `GebProto.arityVaries` / `arityVariesData`,
  `GebProto.arityVariesShapeEquiv` — the functor with non-invertible `reindex`,
  its arity, its operations, and the terminality of its shape presheaf.

## Tags

prototype, inductive-recursive, presheaf, parametric right adjoint
-/

@[expose] public section

universe uI uJ uB vI vJ

open CategoryTheory

namespace GebProto

section Iota

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- The operations of the constant functor at the representable `y j₀`: shapes
are the total space of `y j₀`, the shape-output map is its projection, there
are no directions, and `shapeRestr` is precomposition. -/
def iotaPresheafData (j₀ : J) :
    PresheafPFunctorData.{uI, uJ, max uJ vJ, uB, vI, vJ} I J where
  A := Σ j' : J, (j' ⟶ j₀)
  B := fun _ ↦ PEmpty
  r := fun x ↦ PEmpty.elim x.2
  q := fun x ↦ x.1
  directionRestr := fun _ {_ _} _g d ↦ PEmpty.elim d.1
  shapeRestr := fun {_ j'} g s ↦ ⟨⟨j', g ≫ eqToHom s.2.symm ≫ s.1.2⟩, rfl⟩
  reindex := fun {_ _} _g _a {_} d ↦ PEmpty.elim d.1

/-- Every direction fiber of `iotaPresheafData` is empty, hence a subsingleton;
this discharges all five direction-side functor laws. -/
instance subsingletonIotaDirection (j₀ : J)
    (a : (iotaPresheafData.{uI, uJ, uB, vI, vJ} (I := I) j₀).A) (i : I) :
    Subsingleton ((iotaPresheafData.{uI, uJ, uB, vI, vJ} (I := I) j₀).Direction a i) :=
  ⟨fun x _ ↦ PEmpty.elim x.1⟩

set_option linter.checkUnivs false in
/-- The constant functor at the representable `y j₀`, as a `PresheafPFunctor`.
The shape-side laws are the category laws of `J`; the direction-side laws hold
because every direction fiber is empty. -/
def iotaPresheaf (j₀ : J) : PresheafPFunctor.{uI, uJ, max uJ vJ, uB, vI, vJ} I J where
  toPresheafPFunctorData := iotaPresheafData j₀
  isFunctorial :=
    { directionRestr_id := by intro a i; funext d; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext d; exact Subsingleton.elim _ _
      shapeRestr_id := by
        intro j
        funext s
        obtain ⟨⟨jj, h⟩, rfl⟩ := s
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (by simp [iotaPresheafData])))
      shapeRestr_comp := by
        intro j j' j'' g h
        funext s
        obtain ⟨⟨jj, k⟩, rfl⟩ := s
        refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
        simp only [iotaPresheafData, Function.comp_apply, eqToHom_refl, Category.id_comp]
        exact Category.assoc _ _ _
      reindex_naturality := by intro j j' g a i i' f; funext d; exact Subsingleton.elim _ _
      reindex_id := by intro j a i d; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i d; exact Subsingleton.elim _ _ }

end Iota

section Degeneracy

variable {O : Type uJ}

/-- Claim 2: for a discrete `J` the generalized iota's shape type collapses to
`PUnit`, recovering the single shape of `IR.toSlicePFunctorIota`. -/
def iotaDiscreteShapeEquiv (o : O) :
    (Σ j' : Discrete O, (j' ⟶ (⟨o⟩ : Discrete O))) ≃ PUnit.{uJ + 1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ ⟨⟨o⟩, 𝟙 _⟩
  left_inv := by
    rintro ⟨⟨a⟩, ⟨⟨(h : a = o)⟩⟩⟩
    cases h
    rfl
  right_inv := by rintro ⟨⟩; rfl

end Degeneracy

section IotaConst

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- Claim 3: the constant functor at an *arbitrary* presheaf `P` on `J`. Shapes
are the total space of `P` (its category of elements), the shape-output map is
the projection, there are no directions, and `shapeRestr` is `P`'s own
restriction. This is what a Lemma-1-style completeness result needs and what
`iota` + `sigma` cannot reach, those generating only coproducts of
representables. -/
def iotaConstData (P : Jᵒᵖ ⥤ Type uB) :
    PresheafPFunctorData.{uI, uJ, max uJ uB, uB, vI, vJ} I J where
  A := Σ j : J, P.obj ⟨j⟩
  B := fun _ ↦ PEmpty
  r := fun x ↦ PEmpty.elim x.2
  q := fun x ↦ x.1
  directionRestr := fun _ {_ _} _g d ↦ PEmpty.elim d.1
  shapeRestr := fun {_ j'} g s ↦
    ⟨⟨j', P.map g.op (cast (congrArg (fun x ↦ P.obj ⟨x⟩) s.2) s.1.2)⟩, rfl⟩
  reindex := fun {_ _} _g _a {_} d ↦ PEmpty.elim d.1

/-- Every direction fiber of `iotaConstData` is empty, hence a subsingleton;
this discharges all five direction-side functor laws. -/
instance subsingletonIotaConstDirection (P : Jᵒᵖ ⥤ Type uB)
    (a : (iotaConstData.{uI, uJ, uB, vI, vJ} (I := I) P).A) (i : I) :
    Subsingleton ((iotaConstData.{uI, uJ, uB, vI, vJ} (I := I) P).Direction a i) :=
  ⟨fun x _ ↦ PEmpty.elim x.1⟩

set_option linter.checkUnivs false in
/-- The constant functor at `P` is a genuine `PresheafPFunctor`: the shape-side
laws are `P`'s own functor laws. -/
def iotaConst (P : Jᵒᵖ ⥤ Type uB) :
    PresheafPFunctor.{uI, uJ, max uJ uB, uB, vI, vJ} I J where
  toPresheafPFunctorData := iotaConstData P
  isFunctorial :=
    { directionRestr_id := by intro a i; funext d; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext d; exact Subsingleton.elim _ _
      shapeRestr_id := by
        intro j
        funext s
        obtain ⟨⟨jj, p⟩, rfl⟩ := s
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (by simp [iotaConstData])))
      shapeRestr_comp := by
        intro j j' j'' g h
        funext s
        obtain ⟨⟨jj, p⟩, rfl⟩ := s
        refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
        simp only [iotaConstData, Function.comp_apply, cast_eq]
        exact Functor.map_comp_apply P g.op h.op p
      reindex_naturality := by intro j j' g a i i' f; funext d; exact Subsingleton.elim _ _
      reindex_id := by intro j a i d; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i d; exact Subsingleton.elim _ _ }

/-- The representable case is definitionally the `P := yoneda.obj j₀` case: the
two shape types coincide on the nose. -/
example (j₀ : J) :
    (iotaPresheafData.{uI, uJ, uB, vI, vJ} (I := I) j₀).A =
      (iotaConstData.{uI, uJ, vJ, vI, vJ} (I := I) (yoneda.obj j₀)).A := rfl

end IotaConst

end GebProto

namespace GebProto

section Functoriality

/-!
Does a category-valued decoding target force a *mutual* (inductive-inductive)
definition of codes and code morphisms, as in Positive IR's Agda?

Two observations say no. First, Positive IR's pre-codes are already this
repository's `IR` codes: its `ι` carries an object of `C`, its `σ` a `Set`
with subcodes indexed by it, its `δ` a `Set` with subcodes indexed by
`A → C` — which is exactly `IR.Shape` / `IR.Direction` at `I = O = C₀`.
Second, in the Agda the `δ→δ` constructor of `Hom` takes `F→` and `G→` only as
implicit *indices* and never uses them, so `Hom` does not in fact depend on the
functoriality witnesses.

Together those let the witness be attached *after* the codes, by `IR.rec`,
against the already-defined `IR.Hom` — no mutuality, and so within this
repository's rule that recursion goes through recursors rather than
self-referential inductives. `Functoriality` below is that attachment.
-/

open IndRec IndRec.IR

universe u

variable (C₀ : Type u) [Category.{u} C₀]

/-- The functoriality witness of a code, attached after the fact by `IR.rec`:
nothing at `ι`, componentwise at `σ`, and at `δ` the Positive-IR witness `F→`
— a code morphism between the subcodes at any two labellings related by a
family of `C₀`-morphisms — paired with the witnesses of those subcodes.

That this elaborates at all is the point: `IR.Hom` is already defined, so the
witness needs no mutual definition with the codes. -/
def Functoriality : IR.{u, u, u, u} C₀ C₀ → Type u :=
  rec.{u, u, u, u, u + 1} C₀ C₀ (motive := fun _ ↦ Type u)
    (fun s ↦ match s with
      | Sum.inl _ => fun _ _ ↦ PUnit
      | Sum.inr (Sum.inl _) => fun _ m ↦ ∀ a, m a
      | Sum.inr (Sum.inr B) => fun f m ↦
          (∀ g h : B → C₀, (∀ b, g b ⟶ h b) → Hom C₀ C₀ (f ⟨g⟩) (f ⟨h⟩)) ×
            (∀ i, m i))

end Functoriality

end GebProto

namespace GebProto

section Reindex

/-!
`reindex` is the obligation neither prior paper has an analogue for: Positive
IR's `F→` witnesses functoriality of subcodes in the *input* labelling
(`A → C`), which is the `directionRestr` side, whereas `reindex` witnesses
functoriality of the arity assignment over `el(T₁)` — the *output* side.

`arityVaries` below is the smallest functor that makes the obligation bite. Its
shape presheaf is the representable `y 1` (equivalently, since `1` is terminal
in the walking arrow, the terminal presheaf): one shape over each of `0` and
`1`. But its arity is `Fin 1` at the shape over `1` and `Fin 0` at the shape
over `0`, so `reindex` along `0 ⟶ 1` is the map out of the empty type — not
invertible.

This is what rules out attaching arities per code-*path*. A code built from `ι`
at a presheaf, `σ` over a set, and `δ` adjoining a fixed arity assigns to each
shape the arity accumulated along its path through the code tree; restriction
of a shape never changes that path, so such a code can only denote functors
whose `reindex` is an isomorphism. `arityVaries` therefore has no such code
even though its shape presheaf is as simple as a shape presheaf gets.
-/

open CategoryTheory

/-- The arity of the shape `a`: one direction at `1`, none at `0`. An `abbrev`
so the `PFunctor` projection reduces to it. -/
abbrev arityB (a : Fin 2) : Type := ULift (Fin a.val)

instance subsingletonArityB (a : Fin 2) : Subsingleton (arityB a) :=
  ⟨fun x y ↦ ULift.ext _ _ (Fin.ext (by
    have hx := x.down.isLt
    have hy := y.down.isLt
    have ha := a.isLt
    omega))⟩

/-- Operations of the smallest functor with non-invertible `reindex`: over the
walking arrow, one shape at each object, with one direction at `1` and none
at `0`. `reindex` along `0 ⟶ 1` is `Fin.castLE`, here the map out of `Fin 0`. -/
@[reducible] def arityVariesData : PresheafPFunctorData (Fin 1) (Fin 2) where
  A := Fin 2
  B := arityB
  r := fun _ ↦ 0
  q := fun a ↦ a
  directionRestr := fun _ {_ _} _g d ↦ ⟨d.1, Subsingleton.elim _ _⟩
  shapeRestr := fun {_ j'} _g _s ↦ ⟨j', rfl⟩
  reindex := fun {j j'} g a {_} d ↦ by
    obtain ⟨aa, (rfl : aa = j)⟩ := a
    exact ⟨⟨Fin.castLE (leOfHom g) d.1.down⟩, Subsingleton.elim _ _⟩

/-- Each direction fiber has at most one element, so the five direction-side
laws hold by `Subsingleton.elim`. The *content* is unaffected: the fibers are
empty at the shape over `0` and inhabited at the shape over `1`, which is
exactly what makes `reindex` non-invertible. -/
instance subsingletonArityVariesDirection (a : arityVariesData.A) (i : Fin 1) :
    Subsingleton (arityVariesData.Direction a i) :=
  ⟨fun x y ↦ Subtype.ext (Subsingleton.elim (α := arityB a) x.1 y.1)⟩

/-- The functor: the shape-side laws are trivial because every `Shape j` is the
singleton `{j}`. -/
def arityVaries : PresheafPFunctor (Fin 1) (Fin 2) where
  toPresheafPFunctorData := arityVariesData
  isFunctorial :=
    { directionRestr_id := by intro a i; funext d; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext d; exact Subsingleton.elim _ _
      shapeRestr_id := by
        intro j
        funext s
        obtain ⟨ss, (rfl : ss = j)⟩ := s
        rfl
      shapeRestr_comp := by
        intro j j' j'' g h
        funext s
        obtain ⟨ss, (rfl : ss = j)⟩ := s
        rfl
      reindex_naturality := by intro j j' g a i i' f; funext d; exact Subsingleton.elim _ _
      reindex_id := by intro j a i d; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i d; exact Subsingleton.elim _ _ }

/-- The arity genuinely varies: empty at the shape over `0`, inhabited at the
shape over `1`. So `reindex` along `0 ⟶ 1` is the empty map, not an iso. -/
example : arityVariesData.B ⟨0, by omega⟩ = ULift (Fin 0) := rfl
example : arityVariesData.B ⟨1, by omega⟩ = ULift (Fin 1) := rfl

/-- Every `Shape j` is a singleton, so the shape presheaf is terminal — as
simple as a shape presheaf gets, yet the arity above it is not constant. -/
def arityVariesShapeEquiv (j : Fin 2) : arityVariesData.Shape j ≃ PUnit where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ ⟨j, rfl⟩
  left_inv := by rintro ⟨ss, (rfl : ss = j)⟩; rfl
  right_inv := fun _ ↦ rfl

end Reindex

end GebProto
