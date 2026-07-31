/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Geb.Mathlib.Data.PFunctor.IndRec.Hom
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

/-!
# Prototype: IR code constructors at the presheaf p.r.a. level (choice-free core)

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free; the bundled restatement of the p.r.a. formula, which
writes `⟶` between two objects of a presheaf category and so pulls in
`Classical.choice` from mathlib, is in the sibling `PresheafIRProto.Functor`
module. This module tests the following claims about presheaf-generalized
IR codes:

1. `iotaPresheaf` — the constant (`iota`) case generalizes to the functor
   constant at the representable `y j₀`, whose shape type is the total space
   `Σ j', (j' ⟶ j₀)` of that representable rather than a single shape.
2. `iotaDiscreteShapeEquiv` — for a discrete `J` that shape type collapses to
   `PUnit`. No identification with `IR.toSlicePFunctorIota`'s shape type is
   established; the two are at different universe instantiations.
3. `iotaConst` — the constant functor at an arbitrary presheaf on `J`, which
   is what a Lemma-1-style completeness result needs and which `iota` + `sigma`
   cannot reach (they generate only coproducts of representables).
4. `Functoriality` — that `IR.rec` reaches the subcodes, which is all it
   establishes. Its witness type is built from `IR.Hom`, whose `ι`-clause is
   propositional equality of indices and so ignores `C₀`'s morphisms; it is
   not the type the source requires.
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
* `GebProto.shapePresheaf` / `GebProto.arityPresheaf` — the shape presheaf `T₁`
  and the arity presheaf `E(a)`, as `Functor` values built from the raw fields.
* `GebProto.ArityHom` / `GebProto.ofArityHomElt` /
  `GebProto.objEquivSigmaArityHom` — the p.r.a. formula
  `T Z ≃ Σ a, Hom(E(a), Z)` with the presheaf hom unbundled, hence free of
  `Classical.choice`, and the slice element its inverse produces.
* `GebProto.DomHom` / `GebProto.DomNatFamily` /
  `GebProto.domHomEquivNatFamily` — the domain-level morphism data, the natural
  families it represents, and the Yoneda equivalence between them.
* `GebProto.ShapeHom` — the unbundled presheaf hom `T₁ ⟶ T₁'`.
* `GebProto.PshHom` — the full morphism data of presheaf p.r.a. functors:
  a `ShapeHom`, a backward arity map, and the `el(T₁)ᵒᵖ` naturality of the
  latter, stated across a transport along the former's naturality.
* `GebProto.ObjFib` / `GebProto.objFibRestr` / `GebProto.objFibMap` /
  `GebProto.ofSigmaFib` — the output presheaf's fibres, their `J`-restriction
  and input-presheaf action, unbundled, and the fibre element of a shape and an
  arity hom.
* `GebProto.pshHomFib` — the action of a `PshHom` on those fibres.
* `GebProto.PshNatFamily` / `GebProto.pshHomEquivNatFamily` — the natural
  families a `PshHom` represents, and the equivalence between them.

## Main statements

* `GebProto.pshHomFib_objFibRestr` — the action of a `PshHom` commutes with the
  `J`-restriction, which is the content of `PshHom`'s `reindexCompat` clause.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [GhaniMalatestaNordvallForsberg2014Agda]
* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

prototype, inductive-recursive, presheaf, parametric right adjoint
-/

@[expose] public section

universe uI uJ uA uB uX uZ vI vJ

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
`PUnit`. This is not an identification with `IR.toSlicePFunctorIota`'s shape
type, which is at a different universe instantiation. -/
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
/-- Claim 3: the constant functor at an arbitrary presheaf `P` on `J`. Shapes
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

end IotaConst

end GebProto

namespace GebProto

section Functoriality

/-!
Can the functoriality witness be attached after the codes, rather than as a
code field defined simultaneously with the morphisms?

That depends on which morphism collection is taken. Remark 3.4 of
[GhaniNordvallForsbergMalatesta2015] states that its results are parametric
in that choice: any collection
representing natural transformations between the codes works, provided
identities and composition are definable. Its Definition 3.1 takes a natural
transformation, whose naturality refers to the witnesses and to composition of
code morphisms; [GhaniMalatestaNordvallForsberg2014Agda] takes a bare
family of components, whose
`δ→δ` rule mentions the witnesses only in its conclusion's indices, never in its
premises. Under the
latter the morphism type does not depend on the witnesses, so the witness can
be attached afterwards, by `IR.rec` against an already-defined morphism type.

`Functoriality` below demonstrates only that `IR.rec` reaches the subcodes,
which is what such an attachment needs. Its witness type is built from
`IR.Hom`, whose `ι`-clause is propositional equality of indices and so ignores
the category's morphisms; that is not the type the source requires, and no
claim is made here that this witness is the right one.
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

`arityVaries` below is the smallest functor for which the obligation has content. Its
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
laws hold by `Subsingleton.elim`. The content is unaffected: the fibers are
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
theorem arityVariesData_B_zero : arityVariesData.B ⟨0, by omega⟩ = ULift (Fin 0) := rfl

theorem arityVariesData_B_one : arityVariesData.B ⟨1, by omega⟩ = ULift (Fin 1) := rfl

/-- Every `Shape j` is a singleton, so the shape presheaf is terminal — as
simple as a shape presheaf gets, yet the arity above it is not constant. -/
def arityVariesShapeEquiv (j : Fin 2) : arityVariesData.Shape j ≃ PUnit where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ ⟨j, rfl⟩
  left_inv := by rintro ⟨ss, (rfl : ss = j)⟩; rfl
  right_inv := fun _ ↦ rfl

end Reindex

end GebProto

namespace GebProto

section PolyMorphism

/-!
The regular formula for natural transformations between polynomial functors:
shapes forward, arities backward. For slice polynomial functors `F`, `F'` over
the same `dom` and `cod`, a transformation is a map of shapes over each output
index together with, for each shape, a map of arities in the opposite
direction. Naturality is not a side condition on this data; it is automatic,
which is what `sliceHomApp` below exhibits by constructing the action.

Derivation, for the presheaf case: `T Z j = Σ_{a ∈ T₁ j} Hom(E a, Z)` is a
coproduct of representables in `Z`, so by Yoneda
`Nat(Σ_a Hom(E a, −), Σ_b Hom(E' b, −)) = Π_a Σ_b Hom(E' b, E a)`. Yoneda for
covariant hom-functors holds in any locally small category, so it is not what
restricts the argument. What restricts it is the premise: over the free
coproduct completion the `δ` interpretation is not a coproduct of
`Fam(C)`-representables, since by Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] its coproduct is indexed by set maps
`A → X`, whereas by Definition 2.2 a `Fam(C)`-morphism carries `C`-morphism
data that index does not.
-/

open CategoryTheory

set_option linter.checkUnivs false in
/-- A morphism of slice polynomial functors: shapes forward over each output
index, arities backward at each shape. -/
structure SliceHom {dom : Type uI} {cod : Type uJ}
    (F F' : SlicePFunctor.{uA, uB, uI, uJ} dom cod) : Type (max uA uB uI uJ) where
  /-- The shape map, over each output index. -/
  shape : ∀ j : cod, F.Shape j → F'.Shape j
  /-- The arity map, in the opposite direction, at each shape and base point. -/
  arity : ∀ (j : cod) (a : F.Shape j) (i : dom),
    F'.Direction (shape j a).1 i → F.Direction a.1 i

set_option linter.checkUnivs false in
/-- The action of a `SliceHom` on the domain-restricted functor's value: the
shape travels forward, and each direction of the new shape is filled by pulling
it back along `arity` and reading off the original assignment. That this is
definable with no further data is the content of the formula. -/
def sliceHomApp {dom : Type uI} {cod : Type uJ}
    {F F' : SlicePFunctor.{uA, uB, uI, uJ} dom cod} (α : SliceHom F F')
    {X : Type uX} (p : X → dom) (j : cod)
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j) :
    F'.toSliceDomPFunctor.Obj p :=
  ⟨⟨(α.shape j ⟨x.1.1, hq⟩).1,
      fun (b' : F'.toPFunctor.B (α.shape j ⟨x.1.1, hq⟩).1) ↦
        x.1.2 (α.arity j ⟨x.1.1, hq⟩ (F'.rCurried _ b') ⟨b', rfl⟩).1⟩,
    (F'.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b' ↦
      ((F.toSliceDomPFunctor.compatible_iff _ _ _).mp x.2
        (α.arity j ⟨x.1.1, hq⟩ (F'.rCurried _ b') ⟨b', rfl⟩).1).trans
        (α.arity j ⟨x.1.1, hq⟩ (F'.rCurried _ b') ⟨b', rfl⟩).2⟩

end PolyMorphism

end GebProto

namespace GebProto

section ShapeAndArityPresheaves

/-!
The two presheaves the p.r.a. formula names, extracted from the raw fields as
`Functor` values, on the model of `PresheafPFunctor.objPresheaf`.

`shapePresheaf` lands in `Type uA` and `arityPresheaf` in `Type uB`, those being
the universes of `SlicePFunctor.Shape` (a `Subtype` of `F.A : Type uA`) and of
`SliceDomPFunctor.Direction` (a `Subtype` of `F.B a : Type uB`). Neither carries
a `max` with the base or morphism universes: `Shape j` is cut out of `F.A` by a
`Prop`, and `Direction a i` out of `F.B a` by a `Prop`.

Consequently `arityPresheaf F a : Iᵒᵖ ⥤ Type uB` is an object of the same
category as `Z : Iᵒᵖ ⥤ Type uZ` only when `uB` and `uZ` are the same level.
Lean's `Type` hierarchy is not cumulative, so no relation `uB ≤ uZ` (which is
not expressible on levels anyway) helps; the two options are to instantiate
`uZ := uB`, or to `ULift` both sides into `Type (max uB uZ)`. Both are exhibited
below.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The shape presheaf `T₁ : Jᵒᵖ ⥤ Type uA`: fibre `F.Shape j` over `j`,
restriction maps `F.shapeRestr`, functor laws from `shapeRestr_id` /
`shapeRestr_comp`. -/
def shapePresheaf (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    Jᵒᵖ ⥤ Type uA where
  obj j := F.Shape j.unop
  map g := ↾ F.shapeRestr g.unop
  map_id j := by
    ext a
    exact congrFun (F.isFunctorial.shapeRestr_id j.unop) a
  map_comp g h := by
    ext a
    exact congrFun (F.isFunctorial.shapeRestr_comp g.unop h.unop) a

/-- The arity presheaf `E(a) : Iᵒᵖ ⥤ Type uB` of a shape `a`: fibre
`F.Direction a i` over `i`, restriction maps `F.directionRestr a`, functor laws
from `directionRestr_id` / `directionRestr_comp`. -/
def arityPresheaf (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A) :
    Iᵒᵖ ⥤ Type uB where
  obj i := F.Direction a i.unop
  map f := ↾ F.directionRestr a f.unop
  map_id i := by
    ext d
    exact congrFun (F.isFunctorial.directionRestr_id a i.unop) d
  map_comp f g := by
    ext d
    exact congrFun (F.isFunctorial.directionRestr_comp a f.unop g.unop) d

-- The two `example`s exhibiting the bundled hom, and the universes at which it
-- is formable, live in the sibling `Functor` module: they name `⟶` between
-- objects of a functor category, which is what draws in `Classical.choice`.

end ShapeAndArityPresheaves

end GebProto

namespace GebProto

section UnbundledArityHom

/-!
The p.r.a. formula again, with the presheaf hom in unbundled form.

`objEquivSigmaHom`, in the sibling `PresheafIRProto.Functor` module, depends on
`Classical.choice`, and so does anything
built on it. The dependence enters through `CategoryTheory.Functor.category`,
that is, through writing `⟶` between two objects of a functor category at all,
before any proof: `#print axioms CategoryTheory.Functor.category` reports
`Classical.choice`, whereas `shapePresheaf`, `arityPresheaf`,
`PresheafDomPFunctorData.obj` and `PresheafDomPFunctorData.value` do not.

`ArityHom` is the same data as `arityPresheaf F a ⟶ Z` written as a subtype of
a family of fibre maps, with the naturality square as the subtype predicate —
literally `PresheafDomPFunctorData.IsNatural`'s shape. `Z.map f.op` is
unaffected: the category instance on `Type u` is axiom-free; only the functor
category's instance is not.

Restating the equivalence over `ArityHom` also frees the universe of `Z`:
`objEquivSigmaHom` needs `Z : Iᵒᵖ ⥤ Type uB` so that `Z` and `arityPresheaf F a`
are objects of one category, whereas `ArityHom F a Z` is formable at any `uZ`.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The unbundled presheaf hom `E(a) ⟶ Z`: a family of fibre maps
`F.Direction a i → Z.obj ⟨i⟩` subject to the naturality square. -/
def ArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type (max uI uB uZ) :=
  { α : (i : I) → F.Direction a i → Z.obj ⟨i⟩ //
      ∀ ⦃i i' : I⦄ (f : i' ⟶ i) (b : F.Direction a i),
        α i' (F.directionRestr a f b) = Z.map f.op (α i b) }

/-- The slice element determined by a shape `a` and an unbundled arity hom
`α : E(a) ⟶ Z`: the direction `b` is assigned the `α`-image of `b`, read at
`b`'s own base point `F.rCurried a b`. Compatibility holds by construction, the
index component being that base point. -/
def ofArityHomElt (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ}
    (a : F.A) (α : ArityHom F a Z) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z) :=
  ⟨⟨a, fun b ↦ ⟨F.rCurried a b, α.1 (F.rCurried a b) ⟨b, rfl⟩⟩⟩,
    (F.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩

/-- The component `ofArityHomElt` assigns to a direction is the component `α`
assigns to it. Destructing the direction makes the `cast` inside `value` a
`cast` along a proof of `t = t`, which proof irrelevance reduces away. -/
theorem value_ofArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} (a : F.A) (α : ArityHom F a Z) ⦃i : I⦄
    (b : F.Direction (ofArityHomElt F a α).1.1 i) :
    F.value (ofArityHomElt F a α) b = α.1 i b := by
  obtain ⟨b1, rfl⟩ := b
  rfl

/-- The p.r.a. formula with the hom unbundled: the domain-restricted
interpretation of `F` at `Z` is the coproduct over shapes of the unbundled
representables on the arity presheaves. The forward map reads off the shape and
repackages the direction-assignment, its components being `value` and its
naturality being `IsNatural`; the inverse is `ofArityHomElt`. -/
def objEquivSigmaArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (Z : Iᵒᵖ ⥤ Type uZ) :
    F.toPresheafDomPFunctorData.obj Z ≃ Σ a : F.A, ArityHom F a Z where
  toFun x := ⟨x.1.1.1, ⟨fun i ↦ F.value x.1 (i := i), x.2⟩⟩
  invFun p :=
    ⟨ofArityHomElt F p.1 p.2, by
      intro i i' f b
      rw [value_ofArityHom, value_ofArityHom]
      exact p.2.2 f b⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦ ?_))))
    exact Sigma.ext ((F.compatible_iff _ _ _).mp x.1.2 b).symm (cast_heq _ _)
  right_inv p := by
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun i ↦ funext fun b ↦ ?_)))
    exact value_ofArityHom F p.1 p.2 b

end UnbundledArityHom

end GebProto

namespace GebProto

section UnbundledYoneda

/-!
The Yoneda step, unbundled, at the domain level only: `q`, `shapeRestr` and
`reindex` play no part here, so `DomHom` records only the shape map and the
backward arity map.

`DomHom F F'` is `Π a, Σ a', Hom(E'(a'), E(a))`, and its arity component is
definitionally `ArityHom F' a' (arityPresheaf F a)` — the unbundled hom into
the representing presheaf. `DomNatFamily F F'` is the families
`Π Z, T Z → T' Z` natural in `Z`, with naturality stated against
`PresheafDomPFunctorData.map`, which takes a bare `NatTrans` and so avoids the
functor category's instance.

The two are equivalent. Composing `objEquivSigmaArityHom` on both sides turns a
natural family into a map `Π a, Σ a', ArityHom F' a' (arityPresheaf F a)`, and
Yoneda supplies the inverse: a natural family out of `Σ a, ArityHom F a (−)` is
determined by its value at the representing object, recovered by evaluating at
`Z := arityPresheaf F a` on the generic element `idElt F a` — the element whose
arity hom is the identity.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The bundled natural transformation `E(a) ⟶ Z` of an unbundled arity hom.
The functor category's instance is not involved: `NatTrans` is a structure, and
only `⟶` between two functors would require it. -/
def natTransOfArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    {Z : Iᵒᵖ ⥤ Type uB} (μ : ArityHom F a Z) : NatTrans (arityPresheaf F a) Z where
  app X := ↾ μ.1 X.unop
  naturality := by
    intro _ _ f
    ext b
    exact μ.2 f.unop b

/-- Postcomposition of an unbundled arity hom with a natural transformation. -/
def postcompArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (ν : NatTrans Z Z') (μ : ArityHom F a Z) : ArityHom F a Z' :=
  ⟨fun i b ↦ ν.app ⟨i⟩ (μ.1 i b), by
    intro i i' f b
    change ν.app ⟨i'⟩ (μ.1 i' (F.directionRestr a f b)) = Z'.map f.op (ν.app ⟨i⟩ (μ.1 i b))
    rw [μ.2 f b]
    simp only [← ConcreteCategory.comp_apply]
    rw [ν.naturality f.op]⟩

/-- The identity arity hom, of `F` at `a` into `F`'s own arity presheaf. -/
def idArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A) :
    ArityHom F a (arityPresheaf F a) :=
  ⟨fun _ b ↦ b, by intro i i' f b; rfl⟩

/-- The generic element of shape `a`: the element of `T (E(a))` whose arity hom
is the identity. Yoneda's representing datum. -/
def idElt (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A) :
    F.toPresheafDomPFunctorData.obj (arityPresheaf F a) :=
  (objEquivSigmaArityHom F (arityPresheaf F a)).symm ⟨a, idArityHom F a⟩

/-- The generic element's shape and arity hom are `a` and the identity. -/
theorem objEquivSigmaArityHom_idElt (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (a : F.A) :
    objEquivSigmaArityHom F (arityPresheaf F a) (idElt F a) = ⟨a, idArityHom F a⟩ :=
  (objEquivSigmaArityHom F (arityPresheaf F a)).apply_symm_apply _

/-- The morphism data between two presheaf p.r.a. functors at the domain level:
shapes forward, arities backward, the arity map a morphism of arity
presheaves. -/
def DomHom (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) : Type (max uA uI uB) :=
  (a : F.A) → Σ a' : F'.A, { ψ : (i : I) → F'.Direction a' i → F.Direction a i //
      ∀ ⦃i i' : I⦄ (f : i' ⟶ i) (b : F'.Direction a' i),
        ψ i' (F'.directionRestr a' f b) = F.directionRestr a f (ψ i b) }

/-- The arity component of a `DomHom` is an unbundled arity hom of `F'` into the
arity presheaf of `F`: the representing presheaf of Yoneda's statement. -/
theorem domHom_eq_pi_sigma_arityHom (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    DomHom F F' = ((a : F.A) → Σ a' : F'.A, ArityHom F' a' (arityPresheaf F a)) := rfl

/-- Families `T Z → T' Z` natural in `Z`, with naturality stated unbundled
against `PresheafDomPFunctorData.map`. -/
def DomNatFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    Type (max uA uI vI (uB + 1)) :=
  { η : (Z : Iᵒᵖ ⥤ Type uB) → F.toPresheafDomPFunctorData.obj Z →
        F'.toPresheafDomPFunctorData.obj Z //
      ∀ (Z Z' : Iᵒᵖ ⥤ Type uB) (ν : NatTrans Z Z') (x : F.toPresheafDomPFunctorData.obj Z),
        η Z' (F.toPresheafDomPFunctorData.map ν x) =
          F'.toPresheafDomPFunctorData.map ν (η Z x) }

/-- Under `objEquivSigmaArityHom`, the action on input presheaves is
postcomposition: the shape is untouched and the arity hom is composed with `ν`.
Stated on the inverse side, where both sides are `ofArityHomElt` of the same
data. -/
theorem map_symm_arityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z Z' : Iᵒᵖ ⥤ Type uB} (ν : NatTrans Z Z') (p : Σ a : F.A, ArityHom F a Z) :
    F.toPresheafDomPFunctorData.map ν ((objEquivSigmaArityHom F Z).symm p) =
      (objEquivSigmaArityHom F Z').symm ⟨p.1, postcompArityHom F p.1 ν p.2⟩ :=
  rfl

/-- Yoneda's reconstruction: the element of `T Z` with shape `a` and arity hom
`μ` is the image of the generic element of shape `a` under the action of `μ`. -/
theorem map_idElt (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uB}
    (p : Σ a : F.A, ArityHom F a Z) :
    F.toPresheafDomPFunctorData.map (natTransOfArityHom F p.1 p.2) (idElt F p.1) =
      (objEquivSigmaArityHom F Z).symm p := by
  rw [idElt, map_symm_arityHom]
  rfl

/-- The action of a `DomHom` on the coproduct-of-representables side: the shape
travels forward along `φ`, and the arity hom is precomposed with `φ`'s backward
arity map. -/
def domHomSigma (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (φ : DomHom F F')
    {Z : Iᵒᵖ ⥤ Type uB} (p : Σ a : F.A, ArityHom F a Z) : Σ a' : F'.A, ArityHom F' a' Z :=
  ⟨(φ p.1).1, postcompArityHom F' _ (natTransOfArityHom F p.1 p.2) (φ p.1).2⟩

/-- The natural family determined by a `DomHom`: `domHomSigma` conjugated by the
p.r.a. formula. Keeping the sigma-level action a separate function puts the
dependent shape and arity-hom projections behind one non-dependent argument,
which is what makes the rewrites below applicable. -/
def domHomFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (φ : DomHom F F')
    (Z : Iᵒᵖ ⥤ Type uB) (x : F.toPresheafDomPFunctorData.obj Z) :
    F'.toPresheafDomPFunctorData.obj Z :=
  (objEquivSigmaArityHom F' Z).symm (domHomSigma F F' φ (objEquivSigmaArityHom F Z x))

/-- `domHomFamily` on an element presented by its shape and arity hom. -/
theorem domHomFamily_symm (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (φ : DomHom F F') {Z : Iᵒᵖ ⥤ Type uB} (p : Σ a : F.A, ArityHom F a Z) :
    domHomFamily F F' φ Z ((objEquivSigmaArityHom F Z).symm p) =
      (objEquivSigmaArityHom F' Z).symm (domHomSigma F F' φ p) := by
  rw [domHomFamily, Equiv.apply_symm_apply]

/-- The representation theorem, unbundled: morphism data at the domain level is
the same thing as a family `T Z → T' Z` natural in `Z`. The inverse is Yoneda —
evaluation at the representing presheaf `arityPresheaf F a` on the generic
element `idElt F a`. -/
def domHomEquivNatFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    DomHom F F' ≃ DomNatFamily F F' where
  toFun φ :=
    ⟨domHomFamily F F' φ, by
      intro Z Z' ν x
      obtain ⟨p, rfl⟩ : ∃ p, (objEquivSigmaArityHom F Z).symm p = x :=
        ⟨_, Equiv.symm_apply_apply _ x⟩
      rw [map_symm_arityHom, domHomFamily_symm, domHomFamily_symm, map_symm_arityHom]
      rfl⟩
  invFun η a :=
    objEquivSigmaArityHom F' (arityPresheaf F a) (η.1 (arityPresheaf F a) (idElt F a))
  left_inv φ :=
    funext fun a ↦ by
      simp only [domHomFamily, Equiv.apply_symm_apply, objEquivSigmaArityHom_idElt]
      rfl
  right_inv η := by
    refine Subtype.ext (funext fun Z ↦ funext fun x ↦ ?_)
    obtain ⟨p, rfl⟩ : ∃ p, (objEquivSigmaArityHom F Z).symm p = x :=
      ⟨_, Equiv.symm_apply_apply _ x⟩
    conv_rhs =>
      rw [← map_idElt F p, η.2,
        ← Equiv.symm_apply_apply (objEquivSigmaArityHom F' (arityPresheaf F p.1))
          (η.1 (arityPresheaf F p.1) (idElt F p.1)),
        map_symm_arityHom]
    exact domHomFamily_symm F F' _ p

end UnbundledYoneda

end GebProto

namespace GebProto

section ShapeSide

/-!
The `J`-side of the morphism type: the shape map is a morphism of shape
presheaves, and the arity map is natural over `el(T₁)ᵒᵖ`, not merely over each
fibre of `q` separately.

`ShapeHom` is `ArityHom`'s recipe transposed: a family of fibre maps subject to
a naturality predicate, the fibres now `F.Shape j` and the restriction maps
`shapeRestr`.

`PshHom`'s third law is the `el(T₁)ᵒᵖ` naturality of the arity map, and it does
not typecheck on the nose. For `g : j' ⟶ j` and `a : F.Shape j`, one route runs
the arity map at `F.shapeRestr g a` and then `F.reindex g a`; the other runs
`F'.reindex g (σ j a)` and then the arity map at `a`. The second route's source
is `F'.Direction (F'.shapeRestr g (σ j a)).1 i`, the first route's is
`F'.Direction (σ j' (F.shapeRestr g a)).1 i`, and those two shapes agree only by
the `ShapeHom` naturality of `σ`. The law is therefore stated across a `cast`
along that equality — the device `PresheafPFunctorData.ReindexId` and
`ReindexComp` use, whose transports are likewise supplied by an earlier law
rather than by definitional equality. Here the law is bundled with `σ` in
`ShapeHom`, so the transport is threaded through `shape.2` rather than through
an extra parameter.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The unbundled presheaf hom `T₁ ⟶ T₁'`: a family of fibre maps
`F.Shape j → F'.Shape j` subject to the naturality square against
`shapeRestr`. -/
def ShapeHom (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) : Type (max uJ uA) :=
  { σ : (j : J) → F.Shape j → F'.Shape j //
      ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j),
        σ j' (F.shapeRestr g a) = F'.shapeRestr g (σ j a) }

/-- A morphism of presheaf p.r.a. functors, unbundled: a morphism `σ` of shape
presheaves, an arity map backwards at each shape — a morphism of arity
presheaves, so `q`-fibrewise this is `DomHom`'s data — and the `el(T₁)ᵒᵖ`
naturality of that arity map, stated across the `cast` along `σ`'s own
naturality. -/
structure PshHom (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    Type (max uI uJ uA uB) where
  /-- The shape map, a morphism of shape presheaves. -/
  shape : ShapeHom F F'
  /-- The arity map, backwards, a morphism of arity presheaves. -/
  arity : (j : J) → (a : F.Shape j) → ArityHom F' (shape.1 j a).1 (arityPresheaf F a.1)
  /-- Naturality of `arity` over `el(T₁)ᵒᵖ`: restricting the shape along `g` and
  then reindexing agrees with reindexing in `F'` and then restricting, once the
  source of the second route is transported along `shape.2`. -/
  reindexCompat : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) ⦃i : I⦄
      (d : F'.Direction (shape.1 j' (F.shapeRestr g a)).1 i),
    F.reindex g a ((arity j' (F.shapeRestr g a)).1 i d) =
      (arity j a).1 i (F'.reindex g (shape.1 j a)
        (cast (congrArg (fun s : F'.Shape j' ↦ F'.Direction s.1 i) (shape.2 g a)) d))

/-- The identity morphism. The `cast` in `reindexCompat` is along `rfl`, so the
law reduces to reflexivity — the smallest check that the transport is threaded
in the direction that makes the two routes comparable. -/
def idPshHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) : PshHom F F where
  shape := ⟨fun _ a ↦ a, fun _ _ _ _ ↦ rfl⟩
  arity _ a := idArityHom F a.1
  reindexCompat _ _ _ _ _ _ := rfl

end ShapeSide

end GebProto

namespace GebProto

section ShapeSideAction

/-!
The action of a `PshHom` on the p.r.a. formula, and the two laws that make it a
map of output presheaves. The `Z`-naturality is `DomHom`'s and needs nothing new;
the `J`-restriction law is what tests clause (c) of `PshHom`: the two sides have
different shapes, equal only by the `ShapeHom` naturality of `φ.shape`, and the
components agree exactly when `reindexCompat` holds. So `pshHomObj_objRestr` is
not merely well-typed with clause (c) present — it is unprovable without it.

`PresheafPFunctor.value_objRestrElt` is `private` upstream. Stating the
restriction lemma on the `symm` side of `objEquivSigmaArityHom` does not avoid
it: `objRestrElt` of an `ofArityHomElt` is not `ofArityHomElt` of the reindexed
arity hom on the nose, the two direction-assignments differing by the transport
along a direction's own base-point constraint. That transport is the content of
`value_objRestrElt`, so it is restated here instead.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The component the restricted element assigns to a direction is the component
the original assigns to the direction's `reindex`. Local restatement of the
`private` `PresheafPFunctor.value_objRestrElt`. -/
theorem value_objRestrElt (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) (hq : F.q x.1.1 = j)
    ⦃i : I⦄ (b : F.Direction (F.objRestrElt g x hq).1.1 i) :
    F.value (F.objRestrElt g x hq) b = F.value x (F.reindex g ⟨x.1.1, hq⟩ b) := by
  obtain ⟨b1, rfl⟩ := b
  rfl

/-- Precomposition of an unbundled arity hom with `reindex g a`, which is a
morphism of arity presheaves by `reindex_naturality`. -/
def reindexArityHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ}
    ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    ArityHom F (F.shapeRestr g a).1 Z :=
  ⟨fun i d ↦ μ.1 i (F.reindex g a d), by
    intro i i' f d
    refine Eq.trans (congrArg (μ.1 i') ?_) (μ.2 f (F.reindex g a d))
    exact (congrFun (F.isFunctorial.reindex_naturality g a f) d).symm⟩

/-- The `J`-restriction on the coproduct-of-representables side: the shape is
restricted along `shapeRestr` and the arity hom is precomposed with `reindex`. -/
def objRestrSigma (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ}
    ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.A) (hq : F.q a = j) (μ : ArityHom F a Z) :
    Σ a' : F.A, ArityHom F a' Z :=
  ⟨(F.shapeRestr g ⟨a, hq⟩).1, reindexArityHom F g ⟨a, hq⟩ μ⟩

/-- Under `objEquivSigmaArityHom`, the `J`-restriction is `objRestrSigma`. -/
theorem objEquivSigmaArityHom_objRestr (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.A) (hq : F.q a = j)
    (μ : ArityHom F a Z) :
    objEquivSigmaArityHom F Z
        (F.objRestr g ((objEquivSigmaArityHom F Z).symm ⟨a, μ⟩) hq) =
      objRestrSigma F g a hq μ := by
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun i ↦ funext fun d ↦ ?_)))
  exact (value_objRestrElt F g _ hq d).trans (value_ofArityHom F a μ _)

/-- The same on the `symm` side, which is the form the action below rewrites
with. Transported by hand rather than by `Equiv.eq_symm_apply`, which depends on
`Classical.choice`. -/
theorem objRestr_symm (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.A) (hq : F.q a = j)
    (μ : ArityHom F a Z) :
    F.objRestr g ((objEquivSigmaArityHom F Z).symm ⟨a, μ⟩) hq =
      (objEquivSigmaArityHom F Z).symm (objRestrSigma F g a hq μ) :=
  ((objEquivSigmaArityHom F Z).symm_apply_apply _).symm.trans
    (congrArg (objEquivSigmaArityHom F Z).symm (objEquivSigmaArityHom_objRestr F g a hq μ))

/-- Two shape-and-arity-hom pairs are equal when the shapes are equal and the
arity homs agree across the transport along that equality. The `cast` is along
a `Prop`-valued equality, so proof irrelevance identifies it with the `cast` of
`PshHom.reindexCompat`, which is stated along the `F'.Shape`-level equality. -/
theorem sigmaArityHom_ext (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} {a a' : F.A} (h : a = a') (μ : ArityHom F a Z) (μ' : ArityHom F a' Z)
    (hμ : ∀ (i : I) (d : F.Direction a i),
      μ.1 i d = μ'.1 i (cast (congrArg (fun t : F.A ↦ F.Direction t i) h) d)) :
    (⟨a, μ⟩ : Σ b : F.A, ArityHom F b Z) = ⟨a', μ'⟩ := by
  cases h
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun i ↦ funext fun d ↦ hμ i d)))

/-- The action of a `PshHom` on the coproduct-of-representables side: the shape
travels forward along `φ.shape`, and the arity hom is precomposed with `φ`'s
backward arity map. `DomHom`'s `domHomSigma`, now indexed by an output index. -/
def pshHomSigma (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (φ : PshHom F F')
    {Z : Iᵒᵖ ⥤ Type uB} (j : J) (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    Σ a' : F'.A, ArityHom F' a' Z :=
  ⟨(φ.shape.1 j a).1, postcompArityHom F' _ (natTransOfArityHom F a.1 μ) (φ.arity j a)⟩

/-- The fibre of the output presheaf over `j`, unbundled: the elements of
`F.obj Z` whose `q`-output index is `j`. This is `objPresheaf`'s object part
written without the functor-category instance. Bundling the index proof with the
element keeps the restriction and action laws free of the dependent-proof
argument that blocks rewriting. -/
@[reducible] def ObjFib (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (Z : Iᵒᵖ ⥤ Type uZ) (j : J) : Type (max uI uZ uA uB) :=
  { z : F.toPresheafDomPFunctorData.obj Z // F.q z.shape = j }

/-- The `J`-restriction of the output presheaf, unbundled: `objRestr` together
with the `q`-index of the restricted shape. This is `objPresheaf`'s map part. -/
def objFibRestr (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ}
    ⦃j j' : J⦄ (g : j' ⟶ j) (w : ObjFib F Z j) : ObjFib F Z j' :=
  ⟨F.objRestr g w.1 w.2, (F.shapeRestr g ⟨w.1.shape, w.2⟩).2⟩

/-- The action of an input-presheaf morphism on a fibre: the dom `map`, which
fixes the shape and so fixes the `q`-output index. -/
def objFibMap (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (ν : NatTrans Z Z') {j : J} (w : ObjFib F Z j) : ObjFib F Z' j :=
  ⟨F.toPresheafDomPFunctorData.map ν w.1, w.2⟩

/-- The fibre element with shape `a : F.Shape j` and arity hom `μ`. -/
def ofSigmaFib (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ} {j : J}
    (a : F.Shape j) (μ : ArityHom F a.1 Z) : ObjFib F Z j :=
  ⟨(objEquivSigmaArityHom F Z).symm ⟨a.1, μ⟩, a.2⟩

/-- Every fibre element is `ofSigmaFib` of its own shape and arity hom, which is
what lets the laws below be proved on `ofSigmaFib` alone. -/
theorem ofSigmaFib_self (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} {j : J} (w : ObjFib F Z j) :
    ofSigmaFib F ⟨w.1.shape, w.2⟩ (objEquivSigmaArityHom F Z w.1).2 = w :=
  Subtype.ext ((objEquivSigmaArityHom F Z).symm_apply_apply w.1)

/-- The `J`-restriction of an `ofSigmaFib`: the shape restricts and the arity
hom is precomposed with `reindex`. -/
theorem objFibRestr_ofSigmaFib (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    objFibRestr F g (ofSigmaFib F a μ) =
      ofSigmaFib F (F.shapeRestr g a) (reindexArityHom F g a μ) :=
  Subtype.ext (objRestr_symm F g a.1 a.2 μ)

/-- The input-presheaf action on an `ofSigmaFib`: the shape is untouched and the
arity hom is postcomposed. -/
theorem objFibMap_ofSigmaFib (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z Z' : Iᵒᵖ ⥤ Type uB} (ν : NatTrans Z Z') {j : J} (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    objFibMap F ν (ofSigmaFib F a μ) = ofSigmaFib F a (postcompArityHom F a.1 ν μ) :=
  Subtype.ext (map_symm_arityHom F ν ⟨a.1, μ⟩)

/-- The action of a `PshHom` on a fibre of the output presheaf. -/
def pshHomFib (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (φ : PshHom F F')
    {Z : Iᵒᵖ ⥤ Type uB} (j : J) (w : ObjFib F Z j) : ObjFib F' Z j :=
  ⟨(objEquivSigmaArityHom F' Z).symm
      (pshHomSigma F F' φ j ⟨w.1.shape, w.2⟩ (objEquivSigmaArityHom F Z w.1).2),
    (φ.shape.1 j ⟨w.1.shape, w.2⟩).2⟩

/-- The action on an `ofSigmaFib`: the shape travels along `φ.shape`, and the
arity hom is `φ`'s backward arity map followed by the original. -/
theorem pshHomFib_ofSigmaFib (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (φ : PshHom F F') {Z : Iᵒᵖ ⥤ Type uB} {j : J} (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    pshHomFib F F' φ j (ofSigmaFib F a μ) =
      ofSigmaFib F' (φ.shape.1 j a)
        (postcompArityHom F' _ (natTransOfArityHom F a.1 μ) (φ.arity j a)) :=
  Subtype.ext (congrArg (objEquivSigmaArityHom F' Z).symm
    (congrArg (pshHomSigma F F' φ j a)
      (Subtype.ext (funext fun _i ↦ funext fun b ↦ value_ofArityHom F a.1 μ b))))

/-- Naturality of the action in the input presheaf. Nothing beyond `DomHom`'s
argument: both sides postcompose the same two arity homs. -/
theorem pshHomFib_objFibMap (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (φ : PshHom F F') {Z Z' : Iᵒᵖ ⥤ Type uB} (ν : NatTrans Z Z') (j : J) (w : ObjFib F Z j) :
    pshHomFib F F' φ j (objFibMap F ν w) = objFibMap F' ν (pshHomFib F F' φ j w) := by
  obtain ⟨a, μ, rfl⟩ : ∃ (a : F.Shape j) (μ : ArityHom F a.1 Z), ofSigmaFib F a μ = w :=
    ⟨⟨w.1.shape, w.2⟩, _, ofSigmaFib_self F w⟩
  rw [objFibMap_ofSigmaFib, pshHomFib_ofSigmaFib, pshHomFib_ofSigmaFib, objFibMap_ofSigmaFib]
  rfl

/-- Clause (c) of `PshHom` is what makes the action commute with the
`J`-restriction of the output presheaves. The two sides carry different shapes —
`φ.shape` of a restricted shape against the restriction of a `φ.shape`-image —
identified only by `φ.shape.2`, and their arity homs agree across that transport
exactly by `reindexCompat`. So the law is not merely well-typed once clause (c)
is present; clause (c) is precisely its content. -/
theorem pshHomFib_objFibRestr (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (φ : PshHom F F') {Z : Iᵒᵖ ⥤ Type uB} ⦃j j' : J⦄ (g : j' ⟶ j) (w : ObjFib F Z j) :
    pshHomFib F F' φ j' (objFibRestr F g w) = objFibRestr F' g (pshHomFib F F' φ j w) := by
  obtain ⟨a, μ, rfl⟩ : ∃ (a : F.Shape j) (μ : ArityHom F a.1 Z), ofSigmaFib F a μ = w :=
    ⟨⟨w.1.shape, w.2⟩, _, ofSigmaFib_self F w⟩
  rw [objFibRestr_ofSigmaFib, pshHomFib_ofSigmaFib, pshHomFib_ofSigmaFib,
    objFibRestr_ofSigmaFib]
  refine Subtype.ext (congrArg (objEquivSigmaArityHom F' Z).symm ?_)
  refine sigmaArityHom_ext F' (congrArg Subtype.val (φ.shape.2 g a)) _ _ fun i d ↦ ?_
  exact congrArg (μ.1 i) (φ.reindexCompat g a d)

end ShapeSideAction

end GebProto

namespace GebProto

section ShapeSideYoneda

/-!
The representation theorem on the `J`-side: `PshHom F F'` is the same thing as a
family of maps of output-presheaf fibres, natural in the input presheaf and
commuting with the `J`-restriction.

Both laws are needed and each supplies one half of the reconstruction: the
`Z`-naturality is Yoneda, recovering the shape map and the arity map from the
value at the representing presheaf `arityPresheaf F a`; the `J`-restriction law
supplies the two remaining clauses of `PshHom`, the naturality of the shape map
and `reindexCompat`, which are the shape component and the arity component of a
single equation between fibre elements.
-/

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The generic fibre element of shape `a`: the element whose arity hom is the
identity, bundled with its `q`-output index. Yoneda's representing datum. -/
def genericFib (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {j : J} (a : F.Shape j) :
    ObjFib F (arityPresheaf F a.1) j :=
  ofSigmaFib F a (idArityHom F a.1)

/-- Yoneda at the fibre level: the fibre element of shape `a` and arity hom `μ`
is the image of the generic element of shape `a` under the action of `μ`. -/
theorem ofSigmaFib_eq_objFibMap (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uB} {j : J} (a : F.Shape j) (μ : ArityHom F a.1 Z) :
    ofSigmaFib F a μ = objFibMap F (natTransOfArityHom F a.1 μ) (genericFib F a) := by
  rw [genericFib, objFibMap_ofSigmaFib]
  rfl

/-- The arity hom the p.r.a. formula reads off an `ofArityHomElt` is the one it
was built from. -/
theorem objEquivSigmaArityHom_symm_snd (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} (a : F.A) (μ : ArityHom F a Z) :
    (objEquivSigmaArityHom F Z ((objEquivSigmaArityHom F Z).symm ⟨a, μ⟩)).2 = μ :=
  Subtype.ext (funext fun _i ↦ funext fun b ↦ value_ofArityHom F a μ b)

/-- Converse of `sigmaArityHom_ext`: an equality of fibre elements whose shapes
agree gives agreement of the arity homs across the transport along that
equality. -/
theorem ofSigmaFib_apply (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z : Iᵒᵖ ⥤ Type uZ} {j : J} {s s' : F.Shape j} {γ : ArityHom F s.1 Z}
    {γ' : ArityHom F s'.1 Z} (h : ofSigmaFib F s γ = ofSigmaFib F s' γ') (hs : s = s')
    (i : I) (d : F.Direction s.1 i) :
    γ.1 i d = γ'.1 i (cast (congrArg (fun t : F.Shape j ↦ F.Direction t.1 i) hs) d) := by
  cases hs
  have hγ : (⟨s.1, γ⟩ : Σ b : F.A, ArityHom F b Z) = ⟨s.1, γ'⟩ :=
    (objEquivSigmaArityHom F Z).symm.injective (congrArg Subtype.val h)
  injection hγ with _ h2
  cases h2
  rfl

/-- The arity component of an equality between an input-presheaf image and a
`J`-restriction of fibre elements, once their shapes are known to agree. -/
theorem objFibMap_eq_objFibRestr_apply (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    {Z Z' : Iᵒᵖ ⥤ Type uB} (ν : NatTrans Z Z') ⦃j j' : J⦄ (g : j' ⟶ j)
    (u : ObjFib F Z j') (v : ObjFib F Z' j)
    (h : objFibMap F ν u = objFibRestr F g v)
    (hs : (⟨u.1.shape, u.2⟩ : F.Shape j') = F.shapeRestr g ⟨v.1.shape, v.2⟩)
    (i : I) (d : F.Direction u.1.shape i) :
    (postcompArityHom F u.1.shape ν (objEquivSigmaArityHom F Z u.1).2).1 i d =
      (reindexArityHom F g ⟨v.1.shape, v.2⟩ (objEquivSigmaArityHom F Z' v.1).2).1 i
        (cast (congrArg (fun t : F.Shape j' ↦ F.Direction t.1 i) hs) d) := by
  refine ofSigmaFib_apply F ?_ hs i d
  exact ((objFibMap_ofSigmaFib F ν ⟨u.1.shape, u.2⟩
      (objEquivSigmaArityHom F Z u.1).2).symm.trans
    ((congrArg (objFibMap F ν) (ofSigmaFib_self F u)).trans h)).trans
    ((congrArg (objFibRestr F g) (ofSigmaFib_self F v).symm).trans
      (objFibRestr_ofSigmaFib F g ⟨v.1.shape, v.2⟩ (objEquivSigmaArityHom F Z' v.1).2))

/-- Families of maps of output-presheaf fibres, natural in the input presheaf
and commuting with the `J`-restriction. The `J`-restriction is stated unbundled
against `objFibRestr` (that is, `PresheafPFunctor.objRestr`) rather than via
`objPresheaf.map`. Both are choice-free — `objPresheaf` is a functor into
`Type`, not an object of a functor category — so the unbundled form is a
presentational choice, not a constructivity one. -/
def PshNatFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    Type (max uA uI uJ vI (uB + 1)) :=
  { η : (Z : Iᵒᵖ ⥤ Type uB) → (j : J) → ObjFib F Z j → ObjFib F' Z j //
      (∀ (Z Z' : Iᵒᵖ ⥤ Type uB) (ν : NatTrans Z Z') (j : J) (w : ObjFib F Z j),
          η Z' j (objFibMap F ν w) = objFibMap F' ν (η Z j w)) ∧
        ∀ (Z : Iᵒᵖ ⥤ Type uB) ⦃j j' : J⦄ (g : j' ⟶ j) (w : ObjFib F Z j),
          η Z j' (objFibRestr F g w) = objFibRestr F' g (η Z j w) }

/-- The natural family determined by a `PshHom`. -/
def pshHomFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (φ : PshHom F F') :
    PshNatFamily F F' :=
  ⟨fun _ j ↦ pshHomFib F F' φ j,
    ⟨fun _ _ ν j w ↦ pshHomFib_objFibMap F F' φ ν j w,
      fun _ _ _ g w ↦ pshHomFib_objFibRestr F F' φ g w⟩⟩

/-- The equation the reconstruction rests on: the generic element of the
restricted shape, pushed along `reindex`, is the restriction of the generic
element. Both remaining `PshHom` clauses are components of it. -/
theorem natFamily_generic (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (η : PshNatFamily F F') ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) :
    objFibMap F'
        (natTransOfArityHom F (F.shapeRestr g a).1 (reindexArityHom F g a (idArityHom F a.1)))
        (η.1 (arityPresheaf F (F.shapeRestr g a).1) j' (genericFib F (F.shapeRestr g a))) =
      objFibRestr F' g (η.1 (arityPresheaf F a.1) j (genericFib F a)) := by
  rw [← η.2.1, ← ofSigmaFib_eq_objFibMap, ← objFibRestr_ofSigmaFib]
  exact η.2.2 _ g (genericFib F a)

/-- The shape map recovered from a natural family: the shape of its value on the
generic element. Its naturality is the shape component of `natFamily_generic`. -/
def natFamilyShape (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (η : PshNatFamily F F') : ShapeHom F F' :=
  ⟨fun j a ↦ ⟨(η.1 (arityPresheaf F a.1) j (genericFib F a)).1.shape,
      (η.1 (arityPresheaf F a.1) j (genericFib F a)).2⟩,
    fun _ _ g a ↦ Subtype.ext (congrArg (fun w ↦ w.1.shape) (natFamily_generic F F' η g a))⟩

/-- The arity map recovered from a natural family: the arity hom of its value on
the generic element. -/
def natFamilyArity (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (η : PshNatFamily F F') (j : J) (a : F.Shape j) :
    ArityHom F' ((natFamilyShape F F' η).1 j a).1 (arityPresheaf F a.1) :=
  (objEquivSigmaArityHom F' (arityPresheaf F a.1)
    (η.1 (arityPresheaf F a.1) j (genericFib F a)).1).2

/-- The `PshHom` recovered from a natural family. `reindexCompat` is the arity
component of `natFamily_generic`, read off across the transport along the shape
component of the same equation. -/
def natFamilyPshHom (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (η : PshNatFamily F F') : PshHom F F' where
  shape := natFamilyShape F F' η
  arity := natFamilyArity F F' η
  reindexCompat := by
    intro j j' g a i d
    exact objFibMap_eq_objFibRestr_apply F'
      (natTransOfArityHom F (F.shapeRestr g a).1 (reindexArityHom F g a (idArityHom F a.1)))
      g _ _ (natFamily_generic F F' η g a) ((natFamilyShape F F' η).2 g a) i d

/-- Two `PshHom`s with equal shape maps and arity maps are equal; the remaining
field is a `Prop`. -/
theorem pshHom_ext (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {φ ψ : PshHom F F'}
    (hs : φ.shape = ψ.shape) (ha : φ.arity ≍ ψ.arity) : φ = ψ := by
  obtain ⟨σ, α, hc⟩ := φ
  obtain ⟨σ', α', hc'⟩ := ψ
  cases hs
  cases ha
  rfl

/-- The arity map recovered from the family of a `PshHom` is the original: the
generic element's arity hom is the identity, so the postcomposition it induces
is trivial. -/
theorem natFamilyArity_pshHomFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (φ : PshHom F F') (j : J) (a : F.Shape j) :
    natFamilyArity F F' (pshHomFamily F F' φ) j a = φ.arity j a :=
  (objEquivSigmaArityHom_symm_snd F' _ _).trans
    (Subtype.ext (funext fun i ↦ funext fun b ↦
      value_ofArityHom F a.1 (idArityHom F a.1) ((φ.arity j a).1 i b)))

/-- The representation theorem on the `J`-side: the full morphism data of
presheaf p.r.a. functors is the same thing as a family of maps of
output-presheaf fibres, natural in the input presheaf and commuting with the
`J`-restriction. -/
def pshHomEquivNatFamily (F F' : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    PshHom F F' ≃ PshNatFamily F F' where
  toFun := pshHomFamily F F'
  invFun := natFamilyPshHom F F'
  left_inv φ :=
    pshHom_ext F F' rfl
      (heq_of_eq (funext fun j ↦ funext fun a ↦ natFamilyArity_pshHomFamily F F' φ j a))
  right_inv η := by
    refine Subtype.ext (funext fun Z ↦ funext fun j ↦ funext fun w ↦ ?_)
    obtain ⟨a, μ, rfl⟩ : ∃ (a : F.Shape j) (μ : ArityHom F a.1 Z), ofSigmaFib F a μ = w :=
      ⟨⟨w.1.shape, w.2⟩, _, ofSigmaFib_self F w⟩
    change pshHomFib F F' (natFamilyPshHom F F' η) j (ofSigmaFib F a μ) =
      η.1 Z j (ofSigmaFib F a μ)
    refine (pshHomFib_ofSigmaFib F F' (natFamilyPshHom F F' η) a μ).trans ?_
    refine Eq.trans ?_ (congrArg (η.1 Z j) (ofSigmaFib_eq_objFibMap F a μ)).symm
    refine Eq.trans ?_
      (η.2.1 (arityPresheaf F a.1) Z (natTransOfArityHom F a.1 μ) j (genericFib F a)).symm
    exact (objFibMap_ofSigmaFib F' (natTransOfArityHom F a.1 μ)
        ⟨(η.1 (arityPresheaf F a.1) j (genericFib F a)).1.shape,
          (η.1 (arityPresheaf F a.1) j (genericFib F a)).2⟩
        (objEquivSigmaArityHom F' (arityPresheaf F a.1)
          (η.1 (arityPresheaf F a.1) j (genericFib F a)).1).2).symm.trans
      (congrArg (objFibMap F' (natTransOfArityHom F a.1 μ))
        (ofSigmaFib_self F' (η.1 (arityPresheaf F a.1) j (genericFib F a))))

end ShapeSideYoneda

end GebProto



