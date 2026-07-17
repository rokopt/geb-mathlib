/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!
# Tests for the slice polynomial functor core

Concrete slice polynomial functors over `Bool` exercise the
structures, the compatibility predicate, the object and morphism maps
with their functoriality, and the fibre formers, mostly by `rfl`.

## Tags

polynomial functor, slice category, container, PFunctor
-/

set_option linter.privateModule false

open SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor: one shape, two `Bool`-indexed
directions, constraint `r ⟨(), b⟩ = b`, output index into `Unit`. -/
def testSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ ↦ Bool
  r := fun x ↦ x.2
  q := fun _ ↦ ()

example : testSlice.r ⟨(), true⟩ = true := rfl
example : testSlice.q () = () := rfl

example (X : Type) (p : X → Bool) (v : Bool → X) :
    testSlice.Compatible p () v ↔ ∀ b, p (v b) = b :=
  testSlice.compatible_iff p () v

example (P : PFunctor.{0, 0}) (sc : (a : P.A) → P.B a → Bool) (a : P.A)
    (b : P.B a) : (SliceDomPFunctor.ofCurried P Bool sc).rCurried a b = sc a b :=
  rfl

-- The object map is the compatibility subtype of the interpretation.
example : testSlice.toSliceDomPFunctor.Obj (id : Bool → Bool) =
    { x : (testSlice.toPFunctor).Obj Bool //
      testSlice.toSliceDomPFunctor.Compatible (id : Bool → Bool) x.1 x.2 } := rfl

-- The action fixes the shape.
example (X : Type) (p p' : X → Bool) (f : X → X) (hf : p' ∘ f = p)
    (z : testSlice.toSliceDomPFunctor.Obj p) :
    (testSlice.toSliceDomPFunctor.map f hf z).1.1 = z.1.1 :=
  testSlice.toSliceDomPFunctor.map_fst f hf z

-- The slice object's structure map into `cod` is the output index (`q`) at the shape.
example (X : Type) (p : X → Bool) (z : testSlice.toSliceDomPFunctor.Obj p) :
    testSlice.obj p z = testSlice.q z.1.1 := rfl

-- The slice morphism's underlying function is the `SliceDomPFunctor` map.
example (X : Type) (p p' : X → Bool) (f : X → X) (hf : p' ∘ f = p) :
    testSlice.map f hf = testSlice.toSliceDomPFunctor.map f hf := rfl

-- The morphism lies over `cod`.
example (X : Type) (p p' : X → Bool) (f : X → X) (hf : p' ∘ f = p) :
    testSlice.obj p' ∘ testSlice.map f hf = testSlice.obj p :=
  testSlice.map_w f hf

-- Functoriality: identity and composition.
example (X : Type) (p : X → Bool) :
    testSlice.map id (by simp) =
      (id : testSlice.toSliceDomPFunctor.Obj p → testSlice.toSliceDomPFunctor.Obj p) :=
  testSlice.map_id p

example (X Y Z : Type) (p : X → Bool) (p' : Y → Bool) (p'' : Z → Bool)
    (f : X → Y) (g : Y → Z) (hf : p' ∘ f = p) (hg : p'' ∘ g = p') :
    testSlice.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) =
      testSlice.map g hg ∘ testSlice.map f hf :=
  testSlice.map_comp f g hf hg

-- A self-contained concrete computation of the morphism action over `dom = Bool`,
-- not routed through any dependent module. Compatibility over `(Bool, id)` forces
-- the direction assignment to `id`; the slice morphism `sliceMor` lifts it.
/-- The compatible element of `Obj (id : Bool → Bool)`: one shape, assignment `id`. -/
private def sliceElt : testSlice.toSliceDomPFunctor.Obj (id : Bool → Bool) :=
  ⟨⟨(), id⟩, (testSlice.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩

/-- A non-identity slice morphism `(Bool, id) ⟶ (Bool × Bool, Prod.fst)`. -/
private def sliceMor : Bool → Bool × Bool := fun b ↦ (b, !b)

example : Prod.fst ∘ sliceMor = (id : Bool → Bool) := rfl

-- The action post-composes the direction assignment with `sliceMor`.
example :
    (testSlice.toSliceDomPFunctor.map (p' := Prod.fst) sliceMor rfl sliceElt).1.2 = sliceMor :=
  rfl
example :
    (testSlice.toSliceDomPFunctor.map (p' := Prod.fst) sliceMor rfl sliceElt).1.2 false =
      (false, true) := rfl

-- The shape component is fixed by the action.
example :
    (testSlice.toSliceDomPFunctor.map (p' := Prod.fst) sliceMor rfl sliceElt).1.1 = () := rfl

/-- A slice functor whose shape-output map `q = id` distinguishes its two
shapes, so the output-index content of `obj` is genuinely exercised. -/
def separatingSlice : SlicePFunctor Bool Bool where
  A := Bool
  B := fun _ ↦ Bool
  r := fun x ↦ x.2
  q := id

-- `obj` reads the output index at the shape: with `q = id`, it is the shape
-- projection (this fails for any output index that does not separate the shapes).
example (X : Type) (p : X → Bool) :
    separatingSlice.obj p = fun z ↦ z.1.1 := rfl

-- `map_w` over a functor with a separating output index: the morphism lies over `cod`.
example (X X' : Type) (p : X → Bool) (p' : X' → Bool) (f : X → X')
    (hf : p' ∘ f = p) : separatingSlice.obj p' ∘ separatingSlice.map f hf = separatingSlice.obj p :=
  separatingSlice.map_w f hf

-- Direction is the direction-input-map fibre; the predicate is its membership.
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) :
    F.Direction a i = { b : F.B a // F.r ⟨a, b⟩ = i } := rfl
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) (b : F.B a) :
    F.DirectionOver a i b ↔ F.r ⟨a, b⟩ = i := Iff.rfl

example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) :
    F.Shape j = { a : F.A // F.q a = j } := rfl
example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) (a : F.A) :
    F.ShapeOver j a ↔ F.q a = j := Iff.rfl
