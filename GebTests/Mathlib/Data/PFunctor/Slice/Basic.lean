/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the slice polynomial functor core
-/

open SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor: one shape, two `Bool`-indexed
positions, constraint `s ⟨(), b⟩ = b`, tag into `Unit`. -/
def testSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ => Bool
  s := fun x => x.2
  t := fun _ => ()

example : testSlice.s ⟨(), true⟩ = true := rfl
example : testSlice.t () = () := rfl

example (X : Type) (p : X → Bool) (v : Bool → X) :
    testSlice.Compatible p () v ↔ ∀ b, p (v b) = b :=
  testSlice.compatible_iff p () v

example (P : PFunctor.{0, 0}) (sc : (a : P.A) → P.B a → Bool) (a : P.A)
    (b : P.B a) : (SliceDomPFunctor.ofCurried P Bool sc).sCurried a b = sc a b :=
  rfl

-- The object map is the compatibility subtype of the interpretation.
example : testSlice.toSliceDomPFunctor.obj (id : Bool → Bool) =
    { x : (testSlice.toPFunctor).Obj Bool //
      testSlice.toSliceDomPFunctor.Compatible (id : Bool → Bool) x.1 x.2 } := rfl

-- The action fixes the shape.
example (X : Type) (p p' : X → Bool) (f : X → X) (hf : p' ∘ f = p)
    (z : testSlice.toSliceDomPFunctor.obj p) :
    (testSlice.toSliceDomPFunctor.map f hf z).1.1 = z.1.1 :=
  testSlice.toSliceDomPFunctor.map_fst f hf z

-- The slice object's structure map into `cod` is the tag at the shape.
example (X : Type) (p : X → Bool) (z : testSlice.toSliceDomPFunctor.obj p) :
    testSlice.obj p z = testSlice.t z.1.1 := rfl

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
      (id : testSlice.toSliceDomPFunctor.obj p → testSlice.toSliceDomPFunctor.obj p) :=
  testSlice.map_id p

example (X Y Z : Type) (p : X → Bool) (q : Y → Bool) (r : Z → Bool)
    (f : X → Y) (g : Y → Z) (hf : q ∘ f = p) (hg : r ∘ g = q) :
    testSlice.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) =
      testSlice.map g hg ∘ testSlice.map f hf :=
  testSlice.map_comp f g hf hg

/-- A slice functor whose tag `t = id` distinguishes its two shapes, so the
tag content of `obj` is genuinely exercised. -/
def taggedSlice : SlicePFunctor Bool Bool where
  A := Bool
  B := fun _ => Bool
  s := fun x => x.2
  t := id

-- `obj` reads the tag at the shape: with `t = id`, it is the shape
-- projection (this fails for any tag that does not separate the shapes).
example (X : Type) (p : X → Bool) :
    taggedSlice.obj p = fun z => z.1.1 := rfl

-- `map_w` over a genuinely-tagged functor: the morphism lies over `cod`.
example (X X' : Type) (p : X → Bool) (p' : X' → Bool) (f : X → X')
    (hf : p' ∘ f = p) : taggedSlice.obj p' ∘ taggedSlice.map f hf = taggedSlice.obj p :=
  taggedSlice.map_w f hf

-- Position is the constraint-leg fibre; the predicate is its membership.
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) :
    F.Position a i = { b : F.B a // F.s ⟨a, b⟩ = i } := rfl
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) (b : F.B a) :
    F.PositionOver a i b ↔ F.s ⟨a, b⟩ = i := Iff.rfl

example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) :
    F.Shape j = { a : F.A // F.t a = j } := rfl
example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) (a : F.A) :
    F.ShapeOver j a ↔ F.t a = j := Iff.rfl
