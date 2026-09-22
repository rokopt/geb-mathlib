/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType
public meta import Geb.Prototypes.MType -- shake: keep; #guard needs it
public import Geb.Prototypes.BitStream
public meta import Geb.Prototypes.BitStream -- shake: keep; #guard needs it
public import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures
public meta import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures -- shake: keep; #guard needs it

set_option doc.verso true in
/-!
# Executable observations of M-types constructed from W-types

The checks read the labels along paths of an infinite binary tree built by the
corecursor, of a tree built by the constructor over it, and of a bitstream,
through the destructor, and through the equivalence with mathlib's M-type.
They exercise the compiled dependent eliminator on depths and the slice and
presheaf W-tree encodings of the observations. For the slice M-type they read
the indices of an infinite stream whose index alternates; for the presheaf
M-type, the shapes and indices of the infinite hereditarily natural tree of
the shared walking-arrow fixture, built by the presheaf corecursor, and of its
restriction along the arrow.

## Tags

M-type, W-type, corecursion, test
-/
set_option doc.verso true

-- The fixtures are `@[expose]`d: the code generator rejects a definition whose
-- type mentions a non-exposed type definition, such as the fixture polynomial,
-- even within this module, and `expose` applies to public definitions only.
@[expose] public section

namespace GebTests.MType

open Geb.MType

/-- Infinite binary trees labelled by natural numbers. -/
abbrev labelled : PFunctor.{0, 0} := ⟨ℕ, fun _ ↦ Bool⟩

/-- The coalgebra labelling each node by its breadth-first index. -/
def heapStep (n : ℕ) : labelled.Obj ℕ := ⟨n, fun b ↦ if b then 2 * n + 2 else 2 * n + 1⟩

/-- The breadth-first labelled tree. -/
def heap : M labelled := M.corec heapStep 0

/-- The label at the end of a path of directions. -/
def labelAt (ps : List Bool) (t : M labelled) : ℕ :=
  (ps.foldl (fun t b ↦ t.children b) t).head

#guard labelAt [] heap = 0

#guard labelAt [true, false] heap = 5

#guard labelAt [false, false, true] heap = 8

/-- A root labelled seven over two copies of the breadth-first tree. -/
def grafted : M labelled := M.mk ⟨7, fun _ ↦ heap⟩

#guard labelAt [] grafted = 7

#guard labelAt [true, true] grafted = 2

#guard PFunctor.M.head (mEquiv labelled heap) = 0

#guard PFunctor.M.head (PFunctor.M.children (mEquiv labelled grafted) true) = 0

/-- The alternating bitstream, as an element of the general construction at
the bitstream polynomial. -/
def alternating : M Geb.BitStream.sig :=
  M.corec (fun b : Bool ↦ ⟨some b, fun _ ↦ !b⟩) false

#guard (Geb.BitStream.seqEquiv (mEquiv _ alternating)).take 4 = [false, true, false, true]

/-! ## The slice M-type -/

/-- Streams over {name}`Bool` whose index alternates: the shape is its own
index, and its one child lies over the other index. -/
def alternatingSig : SlicePFunctor.{0, 0, 0, 0} Bool Bool where
  A := Bool
  B _ := Unit
  r x := !x.1
  q a := a

/-- The slice coalgebra on {name}`Bool`: each index has a node over the
other. -/
def alternatingStep (b : Bool) : alternatingSig.toSliceDomPFunctor.Obj (id : Bool → Bool) :=
  ⟨⟨b, fun _ ↦ !b⟩, rfl⟩

/-- The alternating stream from index {name}`true`. -/
def alternatingStream : SliceM alternatingSig :=
  SliceM.corec alternatingSig id alternatingStep rfl true

#guard SliceM.index alternatingSig alternatingStream = true

#guard SliceM.index alternatingSig (alternatingStream.dest.1.2 ()) = false

#guard SliceM.index alternatingSig ((alternatingStream.dest.1.2 ()).dest.1.2 ()) = true

/-! ## The presheaf M-type -/

open CategoryTheory PresheafFixture

/-- The terminal presheaf, the state space of the fixture's coalgebra. -/
@[reducible] def unitY : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := 𝟙 _

/-- The node the coalgebra gives the unique state over an index: the leaf
{name}`Shp.L0a` over {lit}`0`, and over {lit}`1` the branching shape {name}`Shp.R`,
whose children are the states over the indices of its directions. -/
def unitNode (i : Fin 2) : (wFixture.objPresheaf unitY).obj ⟨i⟩ :=
  match i with
  | 0 => ⟨⟨⟨⟨.L0a, fun b ↦ b.elim0⟩, funext fun b ↦ b.elim0⟩, fun _ _ _ b ↦ b.1.elim0⟩, rfl⟩
  | 1 => ⟨⟨⟨⟨.R, fun b ↦ ⟨b, PUnit.unit⟩⟩, rfl⟩, fun _ _ _ _ ↦ rfl⟩, rfl⟩

/-- The coalgebra: restricting the node over {lit}`1` along the arrow gives
the node over {lit}`0`. -/
def unitStep : NatTrans unitY (wFixture.objPresheaf unitY) where
  app j := ↾ fun _ ↦ unitNode j.unop
  naturality X X' f := by
    ext u
    obtain ⟨x⟩ := X
    obtain ⟨x'⟩ := X'
    change unitNode x' = (wFixture.objPresheaf unitY).map f (unitNode x)
    match x, x', f with
    | 0, 0, f =>
      obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      exact (Functor.map_id_apply (wFixture.objPresheaf unitY) _ _).symm
    | 1, 1, f =>
      obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      exact (Functor.map_id_apply (wFixture.objPresheaf unitY) _ _).symm
    | 1, 0, _ =>
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ b.elim0))
    | 0, 1, f => exact absurd (leOfHom f.unop) (by decide)

/-- The infinite hereditarily natural tree over {lit}`1`: an {name}`Shp.R` spine
whose children over {lit}`0` are {name}`Shp.L0a` leaves. -/
def spine : (PresheafM wFixture).obj ⟨1⟩ := (PresheafM.corec wFixture unitY unitStep).app ⟨1⟩ ()

/-- The child of a tree at a direction of {name}`Shp.R`, when its root shape is
{name}`Shp.R`. -/
def rChild (t : M wFixture.toPFunctor) (b : Fin 2) : Option (M wFixture.toPFunctor) :=
  match h : t.head with
  | .R => some (t.children (cast (congrArg BFix h.symm) b))
  | _ => none

#guard spine.down.1.1.head = Shp.R

#guard (rChild spine.down.1.1 0).map M.head = some Shp.L0a

#guard (rChild spine.down.1.1 1).map M.head = some Shp.R

#guard ((rChild spine.down.1.1 1).bind (rChild · 0)).map M.head = some Shp.L0a

#guard SliceM.index wFixture.toSlicePFunctor spine.down.1 = 1

#guard ((PresheafM wFixture).map PresheafPFunctor.arrow.op spine).down.1.1.head = Shp.L0a

end GebTests.MType
