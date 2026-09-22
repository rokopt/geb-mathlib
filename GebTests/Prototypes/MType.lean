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

set_option doc.verso true in
/-!
# Executable observations of M-types constructed from W-types

The checks read the labels along paths of an infinite binary tree built by the
corecursor, of a tree built by the constructor over it, and of a bitstream,
through the destructor, and through the equivalence with mathlib's M-type.
They exercise the compiled dependent eliminator on depths and the slice and
presheaf W-tree encodings of the observations. For the slice M-type they read
the indices of an infinite stream whose index alternates.

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

end GebTests.MType
