/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.UnionFind.OfEdges
public meta import Geb.Mathlib.Data.UnionFind.OfEdges  -- shake: keep; #guard needs it

/-!
# Tests for the size-indexed union-find

A fold over a small edge list, asserted by `#guard`. What is checked
is the partition the fold induces — roots equal within each class,
unequal across — not the root map itself: which representative a
class gets is union by rank's business, an internal of Batteries'
algorithm.

Nothing built from `UnionFind.union` or `rootD` reduces in the kernel,
`root`, `findAux` and `find` being well-founded recursions whose
measure is the `noncomputable` `rankMax`. The assertions are therefore
`#guard` rather than `by decide` or `by rfl`, and each goes through a
locally declared wrapper.

## Tags

union-find, disjoint set, test
-/

@[expose] public section

open Batteries

/-- A three-element edge list over `Fin 5`, merging `0`, `1`, `2` and,
separately, `3` and `4`. -/
def sampleEdges : List (Fin 5 × Fin 5) :=
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
   (⟨3, by decide⟩, ⟨4, by decide⟩)]

/-- The union-find the sample edges induce. -/
def sampleUnionFind : UnionFind.Sized 5 :=
  UnionFind.Sized.ofEdges 5 sampleEdges

/-- The root of a sample index, as a `Nat`. The wrapper is what the
`#guard`s below name; see the module docstring. -/
def sampleRoot (i : Fin 5) : Nat := (sampleUnionFind.root i).val

#guard sampleRoot ⟨0, by decide⟩ == sampleRoot ⟨1, by decide⟩
#guard sampleRoot ⟨1, by decide⟩ == sampleRoot ⟨2, by decide⟩
#guard sampleRoot ⟨3, by decide⟩ == sampleRoot ⟨4, by decide⟩
#guard sampleRoot ⟨0, by decide⟩ != sampleRoot ⟨3, by decide⟩

/-- A listed pair is merged: `root_ofEdges_eq_of_mem` at the sample.
A proof, so no reduction is needed. -/
theorem sampleUnionFind_root_zero_eq_one :
    sampleUnionFind.root ⟨0, by decide⟩ = sampleUnionFind.root ⟨1, by decide⟩ :=
  UnionFind.Sized.root_ofEdges_eq_of_mem (by decide)

/-- The eliminator at the sample: a function constant on each class
agrees on roots. -/
theorem sampleUnionFind_apply_root (h : Fin 5 → Bool)
    (hl : ∀ p ∈ sampleEdges, h p.1 = h p.2) (x : Fin 5) :
    h (sampleUnionFind.root x) = h x :=
  UnionFind.Sized.apply_root_ofEdges hl x
