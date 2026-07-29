/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.UnionFind.OfEdges

/-!
# Tests for the size-indexed union-find

A fold over a small edge list. What is checked is the partition the
fold induces — roots equal within each class, unequal across — not the
root map itself: which representative a class gets is union by rank's
business, an internal of Batteries' algorithm.

Nothing built from `UnionFind.union` or `rootD` reduces in the kernel,
`root`, `findAux` and `find` being well-founded recursions whose
measure is the `noncomputable` `rankMax`, and the fold's compiled form
is not reachable from a sibling library of the same package by
interpretation either. Every assertion below is therefore a proof.
Separation of the two classes is carried by `sampleBelowThree`, a
function constant on each class, which the eliminator transports along
roots.

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

/-- The indicator of the first sample class: constant on `0`, `1`, `2`
and constant on `3`, `4`. -/
def sampleBelowThree (i : Fin 5) : Bool := i.val < 3

/-- `sampleBelowThree` agrees on every listed pair, so the eliminator
applies to it. -/
theorem sampleBelowThree_sampleEdges :
    ∀ p ∈ sampleEdges, sampleBelowThree p.1 = sampleBelowThree p.2 := by decide

/-- A listed pair is merged: `root_ofEdges_eq_of_mem` at the sample. -/
theorem sampleUnionFind_root_zero_eq_one :
    sampleUnionFind.root ⟨0, by decide⟩ = sampleUnionFind.root ⟨1, by decide⟩ :=
  UnionFind.Sized.root_ofEdges_eq_of_mem (by simp [sampleEdges])

/-- Chained edges merge: the first class contains `2` as well. -/
theorem sampleUnionFind_root_zero_eq_two :
    sampleUnionFind.root ⟨0, by decide⟩ = sampleUnionFind.root ⟨2, by decide⟩ :=
  sampleUnionFind_root_zero_eq_one.trans
    (UnionFind.Sized.root_ofEdges_eq_of_mem (by simp [sampleEdges]))

/-- The second class is merged independently of the first. -/
theorem sampleUnionFind_root_three_eq_four :
    sampleUnionFind.root ⟨3, by decide⟩ = sampleUnionFind.root ⟨4, by decide⟩ :=
  UnionFind.Sized.root_ofEdges_eq_of_mem (by simp [sampleEdges])

/-- The two classes stay apart: `sampleBelowThree` separates their
roots. -/
theorem sampleUnionFind_root_zero_ne_three :
    sampleUnionFind.root ⟨0, by decide⟩ ≠ sampleUnionFind.root ⟨3, by decide⟩ := by
  intro he
  have h0 : sampleBelowThree (sampleUnionFind.root ⟨0, by decide⟩) =
      sampleBelowThree ⟨0, by decide⟩ :=
    UnionFind.Sized.apply_root_ofEdges sampleBelowThree_sampleEdges _
  have h3 : sampleBelowThree (sampleUnionFind.root ⟨3, by decide⟩) =
      sampleBelowThree ⟨3, by decide⟩ :=
    UnionFind.Sized.apply_root_ofEdges sampleBelowThree_sampleEdges _
  exact absurd ((h0.symm.trans (congrArg sampleBelowThree he)).trans h3) (by decide)

/-- The eliminator at the sample: a function constant on each class
agrees on roots. -/
theorem sampleUnionFind_apply_root (h : Fin 5 → Bool)
    (hl : ∀ p ∈ sampleEdges, h p.1 = h p.2) (x : Fin 5) :
    h (sampleUnionFind.root x) = h x :=
  UnionFind.Sized.apply_root_ofEdges hl x
