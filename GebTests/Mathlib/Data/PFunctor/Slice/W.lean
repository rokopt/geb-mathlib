/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic
import Geb.Mathlib.Data.PFunctor.Slice.W

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for slice W-types
-/

open SlicePFunctor

-- Definitional shape of the carrier and structure map.
example (F : SlicePFunctor.{0, 0} Bool Bool) :
    F.W = { w : F.toPFunctor.W // F.WValid w } := rfl
example (F : SlicePFunctor.{0, 0} Bool Bool) (z : F.W) :
    F.windex z = F.windexRoot z.1 := rfl

-- The fold's index component is the root tag.
example (F : SlicePFunctor.{0, 0} Bool Bool) (w : F.toPFunctor.W) :
    (F.windexValid w).index = F.windexRoot w :=
  F.windexValid_index_eq_windexRoot w

-- Admissibility unfolds one level.
example (F : SlicePFunctor.{0, 0} Bool Bool) (a : F.toPFunctor.A)
    (f : F.toPFunctor.B a → F.toPFunctor.W) :
    F.WValid (WType.mk a f) ↔
      F.ForAll a (F.WValid ∘ f) ∧ F.OverLeg a (F.windexRoot ∘ f) :=
  F.wValid_mk a f

-- `mk` and `dest` are mutually inverse.
example (F : SlicePFunctor.{0, 0} Bool Bool) (x : F.toSliceDomPFunctor.Obj F.windex) :
    W.dest (W.mk x) = x := W.dest_mk x
example (F : SlicePFunctor.{0, 0} Bool Bool) (z : F.W) :
    W.mk (W.dest z) = z := W.mk_dest z

-- `mk` lies over `I`.
example (F : SlicePFunctor.{0, 0} Bool Bool) (x : F.toSliceDomPFunctor.Obj F.windex) :
    F.windex (W.mk x) = F.obj F.windex x := W.windex_mk x

-- `elim` lies over `I` and satisfies its computation rule.
example (F : SlicePFunctor.{0, 0} Bool Bool) (Y : Type) (p : Y → Bool)
    (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    p ∘ W.elim F Y p g hg = F.windex := W.comp_elim F Y p g hg
example (F : SlicePFunctor.{0, 0} Bool Bool) (Y : Type) (p : Y → Bool)
    (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (x : F.toSliceDomPFunctor.Obj F.windex) :
    W.elim F Y p g hg (W.mk x) =
      g (F.toSliceDomPFunctor.map (W.elim F Y p g hg) (W.comp_elim F Y p g hg) x) :=
  W.elim_mk F Y p g hg x

/-- A concrete slice endofunctor with a leaf shape, so finite admissible trees
exist: shape `false` is a leaf (no directions), shape `true` carries one
direction whose child must lie over `false` (the constraint leg). The tag
`t = id` separates shapes. -/
def wSlice : SlicePFunctor Bool Bool where
  A := Bool
  B := fun a => cond a Unit Empty
  s := fun _ => false
  t := id

/-- The leaf: shape `false`, no directions. -/
def wLeaf : wSlice.toPFunctor.W := WType.mk false (fun e => e.elim)
/-- A node over the leaf: shape `true`, single child the leaf. -/
def wNode : wSlice.toPFunctor.W := WType.mk true (fun _ => wLeaf)

-- Root indices read the tag.
example : wSlice.windexRoot wLeaf = false := rfl
example : wSlice.windexRoot wNode = true := rfl

-- The leaf is admissible vacuously; the node is admissible because its child is the
-- leaf, whose index `false` matches the constraint leg `s ⟨true, _⟩ = false`.
/-- The leaf as an element of the slice W-type. -/
def wLeafElt : wSlice.W :=
  ⟨wLeaf, (wSlice.wValid_mk _ _).mpr ⟨fun e => e.elim, funext fun e => e.elim⟩⟩
/-- The node over the leaf as an element of the slice W-type. -/
def wNodeElt : wSlice.W :=
  ⟨wNode, (wSlice.wValid_mk _ _).mpr ⟨fun _ => wLeafElt.property, rfl⟩⟩

-- Their structure-map indices read the root tag.
example : wSlice.windex wLeafElt = false := rfl
example : wSlice.windex wNodeElt = true := rfl

-- `dest` reads the root shape of an admissible tree.
example : (W.dest wLeafElt).1.1 = false := rfl
example : (W.dest wNodeElt).1.1 = true := rfl

-- `elim` computes on concrete trees. Into the algebra reading the root tag
-- (`wSlice.obj id`, over `Y = Bool` with `p = id`), the eliminator recovers the
-- structure map, so it returns the root tag: `false` for the leaf, `true` for
-- the node.
example : W.elim wSlice Bool id (wSlice.obj id) rfl wLeafElt = false := rfl
example : W.elim wSlice Bool id (wSlice.obj id) rfl wNodeElt = true := rfl
