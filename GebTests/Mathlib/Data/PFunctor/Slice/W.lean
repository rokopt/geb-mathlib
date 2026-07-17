/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic
import Geb.Mathlib.Data.PFunctor.Slice.W

/-!
# Tests for slice W-types
-/

set_option linter.privateModule false

open SlicePFunctor

-- Definitional shape of the carrier and structure map.
example (F : SlicePFunctor.{0, 0} Bool Bool) :
    F.W = { w : F.toPFunctor.W // F.WValid w } := rfl
example (F : SlicePFunctor.{0, 0} Bool Bool) (z : F.W) :
    F.wIndex z = F.wIndexRoot z.1 := rfl

-- The fold's index component is the root output index.
example (F : SlicePFunctor.{0, 0} Bool Bool) (w : F.toPFunctor.W) :
    (F.wIndexValid w).index = F.wIndexRoot w :=
  F.wIndexValid_index_eq_wIndexRoot w

-- Admissibility unfolds one level.
example (F : SlicePFunctor.{0, 0} Bool Bool) (a : F.toPFunctor.A)
    (f : F.toPFunctor.B a → F.toPFunctor.W) :
    F.WValid (WType.mk a f) ↔
      F.ForAll a (F.WValid ∘ f) ∧ F.OverInput a (F.wIndexRoot ∘ f) :=
  F.wValid_mk a f

-- `mk` and `dest` are mutually inverse.
example (F : SlicePFunctor.{0, 0} Bool Bool) (x : F.toSliceDomPFunctor.Obj F.wIndex) :
    W.dest (W.mk x) = x := W.dest_mk x
example (F : SlicePFunctor.{0, 0} Bool Bool) (z : F.W) :
    W.mk (W.dest z) = z := W.mk_dest z

-- `mk` lies over `I`.
example (F : SlicePFunctor.{0, 0} Bool Bool) (x : F.toSliceDomPFunctor.Obj F.wIndex) :
    F.wIndex (W.mk x) = F.obj F.wIndex x := W.wIndex_mk x

-- `elim` lies over `I` and satisfies its computation rule.
example (F : SlicePFunctor.{0, 0} Bool Bool) (Y : Type) (p : Y → Bool)
    (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    p ∘ W.elim F Y p g hg = F.wIndex := W.comp_elim F Y p g hg
example (F : SlicePFunctor.{0, 0} Bool Bool) (Y : Type) (p : Y → Bool)
    (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (x : F.toSliceDomPFunctor.Obj F.wIndex) :
    W.elim F Y p g hg (W.mk x) =
      g (F.toSliceDomPFunctor.map (W.elim F Y p g hg) (W.comp_elim F Y p g hg) x) :=
  W.elim_mk F Y p g hg x

/-- A concrete slice endofunctor with a leaf shape, so finite admissible trees
exist: shape `false` is a leaf (no directions), shape `true` carries one
direction whose child must lie over `false` (the direction-input map). The
shape-output map `q = id` separates shapes. -/
def wSlice : SlicePFunctor Bool Bool where
  A := Bool
  B := fun a ↦ cond a Unit Empty
  r := fun _ ↦ false
  q := id

/-- The leaf: shape `false`, no directions. -/
def wLeaf : wSlice.toPFunctor.W := WType.mk false (fun e ↦ e.elim)
/-- A node over the leaf: shape `true`, single child the leaf. -/
def wNode : wSlice.toPFunctor.W := WType.mk true (fun _ ↦ wLeaf)

-- Root indices read the output index.
example : wSlice.wIndexRoot wLeaf = false := rfl
example : wSlice.wIndexRoot wNode = true := rfl

-- The leaf is admissible vacuously; the node is admissible because its child is the
-- leaf, whose index `false` matches the direction-input map `r ⟨true, _⟩ = false`.
/-- The leaf as an element of the slice W-type. -/
def wLeafElt : wSlice.W :=
  ⟨wLeaf, (wSlice.wValid_mk _ _).mpr ⟨fun e ↦ e.elim, funext fun e ↦ e.elim⟩⟩
/-- The node over the leaf as an element of the slice W-type. -/
def wNodeElt : wSlice.W :=
  ⟨wNode, (wSlice.wValid_mk _ _).mpr ⟨fun _ ↦ wLeafElt.property, rfl⟩⟩

-- Their structure-map indices read the root output index.
example : wSlice.wIndex wLeafElt = false := rfl
example : wSlice.wIndex wNodeElt = true := rfl

-- `dest` reads the root shape of an admissible tree.
example : (W.dest wLeafElt).1.1 = false := rfl
example : (W.dest wNodeElt).1.1 = true := rfl

-- `RecProp` computes one level by `recProp_mk`.
example (x : wSlice.toSliceDomPFunctor.Obj wSlice.wIndex) :
    W.RecProp (fun _ _ ↦ True) (W.mk x) = True :=
  W.recProp_mk _ x
-- `induction` discharges the always-true motive.
example (z : wSlice.W) : True :=
  W.induction (motive := fun _ ↦ True) (fun _ _ ↦ trivial) z

-- `elim` computes on concrete trees. Into the algebra reading the root output
-- index (`wSlice.obj id`, over `Y = Bool` with `p = id`), the eliminator
-- recovers the structure map, so it returns the root output index: `false`
-- for the leaf, `true` for the node.
example : W.elim wSlice Bool id (wSlice.obj id) rfl wLeafElt = false := rfl
example : W.elim wSlice Bool id (wSlice.obj id) rfl wNodeElt = true := rfl
