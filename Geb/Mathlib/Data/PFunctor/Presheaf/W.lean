/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

/-!
# W-types of presheaf polynomial functors: hereditary naturality (constructive core)

For a presheaf polynomial endofunctor `F : PresheafPFunctor I I`, the W-type of
the underlying slice endofunctor `F.toSlicePFunctor : SlicePFunctor I I` carries
a tree-level naturality predicate. A slice W-tree assembles a shape with a
compatible family of child subtrees; the presheaf structure additionally acts on
directions contravariantly (`directionRestr`) and on the assignment of shapes to
output indices. A tree is hereditarily natural when, at every node, restricting a
child subtree along a morphism agrees with selecting the child at the reindexed
direction, hereditarily through the whole tree.

`wRestrTree` is the root-only restriction of a slice W-tree along a morphism: it
restricts the root shape and reindexes the direction-assignment via the
generalized `PresheafPFunctor.objRestrElt`, conjugated by the slice destructor
and constructor. `IsHereditarilyNatural` folds the local naturality equation
over the whole tree through the slice W-type's `Prop`-valued paramorphism
`SlicePFunctor.W.recProp`; `isHereditarilyNatural_mk` is its one-level
computation rule.

## Main definitions

* `PresheafPFunctor.wRestrTree` — the root-only restriction of a slice W-tree
  along a morphism, via the generalized `objRestrElt` at `p := windex`.
* `PresheafPFunctor.IsHereditarilyNatural` — the tree-level naturality predicate
  on slice W-trees, defined by `SlicePFunctor.W.recProp`.

## Main statements

* `PresheafPFunctor.isHereditarilyNatural_mk` — the one-level unfolding of
  `IsHereditarilyNatural` on a constructor `SlicePFunctor.W.mk x`: local
  naturality at the root, together with hereditary naturality of every child.

## Implementation notes

This is the presheaf endofunctor case, `I = J`, so the slice endofunctor
`F.toSlicePFunctor : SlicePFunctor I I` has a W-type. `wRestrTree` and
`IsHereditarilyNatural` act on the un-lifted trees `F.toSlicePFunctor.W` of type
`Type (max uA uB)`; the carrier presheaf's universe management is deferred to a
later module.

The recursion in `IsHereditarilyNatural` is confined to the slice W-type's
`Prop`-valued paramorphism `SlicePFunctor.W.recProp`: no explicit self-recursion
and no `induction` tactic appear. The child-index witness required by
`wRestrTree` is discharged from the compatibility of the node's
direction-assignment (`SliceDomPFunctor.compatible_iff`) together with the
direction's fibre constraint, exactly as `PresheafDomPFunctorData.value` obtains
its index equality.

## References

* [Weber2007]
* [GambinoHyland2004]
* [GambinoKock2013]
* [AltenkirchGhaniHancockMcBrideMorris2015]

## Tags

W-type, initial algebra, polynomial functor, presheaf, parametric right adjoint,
naturality, restriction map, PFunctor
-/

public section

open CategoryTheory

universe uI uA uB vI

namespace PresheafPFunctor

/-- The root-only restriction of a slice W-tree `z` along a morphism `g : j' ⟶ j`
(where `j` is the index of `z`): restrict the root shape and reindex its
direction-assignment via the generalized `objRestrElt` at the projection
`p := F.toSlicePFunctor.windex`, conjugating by the slice destructor and
constructor. The head-index witness required by `objRestrElt` is the hypothesis
`hq`, the root's `q`-output index being read from `PFunctor.W.head`. -/
@[expose] def wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.W :=
  SlicePFunctor.W.mk (F.objRestrElt g (SlicePFunctor.W.dest z)
    (by obtain ⟨w, hw⟩ := z; cases w with | mk a f => exact hq))

/-- Hereditary naturality of a slice W-tree: at every node, restricting a child
subtree along a morphism `g` agrees with selecting the child at the reindexed
direction, hereditarily. The local conjunct is the tree analogue of
`PresheafDomPFunctorData.IsNatural`; the fold over the tree is carried by the
slice W-type's `Prop`-valued paramorphism `SlicePFunctor.W.recProp`. -/
@[expose] def IsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : F.toSlicePFunctor.W → Prop :=
  SlicePFunctor.W.recProp (fun x ih =>
    (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
        x.1.2 (F.directionRestr x.1.1 g b).1
          = F.wRestrTree g (x.1.2 b.1)
              (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex x.1.1 x.1.2).mp
                x.2 b.1).trans b.2)) ∧ ∀ b, ih b)

/-- One-level unfolding of `IsHereditarilyNatural` on a constructor
`SlicePFunctor.W.mk x`: local naturality at the root together with hereditary
naturality of every child subtree. From `SlicePFunctor.W.recProp_mk`. -/
theorem isHereditarilyNatural_mk {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
          x.1.2 (F.directionRestr x.1.1 g b).1
            = F.wRestrTree g (x.1.2 b.1)
                (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex x.1.1 x.1.2).mp
                  x.2 b.1).trans b.2)) ∧
        ∀ b, F.IsHereditarilyNatural (x.1.2 b) := by
  unfold IsHereditarilyNatural
  rw [SlicePFunctor.W.recProp_mk]

end PresheafPFunctor
