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
* `PresheafPFunctor.wRestr` — restriction on the `ULift`ed carrier fibre,
  reindexing the underlying tree along a morphism while preserving the index and
  hereditary naturality.
* `PresheafPFunctor.W` — the carrier presheaf `Iᵒᵖ ⥤ Type (max uI uA uB)`, whose
  fibre over `j` is the `ULift` of the hereditarily-natural slice W-trees indexed
  at `j` and whose restriction maps are `wRestr`.

## Main statements

* `PresheafPFunctor.isHereditarilyNatural_mk` — the one-level unfolding of
  `IsHereditarilyNatural` on a constructor `SlicePFunctor.W.mk x`: local
  naturality at the root, together with hereditary naturality of every child.
* `PresheafPFunctor.windex_wRestrTree` — the index of a root-restricted tree is
  the restriction morphism's source.
* `PresheafPFunctor.isHereditarilyNatural_wRestrTree` — hereditary naturality is
  preserved by the root-only restriction, a one-level argument.
* `PresheafPFunctor.wRestrTree_id` / `PresheafPFunctor.wRestrTree_comp` — the
  functoriality of `wRestrTree`, from which `W`'s functor laws transport.

## Implementation notes

This is the presheaf endofunctor case, `I = J`, so the slice endofunctor
`F.toSlicePFunctor : SlicePFunctor I I` has a W-type. `wRestrTree` and
`IsHereditarilyNatural` act on the un-lifted trees `F.toSlicePFunctor.W` of type
`Type (max uA uB)`; the carrier presheaf `W` `ULift`s the indexed subtype into
`Type (max uI uA uB)` so its fibres land in a single universe with the index
category `I`.

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

/-- The index of a root-restricted tree is `j'`: `wRestrTree g z` rebuilds the
root with the restricted shape `(shapeRestr g _).1`, whose `q`-output index is
`j'`. -/
theorem windex_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.windex (F.wRestrTree g z hq) = j' := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a f => exact (F.shapeRestr g ⟨a, hq⟩).2

/-- The child a root-restricted node assigns to a direction is the child the
original node assigns to the direction's `reindex`. The analogue of
`value_objRestrElt` for the raw child assignment; `rfl` after destructuring the
direction, matching `objRestrElt`'s internal `⟨·, rfl⟩` reconstruction. -/
private theorem snd_objRestrElt {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex) (hq : F.q x.1.1 = j) ⦃i : I⦄
    (d : F.toSliceDomPFunctor.Direction (F.objRestrElt g x hq).1.1 i) :
    (F.objRestrElt g x hq).1.2 d.1 = x.1.2 (F.reindex g ⟨x.1.1, hq⟩ d).1 := by
  obtain ⟨dv, rfl⟩ := d
  rfl

/-- Hereditary naturality is preserved by the root-only restriction: the
children of `wRestrTree g z` are the original subtrees reindexed (each already
hereditarily natural), and its root's local naturality follows from `z`'s own
root local naturality and `reindex_naturality`. A one-level argument, not a
recursion. -/
theorem isHereditarilyNatural_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hz : F.IsHereditarilyNatural z) :
    F.IsHereditarilyNatural (F.wRestrTree g z hq) := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    obtain ⟨hz_local, hz_children⟩ :=
      (F.isHereditarilyNatural_mk (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩)).mp hz
    refine (F.isHereditarilyNatural_mk _).mpr ⟨?_, ?_⟩
    · intro i i' h b
      obtain ⟨bv, rfl⟩ := b
      rw [F.snd_objRestrElt]
      exact (congrArg (fun d => (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩).1.2 d.1)
          (congrFun (F.isFunctorial.reindex_naturality g ⟨a, hq⟩ h) ⟨bv, rfl⟩).symm).trans
        (hz_local h (F.reindex g ⟨a, hq⟩ ⟨bv, rfl⟩))
    · intro b
      exact hz_children (F.reindex g ⟨a, hq⟩ ⟨b, rfl⟩).1

/-- Restriction on the ULifted carrier fibre: apply `wRestrTree` to the
underlying tree of `w` along `g`, re-establishing the index (`j'`, read from the
restricted root shape via `shapeRestr`) and hereditary naturality (preserved by
`wRestrTree`, a one-level consequence of `isHereditarilyNatural_mk` and
`reindex_naturality`). -/
@[expose] def wRestr {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j) :
    ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j ∧ F.IsHereditarilyNatural w } →
      ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j' ∧ F.IsHereditarilyNatural w } :=
  fun w => ULift.up
    ⟨F.wRestrTree g w.down.1 w.down.2.1,
      F.windex_wRestrTree g w.down.1 w.down.2.1,
      F.isHereditarilyNatural_wRestrTree g w.down.1 w.down.2.1 w.down.2.2⟩

/-- Restriction along an identity fixes the tree: `objRestrElt_id` collapses the
rebuilt root, and `mk_dest` reassembles the original tree. -/
theorem wRestrTree_id {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j : I⦄
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.wRestrTree (𝟙 j) z hq = z := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    simp only [wRestrTree]
    rw [F.objRestrElt_id, SlicePFunctor.W.mk_dest]

/-- Restriction along a composite factors: `dest_mk` exposes the inner
restriction and `objRestrElt_comp` splits the rebuilt root. -/
theorem wRestrTree_comp {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' j'' : I⦄ (g : j' ⟶ j)
    (h : j'' ⟶ j') (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hq2 : F.q (PFunctor.W.head (F.wRestrTree g z hq).1) = j') :
    F.wRestrTree (h ≫ g) z hq = F.wRestrTree h (F.wRestrTree g z hq) hq2 := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    simp only [wRestrTree, SlicePFunctor.W.dest_mk]
    rw [F.objRestrElt_comp g h (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩) hq
      (F.shapeRestr g ⟨a, hq⟩).2]

/-- The carrier presheaf `W : Iᵒᵖ ⥤ Type` of the presheaf polynomial endofunctor
`F`: its fibre over `j` is the `ULift` of the hereditarily-natural slice W-trees
indexed at `j`, and its restriction maps are `wRestr`. The functor laws transport
from `objRestrElt_id` / `objRestrElt_comp` through `wRestrTree`, `ULift`, and
`Subtype`. -/
@[expose] def W {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : Iᵒᵖ ⥤ Type (max uI uA uB) where
  obj j := ULift.{uI} { w : F.toSlicePFunctor.W //
    F.toSlicePFunctor.windex w = j.unop ∧ F.IsHereditarilyNatural w }
  map g := ↾ (F.wRestr g.unop)
  map_id j := by
    ext w
    exact F.wRestrTree_id w.down.1 w.down.2.1
  map_comp g h := by
    ext w
    exact F.wRestrTree_comp g.unop h.unop w.down.1 w.down.2.1
      (F.windex_wRestrTree g.unop w.down.1 w.down.2.1)

end PresheafPFunctor
