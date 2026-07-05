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
* `PresheafPFunctor.W.forgetNode` / `PresheafPFunctor.W.rememberNode` — the
  mutually inverse translations between a presheaf node over the carrier
  presheaf `F.W` and the underlying slice node over `windex` together with the
  hereditary naturality of its children.
* `PresheafPFunctor.W.mk` / `PresheafPFunctor.W.dest` — the fixed-point
  constructor and destructor: mutually inverse fibrewise maps between the
  `objPresheaf`-value at `F.W` and `F.W`, exhibiting `F.W` as a fixed point of
  the `objPresheaf`-action at `F.W`.

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
* `PresheafPFunctor.W.dest_mk` / `PresheafPFunctor.W.mk_dest` — `mk` and `dest`
  are mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
  `F.W`.

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

namespace W

/-- Casting a carrier fibre element along an index equality leaves its
underlying slice W-tree unchanged. -/
private theorem cast_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {k k' : I} (e : k = k')
    (u : (F.W).obj ⟨k⟩) :
    (cast (congrArg (fun k : I => (F.W).obj ⟨k⟩) e) u).down.1 = u.down.1 := by
  cases e
  rfl

/-- Two carrier fibre elements with equal underlying trees are equal. -/
private theorem obj_ext {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {k : I} {u u' : (F.W).obj ⟨k⟩}
    (h : u.down.1 = u'.down.1) : u = u' := by
  obtain ⟨u⟩ := u
  obtain ⟨u'⟩ := u'
  exact congrArg ULift.up (Subtype.ext h)

/-- The underlying tree of a restricted fibre element is the root-restriction of
the underlying tree. -/
private theorem map_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃i i' : I⦄ (f : i' ⟶ i)
    (u : (F.W).obj ⟨i⟩) :
    ((F.W).map f.op u).down.1 = F.wRestrTree f u.down.1 u.down.2.1 :=
  rfl

/-- The underlying tree of the value a presheaf node over `F.W` assigns to a
direction is the underlying tree of the carried child fibre element. -/
private theorem value_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction n.1.1 i) :
    (F.toPresheafDomPFunctorData.value n b).down.1 = (n.1.2 b.1).2.down.1 :=
  cast_down F
    (((F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) n.1.1 n.1.2).mp
      n.2 b.1).trans b.2)
    (n.1.2 b.1).2

/-- Rebuild a carrier fibre element from its underlying tree, its `windex`, and
its hereditary naturality: a total-space element over `windex w.down.1` equal to
the original total-space element over `i`. -/
private theorem sigma_eta {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {i : I} (w : (F.W).obj ⟨i⟩) :
    (⟨F.toSlicePFunctor.windex w.down.1, ULift.up ⟨w.down.1, rfl, w.down.2.2⟩⟩ :
      Σ i : I, (F.W).obj ⟨i⟩) = ⟨i, w⟩ := by
  obtain ⟨⟨t, hi, hh⟩⟩ := w
  cases hi
  rfl

/-- Forget a presheaf node over the carrier presheaf `F.W` to the underlying
slice node over `windex`: retain the shape, and send each direction to the
underlying slice W-tree of its carried fibre element. -/
@[expose] def forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) :
    F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex :=
  ⟨⟨n.1.1, fun b => (n.1.2 b).2.down.1⟩,
    (F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex _ _).mpr fun b =>
      ((n.1.2 b).2.down.2.1).trans
        ((F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) _ _).mp
          n.2 b)⟩

/-- Remember a slice node over `windex` whose children are hereditarily natural
as a presheaf node over the carrier presheaf `F.W`: retain the shape, and send
each direction to the carried fibre element built from the child tree, its index
`windex`, and its hereditary naturality. -/
@[expose] def rememberNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (y : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex)
    (hchildren : ∀ b, F.IsHereditarilyNatural (y.1.2 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W)) :=
  ⟨⟨y.1.1, fun b => ⟨F.toSlicePFunctor.windex (y.1.2 b),
      ULift.up ⟨y.1.2 b, rfl, hchildren b⟩⟩⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) _ _).mpr fun b =>
      (F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex _ _).mp y.2 b⟩

/-- `rememberNode` depends on the slice node only, not the hereditary-naturality
data (which occupies a `Prop` position). -/
private theorem rememberNode_eq {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    {y y' : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex}
    (hy : ∀ b, F.IsHereditarilyNatural (y.1.2 b))
    (hy' : ∀ b, F.IsHereditarilyNatural (y'.1.2 b)) (e : y = y') :
    rememberNode F y hy = rememberNode F y' hy' := by
  subst e
  rfl

/-- `forgetNode` inverts `rememberNode`. -/
private theorem forgetNode_rememberNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (y : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex)
    (hchildren : ∀ b, F.IsHereditarilyNatural (y.1.2 b)) :
    forgetNode F (rememberNode F y hchildren) = y := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := y
  rfl

/-- `rememberNode` inverts `forgetNode` (with the hereditary-naturality data
transported through the round trip). -/
private theorem rememberNode_forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W)))
    (hchildren : ∀ b, F.IsHereditarilyNatural ((forgetNode F n).1.2 b)) :
    rememberNode F (forgetNode F n) hchildren = n := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := n
  exact Sigma.ext rfl (heq_of_eq (funext fun b => sigma_eta F (v b).2))

/-- The hereditary naturality of the slice tree built from a presheaf node over
`F.W` is exactly the naturality of the node: the recursive conjunct of
`isHereditarilyNatural_mk` is discharged by the carried hereditary naturality of
each child, and its local conjunct matches the node's `IsNatural` datum through
the underlying-tree correspondence. -/
private theorem isHereditarilyNatural_mk_forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk (forgetNode F n)) ↔
      F.toPresheafDomPFunctorData.IsNatural n := by
  rw [F.isHereditarilyNatural_mk]
  constructor
  · rintro ⟨hloc, -⟩ i i' f b
    apply obj_ext F
    simp only [value_down, map_down]
    exact hloc f b
  · intro hnat
    refine ⟨fun i i' g b => ?_, fun b => (n.1.2 b).2.down.2.2⟩
    have h := congrArg (fun u => u.down.1) (hnat g b)
    simp only [value_down, map_down] at h
    exact h

/-- The fixed-point constructor of the presheaf W-type: the `objPresheaf`-value
at the carrier presheaf `F.W` maps into `F.W`, fibrewise over `I`. It builds the
slice W-tree from the node (via `forgetNode` and the slice constructor
`SlicePFunctor.W.mk`), reads its index from the node's `q`-output index, and
supplies hereditary naturality via `isHereditarilyNatural_mk_forgetNode`. -/
@[expose] def mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : (F.W).obj ⟨j⟩ :=
  ULift.up ⟨SlicePFunctor.W.mk (forgetNode F x.1.1), x.2,
    (isHereditarilyNatural_mk_forgetNode F x.1.1).mpr x.1.2⟩

/-- The fixed-point destructor of the presheaf W-type, inverse to `mk`: the
underlying tree decomposes (via the slice destructor `SlicePFunctor.W.dest`) as
a shape with a family of hereditarily-natural subtrees, reassembled (via
`rememberNode`) into a natural node over `F.W`, and re-indexed at the root's
`q`-output index. -/
@[expose] def dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : (F.objPresheaf F.W).obj ⟨j⟩ := by
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) := by
    rw [SlicePFunctor.W.mk_dest]
    exact z.down.2.2
  have hchildren := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest z.down.1)).mp hz).2
  exact ⟨⟨rememberNode F (SlicePFunctor.W.dest z.down.1) hchildren,
      (isHereditarilyNatural_mk_forgetNode F _).mp (by rw [forgetNode_rememberNode F]; exact hz)⟩,
    calc F.q (SlicePFunctor.W.dest z.down.1).1.1
        = F.toSlicePFunctor.windex (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) :=
          (SlicePFunctor.W.windex_mk (SlicePFunctor.W.dest z.down.1)).symm
      _ = F.toSlicePFunctor.windex z.down.1 := by rw [SlicePFunctor.W.mk_dest]
      _ = j := z.down.2.1⟩

/-- `dest` is a left inverse of `mk`. -/
@[simp]
theorem dest_mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : dest (mk x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (F := F.toSlicePFunctor)
      (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
        (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1)))) := by
    rw [SlicePFunctor.W.mk_dest]
    exact (isHereditarilyNatural_mk_forgetNode F x.1.1).mpr x.1.2
  have hch := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
    (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1)))).mp hz).2
  change rememberNode F (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
    (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1))) hch = x.1.1
  have hy' : ∀ b, F.IsHereditarilyNatural ((forgetNode F x.1.1).1.2 b) :=
    fun b => (x.1.1.1.2 b).2.down.2.2
  exact (rememberNode_eq F hch hy'
    (SlicePFunctor.W.dest_mk (F := F.toSlicePFunctor) (forgetNode F x.1.1))).trans
    (rememberNode_forgetNode F x.1.1 hy')

/-- `mk` is a left inverse of `dest`; with `dest_mk`, `mk` and `dest` are
mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
`F.W`. -/
@[simp]
theorem mk_dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : mk (dest z) = z := by
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) := by
    rw [SlicePFunctor.W.mk_dest]
    exact z.down.2.2
  have hch := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest z.down.1)).mp hz).2
  apply obj_ext F
  change SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F
    (rememberNode F (SlicePFunctor.W.dest (F := F.toSlicePFunctor) z.down.1) hch)) = z.down.1
  rw [forgetNode_rememberNode, SlicePFunctor.W.mk_dest]

end W

end PresheafPFunctor
