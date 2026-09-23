/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType.Slice
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# M-types of presheaf polynomial functors

For a presheaf polynomial endofunctor {lit}`F : PresheafPFunctor I I`, the
M-type is obtained from the M-type of the underlying slice endofunctor
({name}`Geb.MType.SliceM`), as its W-type ({name}`PresheafPFunctor.W`) is obtained from the
underlying slice W-type: the carrier presheaf's fibre over {lit}`j` is the
hereditarily natural trees indexed at {lit}`j`, and its restriction maps
restrict the root of a tree along a morphism, reindexing its children.

{lit}`PresheafM.mRestrTree` is the root-only restriction, the generalized
{name}`PresheafPFunctor.objRestrElt` conjugated by the slice destructor and
constructor. A tree is hereditarily natural when at every node, restricting a
child along a morphism agrees with selecting the child at the restricted
direction: {lit}`PresheafM.IsHereditarilyNatural` is the hereditary form
({name}`Geb.MType.Hereditary`) of the condition on one node
({lit}`PresheafM.NodeNatural`), which
for W-types is an inductive fold and here is coinductive.

The constructor and destructor translate between a node over the carrier
presheaf and the node of trees it carries; they are mutually inverse and
commute with restriction, so the destructor is a natural transformation
({lit}`PresheafM.destNat`) making the carrier a coalgebra of
{name}`PresheafPFunctor.objPresheaf`. The corecursor from a presheaf coalgebra
{lit}`(Y, α)` is the corecursor of the slice coalgebra {lit}`α` induces on the
total space of {lit}`Y`. Its image is hereditarily natural by coinduction, and
it is natural by a one-level argument ({lit}`PresheafM.sliceCorec_map`): the
corecursion from a restricted element and the restriction of the corecursion
are built from the same node, by the naturality of {lit}`α`. It is a morphism
of coalgebras and the only one, by the uniqueness of the slice corecursor, so
the carrier is the terminal coalgebra. The coalgebras are those of the
endofunctor {name}`PresheafPFunctor.objPresheaf` of presheaves valued in
{lit}`Type (max uI uA uB)`, the universe of the carrier: a structure map
{lit}`Y ⟶ objPresheaf Y` needs {lit}`Y` and {lit}`objPresheaf Y` in one
category, as the eliminator of {name}`PresheafPFunctor.W` needs its algebras
in that universe.

## Main definitions

* {lit}`PresheafM.mRestrTree` — the root-only restriction of a tree along a
  morphism.
* {lit}`PresheafM.NodeNatural`, {lit}`PresheafM.IsHereditarilyNatural` — local
  and hereditary naturality.
* {lit}`PresheafM.Fiber`, {lit}`PresheafM` — the carrier presheaf's fibre, and
  the carrier presheaf.
* {lit}`PresheafM.mk`, {lit}`PresheafM.dest` — the constructor and destructor.
* {lit}`PresheafM.destNat`, {lit}`PresheafM.mkNat` — the two as natural
  transformations.
* {lit}`PresheafM.corec` — the corecursor from a presheaf coalgebra.

## Main statements

* {lit}`PresheafM.index_mRestrTree`,
  {lit}`PresheafM.isHereditarilyNatural_mRestrTree` — the restriction lands in
  the fibre over the morphism's source.
* {lit}`PresheafM.mRestrTree_id`, {lit}`PresheafM.mRestrTree_comp` — its
  functoriality, from which the carrier's functor laws follow.
* {lit}`PresheafM.dest_mk`, {lit}`PresheafM.mk_dest` — the constructor and
  destructor are mutually inverse.
* {lit}`PresheafM.mk_map`, {lit}`PresheafM.dest_map` — both commute with
  restriction.
* {lit}`PresheafM.dest_corec` — the corecursor is a morphism of coalgebras.
* {lit}`PresheafM.corec_unique` — it is the only one.

## References

* {cite}`Weber2007`
* {cite}`GambinoKock2013`
* {cite}`VanDenBergDeMarchi2007`, Section 2.

## Tags

M-type, terminal coalgebra, polynomial functor, presheaf, parametric right
adjoint, naturality, coinduction
-/
set_option doc.verso true

@[expose] public section

open CategoryTheory

universe uI uA uB vI uX

namespace Geb.MType

variable {I : Type uI} [Category.{vI} I] (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)

namespace PresheafM

/-- The output index of a tree's root shape is its index. -/
theorem q_dest (z : SliceM F.toSlicePFunctor) :
    F.q z.dest.1.1 = SliceM.index F.toSlicePFunctor z :=
  rfl

/-- The root-only restriction of a tree {lit}`z` indexed at {lit}`j` along a
morphism {lit}`g : j' ⟶ j`: restrict the root shape and reindex the children
by {name}`PresheafPFunctor.objRestrElt`, conjugated by the slice destructor and
constructor. -/
def mRestrTree ⦃j j' : I⦄ (g : j' ⟶ j) (z : SliceM F.toSlicePFunctor)
    (hq : SliceM.index F.toSlicePFunctor z = j) : SliceM F.toSlicePFunctor :=
  SliceM.mk (F.objRestrElt g z.dest ((q_dest F z).trans hq))

/-- The index of a root-restricted tree is the source of the morphism. -/
theorem index_mRestrTree ⦃j j' : I⦄ (g : j' ⟶ j) (z : SliceM F.toSlicePFunctor)
    (hq : SliceM.index F.toSlicePFunctor z = j) :
    SliceM.index F.toSlicePFunctor (mRestrTree F g z hq) = j' :=
  (SliceM.index_mk _).trans (F.shapeRestr g ⟨z.dest.1.1, hq⟩).2

/-- Restriction along an identity fixes the tree. -/
theorem mRestrTree_id ⦃j : I⦄ (z : SliceM F.toSlicePFunctor)
    (hq : SliceM.index F.toSlicePFunctor z = j) : mRestrTree F (𝟙 j) z hq = z := by
  simp only [mRestrTree]
  rw [F.objRestrElt_id]
  exact SliceM.mk_dest z

/-- Restriction along a composite is the composite of the restrictions. -/
theorem mRestrTree_comp ⦃j j' j'' : I⦄ (g : j' ⟶ j) (h : j'' ⟶ j')
    (z : SliceM F.toSlicePFunctor) (hq : SliceM.index F.toSlicePFunctor z = j)
    (hq2 : SliceM.index F.toSlicePFunctor (mRestrTree F g z hq) = j') :
    mRestrTree F (h ≫ g) z hq = mRestrTree F h (mRestrTree F g z hq) hq2 := by
  simp only [mRestrTree, SliceM.dest_mk]
  rw [F.objRestrElt_comp g h z.dest hq (F.shapeRestr g ⟨z.dest.1.1, hq⟩).2]

/-- {name}`mRestrTree` respects equality of trees; the index witnesses are
proof-irrelevant. -/
theorem mRestrTree_congr ⦃j j' : I⦄ (g : j' ⟶ j) {z z' : SliceM F.toSlicePFunctor} (hz : z = z')
    (hq : SliceM.index F.toSlicePFunctor z = j) (hq' : SliceM.index F.toSlicePFunctor z' = j) :
    mRestrTree F g z hq = mRestrTree F g z' hq' := by
  subst hz
  rfl

/-- Naturality of a node: restricting the child at a direction along a
morphism agrees with the child at the restricted direction. The tree
analogue of {name}`PresheafDomPFunctorData.IsNatural`. -/
def NodeNatural (x : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor)) : Prop :=
  ∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
    x.1.2 (F.directionRestr x.1.1 g b).1 =
      mRestrTree F g (x.1.2 b.1)
        (((F.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2 b.1).trans b.2)

/-- Hereditary naturality: every node reached through children is natural. -/
def IsHereditarilyNatural : SliceM F.toSlicePFunctor → Prop :=
  Hereditary (Q := F.toPFunctor) (fun z ↦ z.dest.1) (NodeNatural F ∘ SliceM.dest)

/-- Hereditary naturality unfolded one level. -/
theorem isHereditarilyNatural_iff (z : SliceM F.toSlicePFunctor) :
    IsHereditarilyNatural F z ↔
      NodeNatural F z.dest ∧ ∀ b, IsHereditarilyNatural F (z.dest.1.2 b) := by
  unfold IsHereditarilyNatural
  exact hereditary_iff _ _ z

/-- Hereditary naturality at a constructor. -/
theorem isHereditarilyNatural_mk (x : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor)) :
    IsHereditarilyNatural F (SliceM.mk x) ↔
      NodeNatural F x ∧ ∀ b, IsHereditarilyNatural F (x.1.2 b) := by
  rw [isHereditarilyNatural_iff, SliceM.dest_mk]

/-- The child a root-restricted node assigns to a direction is the child the
original node assigns to the direction's reindexing. -/
private theorem snd_objRestrElt {X : Type uX} {p : X → I} ⦃j j' : I⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j) ⦃i : I⦄
    (d : F.toSliceDomPFunctor.Direction (F.objRestrElt g x hq).1.1 i) :
    (F.objRestrElt g x hq).1.2 d.1 = x.1.2 (F.reindex g ⟨x.1.1, hq⟩ d).1 := by
  obtain ⟨dv, rfl⟩ := d
  rfl

/-- Restricting a natural node gives a natural node: its children are the
original children at the reindexed directions, and naturality transports
along {name}`PresheafPFunctorData.IsFunctorial.reindex_naturality`. -/
theorem nodeNatural_objRestrElt ⦃j j' : I⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor)) (hq : F.q x.1.1 = j)
    (hx : NodeNatural F x) : NodeNatural F (F.objRestrElt g x hq) := by
  intro i i' h b
  obtain ⟨bv, rfl⟩ := b
  refine (snd_objRestrElt F g x hq _).trans ?_
  have hr := congrFun (F.isFunctorial.reindex_naturality g ⟨x.1.1, hq⟩ h) ⟨bv, rfl⟩
  exact (congrArg (fun d : F.toSliceDomPFunctor.Direction x.1.1 _ ↦ x.1.2 d.1) hr.symm).trans
    (hx h (F.reindex g ⟨x.1.1, hq⟩ ⟨bv, rfl⟩))

/-- Hereditary naturality is preserved by the root-only restriction. -/
theorem isHereditarilyNatural_mRestrTree ⦃j j' : I⦄ (g : j' ⟶ j) (z : SliceM F.toSlicePFunctor)
    (hq : SliceM.index F.toSlicePFunctor z = j) (hz : IsHereditarilyNatural F z) :
    IsHereditarilyNatural F (mRestrTree F g z hq) := by
  obtain ⟨hloc, hch⟩ := (isHereditarilyNatural_iff F z).mp hz
  exact (isHereditarilyNatural_mk F _).mpr ⟨nodeNatural_objRestrElt F g z.dest _ hloc,
    fun b ↦ hch (F.reindex g ⟨_, (q_dest F z).trans hq⟩ ⟨b, rfl⟩).1⟩

/-- The fibre of the carrier presheaf over {lit}`j`: the hereditarily natural
trees indexed at {lit}`j`, lifted to the universe of {lit}`I`. -/
abbrev Fiber (j : I) : Type (max uI uA uB) :=
  ULift.{uI} { z : SliceM F.toSlicePFunctor //
    SliceM.index F.toSlicePFunctor z = j ∧ IsHereditarilyNatural F z }

/-- Restriction on fibres. -/
def mRestr ⦃j j' : I⦄ (g : j' ⟶ j) : Fiber F j → Fiber F j' :=
  fun w ↦ ULift.up ⟨mRestrTree F g w.down.1 w.down.2.1, index_mRestrTree F g w.down.1 w.down.2.1,
    isHereditarilyNatural_mRestrTree F g w.down.1 w.down.2.1 w.down.2.2⟩

end PresheafM

open PresheafM in
/-- The carrier presheaf of the M-type of {lit}`F`: its fibre over {lit}`j` is
{name}`PresheafM.Fiber`, and its restriction maps are {name}`PresheafM.mRestr`. -/
def PresheafM : Iᵒᵖ ⥤ Type (max uI uA uB) where
  obj j := Fiber F j.unop
  map g := ↾ (mRestr F g.unop)
  map_id j := by
    ext w
    exact mRestrTree_id F w.down.1 w.down.2.1
  map_comp g h := by
    ext w
    exact mRestrTree_comp F g.unop h.unop w.down.1 w.down.2.1
      (index_mRestrTree F g.unop w.down.1 w.down.2.1)

namespace PresheafM

variable {F}

/-- Casting a fibre element along an index equality leaves its tree
unchanged. -/
private theorem cast_down {k k' : I} (e : k = k') (u : (PresheafM F).obj ⟨k⟩) :
    (cast (congrArg (fun k : I ↦ (PresheafM F).obj ⟨k⟩) e) u).down.1 = u.down.1 := by
  cases e
  rfl

/-- Fibre elements with equal trees are equal. -/
theorem obj_ext {k : I} {u u' : (PresheafM F).obj ⟨k⟩} (h : u.down.1 = u'.down.1) : u = u' := by
  obtain ⟨u⟩ := u
  obtain ⟨u'⟩ := u'
  exact congrArg ULift.up (Subtype.ext h)

/-- The tree of a restricted fibre element is the root restriction of its
tree. -/
theorem map_down ⦃i i' : I⦄ (f : i' ⟶ i) (u : (PresheafM F).obj ⟨i⟩) :
    ((PresheafM F).map f.op u).down.1 = mRestrTree F f u.down.1 u.down.2.1 :=
  rfl

/-- The tree of the value a node over {name}`PresheafM` gives a direction is
the tree of the child it carries. -/
private theorem value_down
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (PresheafM F))) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction n.1.1 i) :
    (F.toPresheafDomPFunctorData.value n b).down.1 = (n.1.2 b.1).2.down.1 :=
  cast_down (((F.toSliceDomPFunctor.compatible_iff
    (PresheafDomPFunctorData.elemProj (PresheafM F)) n.1.1 n.1.2).mp n.2 b.1).trans b.2)
    (n.1.2 b.1).2

/-- A fibre element is its tree placed over the tree's index. -/
private theorem sigma_eta {i : I} (w : (PresheafM F).obj ⟨i⟩) :
    (⟨SliceM.index F.toSlicePFunctor w.down.1, ULift.up ⟨w.down.1, rfl, w.down.2.2⟩⟩ :
      Σ i : I, (PresheafM F).obj ⟨i⟩) = ⟨i, w⟩ := by
  obtain ⟨⟨t, hi, hh⟩⟩ := w
  cases hi
  rfl

/-- Forget a node over the carrier presheaf to the node of trees it carries. -/
def forgetNode (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (PresheafM F))) :
    F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor) :=
  ⟨⟨n.1.1, fun b ↦ (n.1.2 b).2.down.1⟩,
    (F.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b ↦
      ((n.1.2 b).2.down.2.1).trans ((F.toSliceDomPFunctor.compatible_iff
        (PresheafDomPFunctorData.elemProj (PresheafM F)) _ _).mp n.2 b)⟩

/-- Remember a node of hereditarily natural trees as a node over the carrier
presheaf, each child placed over its own index. -/
def rememberNode (y : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor))
    (hch : ∀ b, IsHereditarilyNatural F (y.1.2 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (PresheafM F)) :=
  ⟨⟨y.1.1, fun b ↦ ⟨SliceM.index F.toSlicePFunctor (y.1.2 b), ULift.up ⟨y.1.2 b, rfl, hch b⟩⟩⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (PresheafM F)) _ _).mpr
      fun b ↦ (F.toSliceDomPFunctor.compatible_iff _ _ _).mp y.2 b⟩

/-- {name}`rememberNode` depends on the node only. -/
private theorem rememberNode_congr
    {y y' : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor)} (e : y = y')
    (hy : ∀ b, IsHereditarilyNatural F (y.1.2 b)) (hy' : ∀ b, IsHereditarilyNatural F (y'.1.2 b)) :
    rememberNode y hy = rememberNode y' hy' := by
  subst e
  rfl

/-- {name}`rememberNode` inverts {name}`forgetNode`. -/
private theorem rememberNode_forgetNode
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (PresheafM F)))
    (hch : ∀ b, IsHereditarilyNatural F ((forgetNode n).1.2 b)) :
    rememberNode (forgetNode n) hch = n := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := n
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ sigma_eta (v b).2))

/-- A node over the carrier presheaf is natural exactly when the node of trees
it carries is. -/
theorem nodeNatural_forgetNode
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (PresheafM F))) :
    NodeNatural F (forgetNode n) ↔ F.toPresheafDomPFunctorData.IsNatural n := by
  constructor
  · intro hloc i i' f b
    apply obj_ext
    simp only [value_down, map_down]
    exact hloc f b
  · intro hnat i i' g b
    have h := congrArg (fun u ↦ u.down.1) (hnat g b)
    simp only [value_down n, map_down g] at h
    exact h.trans (mRestrTree_congr F g (value_down n b) _ _)

/-- The constructor: the value of {name}`PresheafPFunctor.objPresheaf` at the carrier maps into
the carrier, fibrewise. -/
def mk {j : I} (x : (F.objPresheaf (PresheafM F)).obj ⟨j⟩) : (PresheafM F).obj ⟨j⟩ :=
  ULift.up ⟨SliceM.mk (forgetNode x.1.1), (SliceM.index_mk _).trans x.2,
    (isHereditarilyNatural_mk F _).mpr
      ⟨(nodeNatural_forgetNode x.1.1).mpr x.1.2, fun b ↦ (x.1.1.1.2 b).2.down.2.2⟩⟩

/-- The destructor, inverse to {name}`mk`: the root node of the tree, its
children placed over their indices. -/
def dest {j : I} (z : (PresheafM F).obj ⟨j⟩) : (F.objPresheaf (PresheafM F)).obj ⟨j⟩ :=
  ⟨⟨rememberNode z.down.1.dest ((isHereditarilyNatural_iff F z.down.1).mp z.down.2.2).2,
      (nodeNatural_forgetNode _).mp ((isHereditarilyNatural_iff F z.down.1).mp z.down.2.2).1⟩,
    (q_dest F z.down.1).trans z.down.2.1⟩

/-- The destructor inverts the constructor. -/
@[simp] theorem dest_mk {j : I} (x : (F.objPresheaf (PresheafM F)).obj ⟨j⟩) : dest (mk x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact (rememberNode_congr (SliceM.dest_mk _)
    ((isHereditarilyNatural_iff F (mk x).down.1).mp (mk x).down.2.2).2
    fun b ↦ (x.1.1.1.2 b).2.down.2.2).trans (rememberNode_forgetNode x.1.1 _)

/-- The constructor inverts the destructor. -/
@[simp] theorem mk_dest {j : I} (z : (PresheafM F).obj ⟨j⟩) : mk (dest z) = z :=
  obj_ext (SliceM.mk_dest z.down.1)

/-- {name}`PresheafPFunctor.objRestrElt` respects equality of nodes; the index
witnesses are proof-irrelevant. -/
private theorem objRestrElt_congr {X : Type uX} {p : X → I} ⦃j j' : I⦄ (g : j' ⟶ j)
    {x x' : F.toSliceDomPFunctor.Obj p} (e : x = x') (hq : F.q x.1.1 = j) (hq' : F.q x'.1.1 = j) :
    F.objRestrElt g x hq = F.objRestrElt g x' hq' := by
  subst e
  rfl

/-- The root restriction of a tree is the constructor applied to the
restriction of any node equal to the tree's root node. -/
private theorem mRestrTree_eq_mk ⦃j j' : I⦄ (g : j' ⟶ j) (z : SliceM F.toSlicePFunctor)
    (hq : SliceM.index F.toSlicePFunctor z = j)
    (y : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor)) (hy : z.dest = y)
    (hy' : F.q y.1.1 = j) : mRestrTree F g z hq = SliceM.mk (F.objRestrElt g y hy') := by
  subst hy
  rfl

/-- Restricting a constructed tree restricts its root node. -/
theorem mRestrTree_mk ⦃j j' : I⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj (SliceM.index F.toSlicePFunctor))
    (hq : SliceM.index F.toSlicePFunctor (SliceM.mk x) = j) (hx : F.q x.1.1 = j) :
    mRestrTree F g (SliceM.mk x) hq = SliceM.mk (F.objRestrElt g x hx) :=
  mRestrTree_eq_mk (F := F) g (SliceM.mk x) hq x (SliceM.dest_mk (F := F.toSlicePFunctor) x) hx

/-- The constructor commutes with restriction: restricting a node and then
constructing is constructing and then restricting the root. -/
theorem mk_map ⦃i i' : I⦄ (g : i' ⟶ i) (x : (F.objPresheaf (PresheafM F)).obj ⟨i⟩) :
    mk ((F.objPresheaf (PresheafM F)).map g.op x) = (PresheafM F).map g.op (mk x) :=
  obj_ext (mRestrTree_mk (F := F) g (forgetNode x.1.1) (mk x).down.2.1 x.2).symm

/-- The destructor commutes with restriction. -/
theorem dest_map ⦃i i' : I⦄ (g : i' ⟶ i) (z : (PresheafM F).obj ⟨i⟩) :
    dest ((PresheafM F).map g.op z) = (F.objPresheaf (PresheafM F)).map g.op (dest z) :=
  (congrArg (fun w ↦ dest ((PresheafM F).map g.op w)) (mk_dest z).symm).trans
    ((congrArg dest (mk_map g (dest z)).symm).trans (dest_mk _))

variable (F) in
/-- The destructor as a natural transformation: the structure map making the
carrier presheaf a coalgebra of {name}`PresheafPFunctor.objPresheaf`. -/
def destNat : NatTrans (PresheafM F) (F.objPresheaf (PresheafM F)) where
  app j := ↾ fun z ↦ dest (j := j.unop) z
  naturality _ _ g := by
    ext z
    exact dest_map g.unop z

variable (F) in
/-- The constructor as a natural transformation. With {name}`destNat`, it
exhibits the carrier presheaf as a fixed point of
{name}`PresheafPFunctor.objPresheaf`: their components are mutually inverse by
{name}`dest_mk` and {name}`mk_dest`. The inverse laws are stated componentwise
rather than through {name}`NatTrans.vcomp`, whose definition depends on
{name}`Classical.choice`. -/
def mkNat : NatTrans (F.objPresheaf (PresheafM F)) (PresheafM F) where
  app j := ↾ fun x ↦ mk (j := j.unop) x
  naturality _ _ g := by
    ext x
    exact mk_map g.unop x

section Corec

variable (F) (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans Y (F.objPresheaf Y))

/-- The slice coalgebra underlying the presheaf coalgebra {lit}`α`, on the
total space of {lit}`Y`: an element over {lit}`i` goes to the node
{lit}`α` gives it. -/
def sliceStep (e : Σ i : I, Y.obj ⟨i⟩) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Y) :=
  (α.app ⟨e.1⟩ e.2).1.1

/-- The underlying slice coalgebra lies over {lit}`I`. -/
theorem obj_sliceStep :
    F.toSlicePFunctor.obj (PresheafDomPFunctorData.elemProj Y) ∘ sliceStep F Y α =
      PresheafDomPFunctorData.elemProj Y :=
  funext fun e ↦ (α.app ⟨e.1⟩ e.2).2

/-- The corecursion of the underlying slice coalgebra. -/
def sliceCorec : (Σ i : I, Y.obj ⟨i⟩) → SliceM F.toSlicePFunctor :=
  SliceM.corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)

/-- The underlying corecursion from an element over {lit}`i` is indexed at
{lit}`i`. -/
theorem index_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    SliceM.index F.toSlicePFunctor (sliceCorec F Y α e) = e.1 :=
  congrFun (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)) e

/-- The destructor of the underlying corecursion. -/
theorem dest_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    (sliceCorec F Y α e).dest = F.toSliceDomPFunctor.map (sliceCorec F Y α)
      (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α))
      (sliceStep F Y α e) :=
  SliceM.dest_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α) e

/-- The node {lit}`α` gives a restricted element is the restriction of the
node it gives the element: the naturality of {lit}`α`. -/
theorem sliceStep_map ⦃i i' : I⦄ (f : i' ⟶ i) (y : Y.obj ⟨i⟩) :
    sliceStep F Y α ⟨i', Y.map f.op y⟩ =
      F.objRestrElt f (sliceStep F Y α ⟨i, y⟩) (α.app ⟨i⟩ y).2 := by
  have h : α.app ⟨i'⟩ (Y.map f.op y) = (F.objPresheaf Y).map f.op (α.app ⟨i⟩ y) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (α.naturality f.op) y).trans (ConcreteCategory.comp_apply _ _ _))
  exact congrArg (fun w : (F.objPresheaf Y).obj ⟨i'⟩ ↦ w.1.1) h

/-- The underlying corecursion from a restricted element is the root
restriction of the corecursion from the element. A one-level argument: both
are constructed from the same node, by the naturality of {lit}`α` and because
mapping children commutes with reindexing them. -/
theorem sliceCorec_map ⦃i i' : I⦄ (f : i' ⟶ i) (y : Y.obj ⟨i⟩) :
    sliceCorec F Y α ⟨i', Y.map f.op y⟩ =
      mRestrTree F f (sliceCorec F Y α ⟨i, y⟩) (index_sliceCorec F Y α ⟨i, y⟩) := by
  refine (SliceM.mk_dest _).symm.trans (congrArg SliceM.mk ?_)
  refine (dest_sliceCorec F Y α _).trans ?_
  rw [sliceStep_map]
  exact objRestrElt_congr f (dest_sliceCorec F Y α ⟨i, y⟩).symm _ _

/-- The child a node gives a direction, as an element of the total space, is
the value the node gives the direction, over the direction's index. -/
private theorem snd_eq_value (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Y))
    ⦃i : I⦄ (b : F.toSliceDomPFunctor.Direction x.1.1 i) :
    x.1.2 b.1 = ⟨i, F.toPresheafDomPFunctorData.value x b⟩ :=
  Sigma.ext (((F.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2 b.1).trans b.2)
    (cast_heq _ _).symm

/-- Mapping the children of a natural node by the underlying corecursion gives
a natural node of trees. -/
theorem nodeNatural_map_sliceCorec (x : F.toPresheafDomPFunctorData.obj Y) :
    NodeNatural F (F.toSliceDomPFunctor.map (sliceCorec F Y α)
      (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)) x.1) := by
  intro i i' g b
  change sliceCorec F Y α (x.1.1.2 (F.directionRestr x.1.1.1 g b).1) =
    mRestrTree F g (sliceCorec F Y α (x.1.1.2 b.1)) _
  rw [snd_eq_value F Y x.1 (F.directionRestr x.1.1.1 g b), x.2 g b, sliceCorec_map]
  exact mRestrTree_congr F g (congrArg (sliceCorec F Y α) (snd_eq_value F Y x.1 b).symm) _ _

/-- The underlying corecursion is hereditarily natural: its nodes are natural,
by {name}`nodeNatural_map_sliceCorec`, so it is hereditarily natural by
{name}`Geb.MType.hereditary_of_hom`. -/
theorem isHereditarilyNatural_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    IsHereditarilyNatural F (sliceCorec F Y α e) := by
  unfold IsHereditarilyNatural
  refine hereditary_of_hom (Q := F.toPFunctor) _ _ (fun e ↦ (sliceStep F Y α e).1)
    (sliceCorec F Y α) (fun e ↦ congrArg Subtype.val (dest_sliceCorec F Y α e)) (fun e ↦ ?_) e
  change NodeNatural F (sliceCorec F Y α e).dest
  rw [dest_sliceCorec]
  exact nodeNatural_map_sliceCorec F Y α (α.app ⟨e.1⟩ e.2).1

/-- The corecursor from a presheaf coalgebra {lit}`(Y, α)`: a natural
transformation into the carrier presheaf, whose component at {lit}`j` is the
underlying corecursion; naturality is {name}`sliceCorec_map`. -/
def corec : NatTrans Y (PresheafM F) where
  app j := ↾ fun y ↦ ULift.up ⟨sliceCorec F Y α ⟨j.unop, y⟩, index_sliceCorec F Y α _,
    isHereditarilyNatural_sliceCorec F Y α _⟩
  naturality _ _ g := by
    ext y
    apply obj_ext
    exact sliceCorec_map F Y α g.unop y

/-- The computation rule for the corecursor: it is a morphism of presheaf
coalgebras. -/
theorem dest_corec {j : I} (y : Y.obj ⟨j⟩) :
    dest ((corec F Y α).app ⟨j⟩ y) = (F.mapPresheaf (corec F Y α)).app ⟨j⟩ (α.app ⟨j⟩ y) := by
  apply Subtype.ext
  apply Subtype.ext
  refine (rememberNode_congr (dest_sliceCorec F Y α ⟨j, y⟩)
    ((isHereditarilyNatural_iff F _).mp (isHereditarilyNatural_sliceCorec F Y α ⟨j, y⟩)).2
    fun b ↦ isHereditarilyNatural_sliceCorec F Y α _).trans ?_
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦
    sigma_eta ((corec F Y α).app ⟨_⟩ ((sliceStep F Y α ⟨j, y⟩).1.2 b).2)))

/-- The corecursor is the only morphism of presheaf coalgebras into the
carrier presheaf: its underlying slice-level function is a morphism of slice
coalgebras, so it is the underlying corecursion. -/
theorem corec_unique (f : NatTrans Y (PresheafM F))
    (hf : ∀ (j : I) (y : Y.obj ⟨j⟩),
      dest (f.app ⟨j⟩ y) = (F.mapPresheaf f).app ⟨j⟩ (α.app ⟨j⟩ y)) :
    f = corec F Y α := by
  have h : (fun e : Σ i : I, Y.obj ⟨i⟩ ↦ (f.app ⟨e.1⟩ e.2).down.1) = sliceCorec F Y α :=
    SliceM.corec_unique F.toSlicePFunctor _ _ _ _ (funext fun e ↦ (f.app ⟨e.1⟩ e.2).down.2.1)
      fun e ↦ congrArg (fun w : (F.objPresheaf (PresheafM F)).obj ⟨e.1⟩ ↦ forgetNode w.1.1)
        (hf e.1 e.2)
  ext j y
  exact obj_ext (congrFun h ⟨j.unop, y⟩)

end Corec

end PresheafM

end Geb.MType
