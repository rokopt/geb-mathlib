/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA -- shake: keep
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Tests for quotient presheaf polynomial functors: directions in commutative trees

A quotient inductive-inductive type over the walking arrow `false ⟶ true`: binary
trees modulo commutativity over `false`, and the leaf directions of a tree over `true`,
each direction lying over its tree. The directions are `here`, the direction of the leaf,
and `inL p y` and `inR x p`, a direction `p` in the left or the right subtree of a
node. The type of a direction is a single tree constructor applied to arguments of the
direction constructor: `inL p y` lies over `node t y` where `t` is the tree of `p`.

The witnesses are the congruences of every constructor, commutativity `swap x y`
between `node x y` and `node y x`, and its lift to directions, `dswap p y` between
`inL p y` and `inR y p`, which lies over `swap t y`: a witness between directions
restricts, along the arrow, to a witness between their trees. Each equation comes in
both orientations.

The tests compute the tree of a direction and the endpoints of the witnesses, and
identify, in the quotient, the two leaf directions of `node leaf leaf`. They then
eliminate into a model on the walking arrow, a presheaf whose value over the trees is
the number of leaves and over the directions the depth with the number of leaves of the
tree, whose restriction forgets the depth. Both equations hold in it, commutativity by
the commutativity of addition and its lift by the invariance of depth, so the
eliminator gives the two identified directions of `node leaf leaf` one depth.

Every term constructor has its congruence among the witness constructors and takes
terms as arguments, and every constructor has finitely many arguments, so the quotient
is the initial model: the eliminator into the depth model is the only morphism of
models into it.

## Tags

prototype, quotient inductive-inductive type, W-type, presheaf, walking arrow
-/

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Directions

/-- The base: the walking arrow `false ⟶ true` of sorts, trees over `false` and
directions over `true`, times the walking parallel pair. -/
abbrev Obj : Type := Bool × WalkingParallelPair

/-- The morphism from the trees to the directions of the walking arrow. -/
def arrow : (false : Bool) ⟶ true := homOfLE (by decide)

/-- The constructors. -/
inductive Sh
  | leaf
  | node
  | here
  | inL
  | inR
  | cLeaf
  | cNode
  | swap (o : Bool)
  | cHere
  | cInL
  | cInR
  | dswap (o : Bool)

namespace Sh

/-- The sort of a constructor: trees, `false`, or directions, `true`. -/
def sort : Sh → Bool
  | leaf | node | cLeaf | cNode | swap _ => false
  | here | inL | inR | cHere | cInL | cInR | dswap _ => true

/-- Whether a constructor builds terms, `zero`, or witnesses, `one`. -/
def wobj : Sh → WalkingParallelPair
  | leaf | node | here | inL | inR => .zero
  | cLeaf | cNode | swap _ | cHere | cInL | cInR | dswap _ => .one

/-- The arguments of a constructor. For `node`, `swap` and `cNode` the left and the
right subtree; for `inL`, `cInL` and `dswap` the direction `false` and the other tree
`true`; for `inR` and `cInR` the other tree `false` and the direction `true`. -/
def Gen : Sh → Type
  | leaf | here | cLeaf | cHere => PEmpty
  | node | inL | inR | cNode | cInL | cInR | swap _ | dswap _ => Bool

/-- The sort of an argument. -/
def gsort : (s : Sh) → Gen s → Bool
  | leaf, b => nomatch b
  | here, b => nomatch b
  | cLeaf, b => nomatch b
  | cHere, b => nomatch b
  | node, _ => false
  | cNode, _ => false
  | swap _, _ => false
  | inL, b => !b
  | cInL, b => !b
  | dswap _, b => !b
  | inR, b => b
  | cInR, b => b

/-- Whether the arguments of a constructor are terms or witnesses: witnesses for the
congruences of constructors with arguments. -/
def gwobj : Sh → WalkingParallelPair
  | cNode | cInL | cInR => .one
  | _ => .zero

/-- The object over which an argument lies. -/
abbrev gobj (s : Sh) (b : Gen s) : Obj := (gsort s b, gwobj s)

/-- The tree constructor of the tree of a direction constructor, and of the witness
between trees under a witness between directions. -/
def typeOf : Sh → Sh
  | here => leaf
  | inL => node
  | inR => node
  | cHere => cLeaf
  | cInL => cNode
  | cInR => cNode
  | dswap o => swap o
  | s => s

/-- The term constructor of an endpoint of a witness constructor: the source for
`false` and the target for `true`. The source of `dswap false` is `inL p y` and its
target `inR y p`; `dswap true` is the reverse. -/
def endpoint : Bool → Sh → Sh
  | _, cLeaf => leaf
  | _, cNode => node
  | _, swap _ => node
  | _, cHere => here
  | _, cInL => inL
  | _, cInR => inR
  | false, dswap false => inL
  | false, dswap true => inR
  | true, dswap false => inR
  | true, dswap true => inL
  | _, s => s

/-- The restriction of a constructor from sort `i` to sort `i'`. -/
def restrSort : Bool → Bool → Sh → Sh
  | false, true, s => typeOf s
  | _, _, s => s

/-- The restriction of a constructor along a morphism of the walking parallel pair. -/
def restrWPP : {x' x : WalkingParallelPair} → (x' ⟶ x) → Sh → Sh
  | _, _, .id _, s => s
  | _, _, .left, s => endpoint false s
  | _, _, .right, s => endpoint true s

/-- The arguments of a constructor that the arguments of the constructor of its tree
read, with the morphisms between their objects. -/
def genSort : (s : Sh) → (b : Gen (typeOf s)) → Σ b' : Gen s, (gobj (typeOf s) b ⟶ gobj s b')
  | leaf, b => ⟨b, 𝟙 _⟩
  | node, b => ⟨b, 𝟙 _⟩
  | cLeaf, b => ⟨b, 𝟙 _⟩
  | cNode, b => ⟨b, 𝟙 _⟩
  | swap _, b => ⟨b, 𝟙 _⟩
  | here, b => nomatch b
  | cHere, b => nomatch b
  | inL, false => ⟨false, (arrow, 𝟙 _)⟩
  | inL, true => ⟨true, 𝟙 _⟩
  | cInL, false => ⟨false, (arrow, 𝟙 _)⟩
  | cInL, true => ⟨true, 𝟙 _⟩
  | dswap _, false => ⟨false, (arrow, 𝟙 _)⟩
  | dswap _, true => ⟨true, 𝟙 _⟩
  | inR, false => ⟨false, 𝟙 _⟩
  | inR, true => ⟨true, (arrow, 𝟙 _)⟩
  | cInR, false => ⟨false, 𝟙 _⟩
  | cInR, true => ⟨true, (arrow, 𝟙 _)⟩

/-- The arguments of a witness constructor that the arguments of its endpoint read, with
the morphisms between their objects. -/
def genEnd : (e : Bool) → (s : Sh) → (b : Gen (endpoint e s)) →
    Σ b' : Gen s, (gobj (endpoint e s) b ⟶ gobj s b')
  | _, leaf, b => ⟨b, 𝟙 _⟩
  | _, node, b => ⟨b, 𝟙 _⟩
  | _, here, b => ⟨b, 𝟙 _⟩
  | _, inL, b => ⟨b, 𝟙 _⟩
  | _, inR, b => ⟨b, 𝟙 _⟩
  | _, cLeaf, b => nomatch b
  | _, cHere, b => nomatch b
  | e, cNode, b => ⟨b, (𝟙 _, endHom e)⟩
  | e, cInL, b => ⟨b, (𝟙 _, endHom e)⟩
  | e, cInR, b => ⟨b, (𝟙 _, endHom e)⟩
  | e, swap o, b => ⟨cond (e ^^ o) (!b) b, 𝟙 _⟩
  | false, dswap false, b => ⟨b, 𝟙 _⟩
  | true, dswap true, b => ⟨b, 𝟙 _⟩
  | false, dswap true, false => ⟨true, 𝟙 _⟩
  | false, dswap true, true => ⟨false, 𝟙 _⟩
  | true, dswap false, false => ⟨true, 𝟙 _⟩
  | true, dswap false, true => ⟨false, 𝟙 _⟩

/-- The restriction of a constructor to a lower sort keeps its object of the walking
parallel pair. -/
theorem wobj_restrSort (i' i : Bool) (s : Sh) : (restrSort i' i s).wobj = s.wobj := by
  cases i' <;> cases i <;> rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> rfl

/-- The restriction of a constructor to a lower sort lies over that sort. -/
theorem sort_restrSort (i' i : Bool) (s : Sh) (hs : s.sort = i) (h : i' ≤ i) :
    (restrSort i' i s).sort = i' := by
  cases i' <;> cases i
  · exact hs
  · rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> rfl
  · exact absurd h (by decide)
  · exact hs

/-- The restriction of a constructor along the walking parallel pair keeps its sort. -/
theorem sort_restrWPP {x' x : WalkingParallelPair} (h : x' ⟶ x) (s : Sh) :
    (restrWPP h s).sort = s.sort := by
  cases h <;> rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;>
    (try cases o) <;> rfl

/-- The restriction of a constructor along the walking parallel pair lies over the
source of the morphism. -/
theorem wobj_restrWPP {x' x : WalkingParallelPair} (h : x' ⟶ x) (s : Sh) (hs : s.wobj = x) :
    (restrWPP h s).wobj = x' := by
  cases h with
  | id => exact hs
  | left => rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> (try cases o) <;> rfl
  | right => rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> (try cases o) <;> rfl

end Sh

/-- The reindexing of the arguments of a constructor's restriction to a lower sort. -/
def genRestrSort : (i' i : Bool) → (s : Sh) → (b : Sh.Gen (Sh.restrSort i' i s)) →
    Σ b' : Sh.Gen s, (Sh.gobj (Sh.restrSort i' i s) b ⟶ Sh.gobj s b')
  | false, true, s, b => Sh.genSort s b
  | false, false, _, b => ⟨b, 𝟙 _⟩
  | true, true, _, b => ⟨b, 𝟙 _⟩
  | true, false, _, b => ⟨b, 𝟙 _⟩

/-- The reindexing of the arguments of a constructor's restriction along the walking
parallel pair. -/
def genRestrWPP : {x' x : WalkingParallelPair} → (h : x' ⟶ x) → (s : Sh) →
    (b : Sh.Gen (Sh.restrWPP h s)) → Σ b' : Sh.Gen s, (Sh.gobj (Sh.restrWPP h s) b ⟶ Sh.gobj s b')
  | _, _, .id _, _, b => ⟨b, 𝟙 _⟩
  | _, _, .left, s, b => Sh.genEnd false s b
  | _, _, .right, s, b => Sh.genEnd true s b

/-- The constructors and their arguments, with free arities: restriction along a
morphism of the base restricts along the sort and then along the walking parallel
pair, and reindexes the arguments through both. -/
def freeArity : FreeArity.{0, 0, 0, 0} Obj where
  A := Sh
  q s := (s.sort, s.wobj)
  Gen := Sh.Gen
  gobj := Sh.gobj
  restr g s := Sh.restrWPP (Prod.snd g) (Sh.restrSort _ _ s)
  q_restr g s hs := Prod.ext
    ((Sh.sort_restrWPP _ _).trans
      (Sh.sort_restrSort _ _ s (congrArg Prod.fst hs) (leOfHom (Prod.fst g))))
    (Sh.wobj_restrWPP _ _ ((Sh.wobj_restrSort _ _ s).trans (congrArg Prod.snd hs)))
  reindex g s b :=
    ⟨(genRestrSort _ _ s (genRestrWPP (Prod.snd g) _ b).1).1,
      (genRestrWPP (Prod.snd g) _ b).2 ≫ (genRestrSort _ _ s (genRestrWPP (Prod.snd g) _ b).1).2⟩

/-- Restriction along an identity is the identity. -/
theorem restr_id : freeArity.toData.ShapeRestrId := by
  intro j
  obtain ⟨i, x⟩ := j
  funext s
  cases i <;> rfl

/-- Restriction along a composite is the composite of restrictions. -/
theorem restr_comp : freeArity.toData.ShapeRestrComp := by
  intro j j' j'' g h
  obtain ⟨i, x⟩ := j
  obtain ⟨i', x'⟩ := j'
  obtain ⟨i'', x''⟩ := j''
  obtain ⟨g₁, g₂⟩ := g
  obtain ⟨h₁, h₂⟩ := h
  funext s
  obtain ⟨s, hs⟩ := s
  apply Subtype.ext
  cases i <;> cases i' <;> cases i'' <;>
    (try exact absurd (leOfHom g₁ : true ≤ false) (by decide)) <;>
    (try exact absurd (leOfHom h₁ : true ≤ false) (by decide)) <;>
    cases g₂ <;> cases h₂ <;>
    rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> (try cases o) <;> rfl

/-- Reindexing along an identity is the identity. -/
theorem reindex_id : freeArity.toData.ReindexId restr_id := by
  intro j s i d
  obtain ⟨i₀, x⟩ := j
  obtain ⟨⟨b, c, k⟩, hd⟩ := d
  cases i₀ <;>
    exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.comp_id k)))))

set_option maxHeartbeats 1000000 in
-- The exhaustive case split closes each case by `rfl`; together they exceed the default limit.
/-- Reindexing along a composite is the composite of reindexings: after the case split
the arguments agree and the morphisms differ by associativity. -/
theorem reindex_comp : freeArity.toData.ReindexComp restr_comp := by
  intro j j' j'' g h s i d
  obtain ⟨i₀, x⟩ := j
  obtain ⟨i₁, x'⟩ := j'
  obtain ⟨i₂, x''⟩ := j''
  obtain ⟨g₁, g₂⟩ := g
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨s, hs⟩ := s
  obtain ⟨⟨b, ⟨ci, cx⟩, ⟨k₁, k₂⟩⟩, hd⟩ := d
  cases i₀ <;> cases i₁ <;> cases i₂ <;>
    (try exact absurd (leOfHom g₁ : true ≤ false) (by decide)) <;>
    (try exact absurd (leOfHom h₁ : true ≤ false) (by decide)) <;>
    cases g₂ <;> cases h₂ <;>
    rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;> (try cases o) <;>
    cases b <;> cases k₂ <;> rfl

/-- The quotient presheaf polynomial functor of directions in commutative trees. -/
def F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} Obj Obj :=
  freeArity.toPresheaf restr_id restr_comp reindex_id reindex_comp

/-- The element of the W-type built by a constructor from its arguments. -/
def nd (s : Sh) (ts : (b : Sh.Gen s) → F.W.obj ⟨Sh.gobj s b⟩) : F.W.obj ⟨(s.sort, s.wobj)⟩ :=
  PresheafPFunctor.W.mk (FreeArity.freeNode (S := freeArity) F.W s rfl ts)

/-- The trees. -/
abbrev Tree := F.W.obj ⟨termObj false⟩

/-- The directions. -/
abbrev Pos := F.W.obj ⟨termObj true⟩

/-- The witnesses between trees. -/
abbrev TreeWit := F.W.obj ⟨eqObj false⟩

/-- The witnesses between directions. -/
abbrev PosWit := F.W.obj ⟨eqObj true⟩

/-- The leaf. -/
def leaf : Tree := nd .leaf fun b ↦ nomatch b

/-- The node on two trees. -/
def node (x y : Tree) : Tree := nd .node fun b ↦ cond b y x

/-- The direction of the leaf. -/
def here : Pos := nd .here fun b ↦ nomatch b

/-- A direction in the left subtree. -/
def inL (p : Pos) (y : Tree) : Pos := nd .inL fun | false => p | true => y

/-- A direction in the right subtree. -/
def inR (x : Tree) (p : Pos) : Pos := nd .inR fun | false => x | true => p

/-- The witness of commutativity at two trees. -/
def swap (x y : Tree) : TreeWit := nd (.swap false) fun b ↦ cond b y x

/-- The witness between a direction in the left subtree and the corresponding direction
in the right subtree of the commuted tree. -/
def dswap (p : Pos) (y : Tree) : PosWit := nd (.dswap false) fun | false => p | true => y

/-- The tree of a direction. -/
abbrev tree (p : Pos) : Tree := restr F.W arrow p

/-- The tree of the leaf's direction is the leaf. -/
theorem tree_here : tree here = leaf :=
  (PresheafPFunctor.carrier.mk_map (termHom arrow) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W .here rfl (termHom arrow) _)).trans
    (congrArg (nd .leaf) (funext fun b ↦ nomatch b)))

/-- The tree of a direction in the left subtree is the node on the direction's tree and
the other tree. -/
theorem tree_inL (p : Pos) (y : Tree) : tree (inL p y) = node (tree p) y := by
  refine (PresheafPFunctor.carrier.mk_map (termHom arrow) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W .inL rfl (termHom arrow) _)).trans ?_)
  refine congrArg (nd .node) (funext fun b ↦ ?_)
  cases b
  · rfl
  · exact QuotientPRA.restr_id F.W false y

/-- The tree of a direction in the right subtree is the node on the other tree and the
direction's tree. -/
theorem tree_inR (x : Tree) (p : Pos) : tree (inR x p) = node x (tree p) := by
  refine (PresheafPFunctor.carrier.mk_map (termHom arrow) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W .inR rfl (termHom arrow) _)).trans ?_)
  refine congrArg (nd .node) (funext fun b ↦ ?_)
  cases b
  · exact QuotientPRA.restr_id F.W false x
  · rfl

/-- The source of a commutativity witness is the node on the trees in order. -/
theorem src_swap (x y : Tree) : src F.W false (swap x y) = node x y := by
  refine (PresheafPFunctor.carrier.mk_map (srcHom false) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W (.swap false) rfl (srcHom false) _)).trans ?_)
  refine congrArg (nd .node) (funext fun b ↦ ?_)
  cases b
  · exact QuotientPRA.restr_id F.W false x
  · exact QuotientPRA.restr_id F.W false y

/-- The target of a commutativity witness is the node on the trees exchanged. -/
theorem tgt_swap (x y : Tree) : tgt F.W false (swap x y) = node y x := by
  refine (PresheafPFunctor.carrier.mk_map (tgtHom false) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W (.swap false) rfl (tgtHom false) _)).trans ?_)
  refine congrArg (nd .node) (funext fun b ↦ ?_)
  cases b
  · exact QuotientPRA.restr_id F.W false y
  · exact QuotientPRA.restr_id F.W false x

/-- The source of a direction witness is the direction in the left subtree. -/
theorem src_dswap (p : Pos) (y : Tree) : src F.W true (dswap p y) = inL p y := by
  refine (PresheafPFunctor.carrier.mk_map (srcHom true) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W (.dswap false) rfl (srcHom true) _)).trans ?_)
  refine congrArg (nd .inL) (funext fun b ↦ ?_)
  cases b
  · exact QuotientPRA.restr_id F.W true p
  · exact QuotientPRA.restr_id F.W false y

/-- The target of a direction witness is the corresponding direction in the right
subtree of the commuted tree. -/
theorem tgt_dswap (p : Pos) (y : Tree) : tgt F.W true (dswap p y) = inR y p := by
  refine (PresheafPFunctor.carrier.mk_map (tgtHom true) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W (.dswap false) rfl (tgtHom true) _)).trans ?_)
  refine congrArg (nd .inR) (funext fun b ↦ ?_)
  cases b
  · exact QuotientPRA.restr_id F.W false y
  · exact QuotientPRA.restr_id F.W true p

/-- A direction witness lies over a commutativity witness: its restriction along the
arrow is the witness between the trees of its endpoints. -/
theorem restrEq_dswap (p : Pos) (y : Tree) : restrEq F.W arrow (dswap p y) = swap (tree p) y := by
  refine (PresheafPFunctor.carrier.mk_map (eqHom arrow) _).symm.trans
    ((congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity) F.W (.dswap false) rfl (eqHom arrow) _)).trans ?_)
  refine congrArg (nd (.swap false)) (funext fun b ↦ ?_)
  cases b
  · rfl
  · exact QuotientPRA.restr_id F.W false y

/-- The two directions of the leaves of `node leaf leaf` have the same class. -/
theorem inL_here_eq_inR_here :
    quotientMk F (inL here leaf) = quotientMk F (inR leaf here) := by
  rw [← src_dswap, ← tgt_dswap]
  exact quotientMk_src F (dswap here leaf)

/-- The class of the tree of a direction is the tree of the direction's class: the
quotient's restriction along the arrow sends the class of `inL p y` to the class of
`node (tree p) y`. -/
theorem quotient_map_inL (p : Pos) (y : Tree) :
    (quotient F).map arrow.op (quotientMk F (inL p y)) = quotientMk F (node (tree p) y) :=
  congrArg (quotientMk F) (tree_inL p y)

/-! ## A model: the depth of a direction -/

/-- The values of the model: over the trees the number of leaves, over the directions
the depth of a direction together with the number of leaves of its tree. -/
def Val : Bool → Type
  | false => ℕ
  | true => ℕ × ℕ

/-- A value over the trees as a number. -/
abbrev Val.nat (v : Val false) : ℕ := v

/-- A value over the directions as a pair of numbers. -/
abbrev Val.pair (v : Val true) : ℕ × ℕ := v

/-- The restriction of values along the walking arrow: a direction goes to the number
of leaves of its tree. -/
def valMap : (i i' : Bool) → Val i → Val i'
  | true, false => Prod.snd
  | false, false => id
  | true, true => id
  | false, true => fun _ ↦ ((0 : ℕ), (0 : ℕ))

/-- The presheaf of values on the walking arrow. -/
def P : Boolᵒᵖ ⥤ Type where
  obj i := Val i.unop
  map {i i'} _ := ↾ valMap i.unop i'.unop
  map_id i := by
    obtain ⟨i⟩ := i
    cases i <;> rfl
  map_comp {i i' i''} g h := by
    obtain ⟨i⟩ := i
    obtain ⟨i'⟩ := i'
    obtain ⟨i''⟩ := i''
    cases i <;> cases i' <;> cases i'' <;>
      first
        | rfl
        | exact absurd (leOfHom g.unop : true ≤ false) (by decide)
        | exact absurd (leOfHom h.unop : true ≤ false) (by decide)

/-- The value of a constructor of sort `i` from the values of its arguments: the value
of its source endpoint. A node has the leaves of its subtrees; a direction in a subtree
is one deeper than its direction there, and its tree has the leaves of both subtrees. -/
def alg : (i : Bool) → (s : Sh) → ((b : Sh.Gen s) → Val (Sh.gsort s b)) → Val i
  | false, .leaf, _ => (1 : ℕ)
  | false, .node, t => (t false).nat + (t true).nat
  | false, .cLeaf, _ => (1 : ℕ)
  | false, .cNode, t => (t false).nat + (t true).nat
  | false, .swap false, t => (t false).nat + (t true).nat
  | false, .swap true, t => (t true).nat + (t false).nat
  | true, .here, _ => ((0 : ℕ), (1 : ℕ))
  | true, .inL, t => ((t false).pair.1 + 1, (t false).pair.2 + (t true).nat)
  | true, .inR, t => ((t true).pair.1 + 1, (t false).nat + (t true).pair.2)
  | true, .cHere, _ => ((0 : ℕ), (1 : ℕ))
  | true, .cInL, t => ((t false).pair.1 + 1, (t false).pair.2 + (t true).nat)
  | true, .cInR, t => ((t true).pair.1 + 1, (t false).nat + (t true).pair.2)
  | true, .dswap false, t => ((t false).pair.1 + 1, (t false).pair.2 + (t true).nat)
  | true, .dswap true, t => ((t false).pair.1 + 1, (t true).nat + (t false).pair.2)
  | false, _, _ => (0 : ℕ)
  | true, _, _ => ((0 : ℕ), (0 : ℕ))

/-- Restriction commutes with the model's value on constructors, for argument values
that restrict along the walking arrow by `valMap`: the equations hold in the model, and
the tree of a direction has the leaves the direction's value records. -/
theorem alg_restr {c c' : Obj} (g : c' ⟶ c) (s : Sh) (hs : (s.sort, s.wobj) = c)
    (t : (b : Sh.Gen s) → Val (Sh.gsort s b)) :
    alg c'.1 (freeArity.restr g s) (fun b' ↦
        valMap (Sh.gsort s (freeArity.reindex g s b').1) (Sh.gsort (freeArity.restr g s) b')
          (t (freeArity.reindex g s b').1)) =
      valMap c.1 c'.1 (alg c.1 s t) := by
  obtain ⟨i, x⟩ := c
  obtain ⟨i', x'⟩ := c'
  obtain ⟨g₁, g₂⟩ := g
  cases i <;> cases i' <;> (try exact absurd (leOfHom g₁ : true ≤ false) (by decide)) <;>
    cases g₂ <;> rcases s with _ | _ | _ | _ | _ | _ | _ | o | _ | _ | _ | o <;>
    (try cases o) <;>
    first
      | rfl
      | exact Nat.add_comm _ _
      | exact Prod.ext rfl (Nat.add_comm _ _)
      | nomatch hs

/-- The value a node over the model's presheaf gives an argument, at the argument's own
object. -/
def top {c : Objᵒᵖ} (n : (F.objPresheaf (discrete P)).obj c) (b : Sh.Gen n.1.1.1.1) :
    Val (Sh.gsort n.1.1.1.1 b) :=
  F.toPresheafDomPFunctorData.value n.1.1 ⟨⟨b, Sh.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩

/-- The value a node gives an argument at any direction is the argument's value
restricted along the walking arrow: the naturality of the node, the discrete graph's
restriction along the walking parallel pair being the identity. -/
theorem value_eq {c : Objᵒᵖ} (n : (F.objPresheaf (discrete P)).obj c) (b : Sh.Gen n.1.1.1.1)
    {c' : Obj} (k : c' ⟶ Sh.gobj n.1.1.1.1 b) :
    F.toPresheafDomPFunctorData.value n.1.1 ⟨⟨b, c', k⟩, rfl⟩ =
      valMap (Sh.gsort n.1.1.1.1 b) c'.1 (top n b) := by
  have h := n.1.2 k ⟨⟨b, Sh.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩
  change F.toPresheafDomPFunctorData.value n.1.1 ⟨⟨b, c', k ≫ 𝟙 _⟩, rfl⟩ =
    valMap (Sh.gsort n.1.1.1.1 b) c'.1 (top n b) at h
  exact (congrArg (fun m : c' ⟶ Sh.gobj n.1.1.1.1 b ↦
    F.toPresheafDomPFunctorData.value n.1.1 ⟨⟨b, c', m⟩, rfl⟩) (Category.comp_id k)).symm.trans h

/-- The argument values of a restricted node are the original argument values
restricted along the walking arrow. -/
theorem top_map {c c' : Objᵒᵖ} (g : c ⟶ c') (n : (F.objPresheaf (discrete P)).obj c)
    (b : Sh.Gen (freeArity.restr g.unop n.1.1.1.1)) :
    top ((F.objPresheaf (discrete P)).map g n) b =
      valMap (Sh.gsort n.1.1.1.1 (freeArity.reindex g.unop n.1.1.1.1 b).1)
        (Sh.gsort (freeArity.restr g.unop n.1.1.1.1) b)
        (top n (freeArity.reindex g.unop n.1.1.1.1 b).1) :=
  value_eq n _ _

/-- The model's algebra: a node goes to the value of its constructor on its arguments'
values. -/
def model : NatTrans (F.objPresheaf (discrete P)) (discrete P) where
  app c := ↾ fun n ↦ alg c.unop.1 n.1.1.1.1 (top n)
  naturality c c' g := by
    ext n
    change alg c'.unop.1 (freeArity.restr g.unop n.1.1.1.1)
        (top ((F.objPresheaf (discrete P)).map g n)) =
      valMap c.unop.1 c'.unop.1 (alg c.unop.1 n.1.1.1.1 (top n))
    rw [show top ((F.objPresheaf (discrete P)).map g n) = _ from funext (top_map g n)]
    exact alg_restr g.unop n.1.1.1.1 n.2 (top n)

/-- The eliminator of the W-type into the model on the tree a constructor builds is the
model's value on the eliminator's values on the arguments. -/
theorem wElim_nd (s : Sh) (ts : (b : Sh.Gen s) → F.W.obj ⟨Sh.gobj s b⟩) :
    (PresheafPFunctor.W.elim F (discrete P) model).app ⟨(s.sort, s.wobj)⟩ (nd s ts) =
      alg s.sort s fun b ↦ (PresheafPFunctor.W.elim F (discrete P) model).app _ (ts b) := by
  refine (PresheafPFunctor.W.elim_mk F (discrete P) model _).trans ?_
  change alg s.sort s (top ((F.mapPresheaf (PresheafPFunctor.W.elim F (discrete P) model)).app _
    (FreeArity.freeNode (S := freeArity) F.W s rfl ts))) = _
  congr 1
  funext b
  change (PresheafPFunctor.W.elim F (discrete P) model).app _ (F.W.map (𝟙 _).op (ts b)) = _
  rw [op_id, Functor.map_id_apply]

/-- The eliminator of the quotient into the model. -/
def depth : NatTrans (quotient F) P := elim F P model

/-- The number of leaves of the class of a tree. -/
abbrev leaves (x : Tree) : ℕ := Val.nat (depth.app ⟨false⟩ (quotientMk F x))

/-- The depth of the class of a direction, with the number of leaves of its tree. -/
abbrev posDepth (p : Pos) : ℕ × ℕ := Val.pair (depth.app ⟨true⟩ (quotientMk F p))

/-- The leaf has one leaf. -/
theorem leaves_leaf : leaves leaf = 1 := wElim_nd .leaf fun b ↦ nomatch b

/-- A node has the leaves of its subtrees. -/
theorem leaves_node (x y : Tree) : leaves (node x y) = leaves x + leaves y := wElim_nd .node _

/-- The direction of the leaf has depth zero, in a tree of one leaf. -/
theorem posDepth_here : posDepth here = (0, 1) := wElim_nd .here fun b ↦ nomatch b

/-- A direction in the left subtree is one deeper than its direction there. -/
theorem posDepth_inL (p : Pos) (y : Tree) :
    posDepth (inL p y) = ((posDepth p).1 + 1, (posDepth p).2 + leaves y) :=
  wElim_nd .inL _

/-- A direction in the right subtree is one deeper than its direction there. -/
theorem posDepth_inR (x : Tree) (p : Pos) :
    posDepth (inR x p) = ((posDepth p).1 + 1, leaves x + (posDepth p).2) :=
  wElim_nd .inR _

/-- The tree of a direction has the leaves its depth records: the eliminator is a
morphism of presheaves on the walking arrow. -/
theorem leaves_tree (p : Pos) : leaves (tree p) = (posDepth p).2 :=
  naturality_apply depth arrow.op (quotientMk F p)

-- The two leaf directions of `node leaf leaf` have depth one, in a tree of two leaves.
example : posDepth (inL here leaf) = (1, 2) := by
  rw [posDepth_inL, posDepth_here, leaves_leaf]

-- The identification of the two directions in the quotient agrees with the model.
example : posDepth (inR leaf here) = (1, 2) := by
  change Val.pair (depth.app ⟨true⟩ (quotientMk F (inR leaf here))) = (1, 2)
  rw [← inL_here_eq_inR_here]
  exact (posDepth_inL here leaf).trans (by rw [posDepth_here, leaves_leaf])

/-! ## Initiality -/

/-- The arguments of each constructor are finite. -/
instance (s : freeArity.A) : FinEnum (freeArity.Gen s) :=
  match s with
  | .leaf | .here | .cLeaf | .cHere => finEnumPEmpty
  | .node | .inL | .inR | .cNode | .cInL | .cInR | .swap _ | .dswap _ => finEnumBool

/-- The arguments of the tree and direction constructors are trees and directions. -/
theorem termArguments : TermArguments freeArity := by
  intro s b hs
  cases s <;> first | rfl | exact nomatch hs

/-- The congruence constructor of each term constructor: an endpoint of its witness is
the constructor applied to the same endpoints of the witnesses between its arguments. -/
theorem hasCongruences :
    HasCongruences Directions.restr_id Directions.restr_comp Directions.reindex_id
      Directions.reindex_comp termArguments := by
  intro s c hq hc es
  subst hq
  cases s <;> (try exact WalkingParallelPair.noConfusion hc)
  · refine ⟨nd .cLeaf (fun b ↦ nomatch b), fun o ↦ ?_⟩
    cases o <;> exact (PresheafPFunctor.carrier.mk_map _ _).symm.trans
      ((congrArg PresheafPFunctor.W.mk (FreeArity.map_freeNode (S := freeArity) F.W .cLeaf rfl
        _ _)).trans (congrArg (nd .leaf) (funext fun b ↦ nomatch b)))
  · refine ⟨nd .cNode es, fun o ↦ ?_⟩
    cases o <;> exact (PresheafPFunctor.carrier.mk_map _ _).symm.trans
      ((congrArg PresheafPFunctor.W.mk (FreeArity.map_freeNode (S := freeArity) F.W .cNode rfl
        _ es)).trans (congrArg (nd .node) (funext fun b ↦
          congrArg (fun g ↦ F.W.map (Quiver.Hom.op g) (es b)) (Category.comp_id _))))
  · refine ⟨nd .cHere (fun b ↦ nomatch b), fun o ↦ ?_⟩
    cases o <;> exact (PresheafPFunctor.carrier.mk_map _ _).symm.trans
      ((congrArg PresheafPFunctor.W.mk (FreeArity.map_freeNode (S := freeArity) F.W .cHere rfl
        _ _)).trans (congrArg (nd .here) (funext fun b ↦ nomatch b)))
  · refine ⟨nd .cInL es, fun o ↦ ?_⟩
    cases o <;> exact (PresheafPFunctor.carrier.mk_map _ _).symm.trans
      ((congrArg PresheafPFunctor.W.mk (FreeArity.map_freeNode (S := freeArity) F.W .cInL rfl
        _ es)).trans (congrArg (nd .inL) (funext fun b ↦
          congrArg (fun g ↦ F.W.map (Quiver.Hom.op g) (es b)) (Category.comp_id _))))
  · refine ⟨nd .cInR es, fun o ↦ ?_⟩
    cases o <;> exact (PresheafPFunctor.carrier.mk_map _ _).symm.trans
      ((congrArg PresheafPFunctor.W.mk (FreeArity.map_freeNode (S := freeArity) F.W .cInR rfl
        _ es)).trans (congrArg (nd .inR) (funext fun b ↦
          congrArg (fun g ↦ F.W.map (Quiver.Hom.op g) (es b)) (Category.comp_id _))))

-- The quotient with its algebra is the initial model: `depth` is the only morphism of
-- models from it to the depth model.
example : ∃! h : NatTrans (quotient F) P, IsModelHom (quotientModel hasCongruences) model h :=
  existsUnique_isModelHom hasCongruences P model

end GebProto.QuotientPRA.Directions
