/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.RoseTree.Basic
public import Geb.Prototypes.RoseTree.Bits
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
public import Geb.Prototypes.Computability.BitTree.EliasBinary.Bound

set_option doc.verso true in
/-!
# Rose trees as binary trees with bitstrings at the leaves

A rose tree of bitstrings is a binary tree with bitstrings at its leaves:
a node is the left spine of one fork per child, the spine's leftmost leaf
carrying the label and each fork's right child a child's tree. The
correspondence is the classical rotation and is a bijection, so the
repository's Elias-length encoding of binary trees
{name}`Geb.BitTree.Elias.encode` serializes rose trees, its injectivity
serializes them faithfully, and its recognizer
{name}`Geb.BitTree.Elias.validBool`, computed in linear time and logarithmic
space by {name}`Geb.BitTree.EliasBinary.computableInTimeAndSpace_validBool`,
recognizes the serialized rose trees. Under that encoding a node reads as its
arity in unary, a zero, the delta-coded length of its label, the label, and
the children in order.

# Main definitions

* {lit}`RoseTree.toBin`, {lit}`RoseTree.ofBin` — the rotation and its inverse.
* {lit}`RoseTree.wire` — the serialization.

# Main statements

* {lit}`RoseTree.equivBin` — the rotation is a bijection.
* {lit}`RoseTree.wire_injective`, {lit}`RoseTree.validBool_iff_wire` — the
  serialization is injective and its image is what the recognizer accepts.

# Tags

rose tree, binary tree, left spine, serialization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.RoseTree

open Geb.BitTree (Tree leaf fork tree_ind)
open Geb.SizeBounded.Logspace.WTree (spine spine_concat)
open Geb.Oitavem (rank unrank rank_unrank unrank_rank)

/-- The rotation: a node is the left spine of its children's trees over the
leaf carrying its label. -/
def toBin : RoseTree ℕ → Tree := elim fun a bs ↦ spine (leaf (unrank a)) bs

/-- The computation rule of the rotation. -/
theorem toBin_node (a : ℕ) (cs : List (RoseTree ℕ)) :
    toBin (node a cs) = spine (leaf (unrank a)) (cs.map toBin) := elim_node _ a cs

/-- The inverse rotation: a leaf is a childless node, and a fork appends its
right child to the node its left child reads as. -/
def ofBin : Tree → RoseTree ℕ := WType.elim (RoseTree ℕ) fun x ↦
  match x with
  | ⟨some s, _⟩ => node (rank s) []
  | ⟨none, f⟩ => node (f false).label ((f false).children ++ [f true])

@[simp] theorem ofBin_leaf (s : List Bool) : ofBin (leaf s) = node (rank s) [] := rfl

@[simp] theorem ofBin_fork (l r : Tree) :
    ofBin (fork l r) = node (ofBin l).label ((ofBin l).children ++ [ofBin r]) := rfl

/-- Reading a spine appends the trees its forks carry to the node its base
reads as. -/
theorem ofBin_spine (t : Tree) (bs : List Tree) :
    ofBin (spine t bs) = node (ofBin t).label ((ofBin t).children ++ bs.map ofBin) := by
  refine List.rec (motive := fun bs ↦ ∀ t, ofBin (spine t bs) =
    node (ofBin t).label ((ofBin t).children ++ bs.map ofBin)) ?_ ?_ bs t
  · intro t
    simp [spine]
  · intro b bs ih t
    rw [show spine t (b :: bs) = spine (fork t b) bs from rfl, ih, ofBin_fork, label_node,
      children_node, List.map_cons, List.append_assoc, List.singleton_append]

/-- Rotating and reading back is the identity. -/
theorem ofBin_toBin (t : RoseTree ℕ) : ofBin (toBin t) = t := by
  refine ind (P := fun t ↦ ofBin (toBin t) = t) ?_ t
  intro a cs ih
  rw [toBin_node, ofBin_spine, ofBin_leaf, label_node, children_node, rank_unrank,
    List.nil_append, List.map_map]
  congr 1
  exact List.map_congr_left ih |>.trans (List.map_id cs)

/-- Reading and rotating back is the identity. -/
theorem toBin_ofBin (b : Tree) : toBin (ofBin b) = b := by
  refine tree_ind (P := fun b ↦ toBin (ofBin b) = b) ?_ ?_ b
  · intro s
    rw [ofBin_leaf, toBin_node, List.map_nil, unrank_rank]
    rfl
  · intro l r ihl ihr
    have key : ∀ u : RoseTree ℕ, spine (leaf (unrank u.label)) (u.children.map toBin) = toBin u :=
      fun u ↦ by rw [← toBin_node, node_label_children]
    rw [ofBin_fork, toBin_node, List.map_append, List.map_singleton, spine_concat, key, ihl, ihr]

/-- The rotation is a bijection. -/
def equivBin : RoseTree ℕ ≃ Tree := ⟨toBin, ofBin, ofBin_toBin, toBin_ofBin⟩

/-- The serialization: the Elias-length encoding of the rotation. -/
def wire (t : RoseTree ℕ) : List Bool := Geb.BitTree.Elias.encode (toBin t)

/-- The serialization is injective. -/
theorem wire_injective : Function.Injective wire :=
  Geb.BitTree.Elias.encode_injective.comp equivBin.injective

/-- The recognizer accepts exactly the serialized rose trees. -/
theorem validBool_iff_wire (w : List Bool) :
    Geb.BitTree.Elias.validBool w = true ↔ ∃ t, wire t = w := by
  rw [Geb.BitTree.Elias.validBool_iff_existsUnique]
  constructor
  · rintro ⟨b, hb, -⟩
    exact ⟨ofBin b, by rw [wire, toBin_ofBin, hb]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨toBin t, rfl, fun b hb ↦ Geb.BitTree.Elias.encode_injective hb⟩

end Geb.RoseTree

end
