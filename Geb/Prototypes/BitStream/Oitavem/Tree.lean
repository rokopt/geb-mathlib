/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Stream -- shake: keep; the docstring names depthWord
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The tree an expression codes in a coded signature

The recognized language of coded bitstreams does not depend on the target
M-type. An expression of Logs with one normal and no safe argument codes an
element of the M-type of any finitary polynomial functor whose shapes are
coded by bitstrings, a {name}`Geb.SizeBounded.Logspace.WTree.CodedSig`: the
state of the corecursion is a path word, the shape at a node is the decoding
of the expression's value at the node's word, and the child at a direction
extends the word by the direction's position in unary, terminated by a
clear bit. The bitstream reading is the case of one direction per node,
where the path of directions zero to a depth is that depth's word,
{name}`Geb.BitStream.Oitavem.depthWord`. Compatibility of the shapes at successive nodes is
supplied by the corecursion rather than checked. What is not automatic is
totality: a value that decodes to no shape reads as the designated default
shape of the signature, as the empty value reads as termination for
bitstreams. A nullary default makes such a node a leaf, and a default with
directions gives it subtrees, read from the extended words in turn.

The path theorem is stated with mathlib's paths in an M-type,
{name}`PFunctor.M.IsPath` and {name}`PFunctor.M.iselect`: the shape at a
path is the shape read at the path's word. The definitions and the
generator law depend on {name}`PFunctor.M.corec` alone; the path theorems
depend on the destructor {name}`PFunctor.M.dest`, whose dependence on
{lit}`Classical.choice` the module inherits, so it is listed in
{lit}`GebMeta.classicalAllowedModules`.

# Main definitions

* {lit}`dirWord`, {lit}`pathWord` — the word of a direction's position,
  and of a path.
* {lit}`shapeAt`, {lit}`stepM`, {lit}`toM` — the shape read at a word, the
  coalgebra on words, and the coded tree.

# Main statements

* {lit}`corec_stepM`, {lit}`toM_eq_mk` — the generator law: the node at a
  word is its shape over the corecursions from the extended words.
* {lit}`isubtree_corec_stepM`, {lit}`iselect_toM` — the subtree at a path
  is the corecursion from the path's word, and its shape is the shape read
  there.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

bitstream, M-type, corecursion, coded signature, finitary polynomial functor
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Expr)
open Geb.SizeBounded.Logspace.WTree (CodedSig)
open PFunctor.M (IsPath isubtree iselect)

public section

/-- The word of a direction's position: the position in unary, terminated by
a clear bit, so that the path of positions zero to a depth is the depth's
word. -/
@[expose] def dirWord (i : ℕ) : List Bool := List.replicate i true ++ [false]

variable {I : Type} (C : CodedSig I)

/-- The word of a path: the words of its directions' positions in order. -/
@[expose] def pathWord (ps : List C.P.toPFunctor.Idx) : List Bool :=
  ps.flatMap fun x ↦ dirWord (C.idx x.1 x.2)

/-- The word of a path with a first direction. -/
theorem pathWord_cons (x : C.P.toPFunctor.Idx) (ps : List C.P.toPFunctor.Idx) :
    pathWord C (x :: ps) = dirWord (C.idx x.1 x.2) ++ pathWord C ps :=
  List.flatMap_cons

variable [Inhabited C.P.A]

/-- The shape read at a word: the decoding of the expression's value there,
or the default shape when the value decodes to none. -/
@[expose] def shapeAt (e : Expr 1 0) (p : List Bool) : C.P.A :=
  (C.decode (e.eval ![p] Fin.elim0)).getD default

/-- The coalgebra on words: the shape read at the word, with the child at a
direction at the word extended by the direction's word. -/
@[expose] def stepM (e : Expr 1 0) (p : List Bool) : C.P.toPFunctor (List Bool) :=
  ⟨shapeAt C e p, fun b ↦ p ++ dirWord (C.idx _ b)⟩

/-- The tree an expression codes: the corecursion from the empty word. -/
@[expose] def toM (e : Expr 1 0) : C.P.toPFunctor.M := PFunctor.M.corec (stepM C e) []

/-- The generator law at a word: the corecursion from a word is the node of
the shape read there over the corecursions from the extended words. -/
theorem corec_stepM (e : Expr 1 0) (p : List Bool) :
    PFunctor.M.corec (stepM C e) p =
      PFunctor.M.mk
        ⟨shapeAt C e p, fun b ↦ PFunctor.M.corec (stepM C e) (p ++ dirWord (C.idx _ b))⟩ :=
  PFunctor.M.corec_def _ _

/-- The generator law: the coded tree is the node of the shape read at the
empty word over the corecursions from the directions' words. -/
theorem toM_eq_mk (e : Expr 1 0) :
    toM C e =
      PFunctor.M.mk ⟨shapeAt C e [], fun b ↦ PFunctor.M.corec (stepM C e) (dirWord (C.idx _ b))⟩ :=
  corec_stepM C e []

/-- The subtree at a path of the corecursion from a word is the corecursion
from the word extended by the path's word. -/
theorem isubtree_corec_stepM [DecidableEq C.P.A] (e : Expr 1 0) :
    ∀ (ps : List C.P.toPFunctor.Idx) (p : List Bool),
      IsPath ps (PFunctor.M.corec (stepM C e) p) →
        isubtree ps (PFunctor.M.corec (stepM C e) p) =
          PFunctor.M.corec (stepM C e) (p ++ pathWord C ps)
  | [], p, _ => by rw [isubtree, pathWord, List.flatMap_nil, List.append_nil]
  | ⟨a, i⟩ :: ps, p, h => by
    rw [corec_stepM] at h
    obtain rfl := PFunctor.M.isPath_cons h
    exact (congrArg (isubtree (⟨_, i⟩ :: ps)) (corec_stepM C e p)).trans
      ((PFunctor.M.isubtree_cons ps _).trans
        ((isubtree_corec_stepM e ps _ (PFunctor.M.isPath_cons' h)).trans
          (congrArg _ ((List.append_assoc _ _ _).trans
            (congrArg (p ++ ·) (pathWord_cons C ⟨_, i⟩ ps).symm)))))

/-- The shape of the coded tree at a path is the shape read at the path's
word. -/
theorem iselect_toM [DecidableEq C.P.A] (e : Expr 1 0) (ps : List C.P.toPFunctor.Idx)
    (h : IsPath ps (toM C e)) : iselect ps (toM C e) = shapeAt C e (pathWord C ps) := by
  change PFunctor.M.head (isubtree ps (PFunctor.M.corec (stepM C e) [])) = _
  rw [isubtree_corec_stepM C e ps [] h, List.nil_append, corec_stepM, PFunctor.M.head_mk]
  rfl

end

end Geb.BitStream.Oitavem
