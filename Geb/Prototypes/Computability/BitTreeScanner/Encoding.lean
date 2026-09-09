/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Foundations.Data.PFunctor.Free
public import Mathlib.Control.Monad.Cont
meta import GebMeta  -- shake: keep; supplies the cite docstring role

set_option doc.verso true

/-!
# Binary trees with bitstrings at the leaves, and their prefix encoding

The free monad of the polynomial functor {lit}`X ↦ X × X` at the type of
bitstrings: a tree is a bitstring, or a pair of trees. This module names the
type as an instance of Cslib's {name}`PFunctor.FreeM` and spells its trees as
bitstrings by a prefix code in a single pass.

A pair is spelled by the bit {lit}`true` followed by its two children's
spellings, and a leaf by the bit {lit}`false` followed by its bitstring's
self-delimiting body: each payload bit prefixed by {lit}`true`, and the
bit {lit}`false` closing the string. The bits at which the spelling branches
are those of the recursive scheme {cite}`Jacobson1989` § 1 states for
unlabelled binary trees, {lit}`false` for an absent subtree and {lit}`true`
followed by the two subtrees' representations for a node, two bits per
node; the payload of a leaf follows its bit in place. That paper's
level-order marked representation, the one its rank and select directories
index, reorders the same bits. A tree of {lit}`p` pairs and {lit}`m` payload
bits is spelled by {lit}`3 * p + 2 * m + 2` bits, {lit}`length_spell`.

## Main definitions

* {lit}`Geb.BitTreeScanner.square` — the polynomial functor {lit}`X ↦ X × X`.
* {lit}`Geb.BitTreeScanner.BitTree` — the free monad of {lit}`square` at {lit}`List Bool`.
* {lit}`Geb.BitTreeScanner.leaf`, {lit}`Geb.BitTreeScanner.pair` — the two forms of its
  trees.
* {lit}`Geb.BitTreeScanner.leafBody` — the self-delimiting body of a leaf's
  bitstring.
* {lit}`Geb.BitTreeScanner.spell` — the encoding.
* {lit}`Geb.BitTreeScanner.sumHandler`, {lit}`Geb.BitTreeScanner.pairs`,
  {lit}`Geb.BitTreeScanner.payload` — a tree's count of pairs and of payload bits.

## Main statements

* {lit}`Geb.BitTreeScanner.spell_pure`, {lit}`Geb.BitTreeScanner.spell_liftBind`,
  {lit}`Geb.BitTreeScanner.spell_leaf`, {lit}`Geb.BitTreeScanner.spell_pair` — the
  encoding's equations at each constructor.
* {lit}`Geb.BitTreeScanner.leafBody_cons` — the leaf body's equation at a payload
  bit.
* {lit}`Geb.BitTreeScanner.pairs_pure`, {lit}`Geb.BitTreeScanner.pairs_liftBind`,
  {lit}`Geb.BitTreeScanner.payload_pure`, {lit}`Geb.BitTreeScanner.payload_liftBind` — the
  counts' equations at each constructor.
* {lit}`Geb.BitTreeScanner.length_leafBody`, {lit}`Geb.BitTreeScanner.length_spell` — the
  lengths of a leaf body and of a spelling.

## Implementation notes

The code generator does not compile {name}`PFunctor.FreeM.rec`, so
{lit}`spell` is the interpretation {name}`PFunctor.FreeM.liftM` of a tree
into the continuation monad {name}`Cont` at {lit}`List Bool`, applied to the
leaf's spelling as the final continuation: the pair handler receives the
continuation, applies it to each direction and concatenates.
{name}`PFunctor.FreeM.liftM` is structurally recursive in Cslib, so the
interpretation compiles, and its two equations reduce by {lit}`rfl`. The two
counts are the same interpretation at {lit}`ℕ`.

{lit}`pair` is spelled through {name}`cond` rather than {lit}`if`, so that a
pair's children reduce at the two literal directions without a decidability
instance.

## References

* {cite}`Jacobson1989`

## Tags

binary tree, free monad, polynomial functor, prefix code, succinct encoding
-/

@[expose] public section

namespace Geb.BitTreeScanner

/-- The polynomial functor {lit}`X ↦ X × X`: one shape with two directions. -/
abbrev square : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Bool⟩

/-- Binary trees with bitstrings at the leaves: the free monad of
{name}`square` at {lit}`List Bool`. -/
abbrev BitTree : Type := square.FreeM (List Bool)

/-- The tree that is a bitstring. -/
abbrev leaf (s : List Bool) : BitTree := .pure s

/-- The tree that is a pair, the direction {lit}`false` leading to {lit}`l` and
{lit}`true` to {lit}`r`. -/
abbrev pair (l r : BitTree) : BitTree := .liftBind () fun d ↦ cond d r l

/-- The self-delimiting body of a leaf's bitstring: each payload bit prefixed by
{lit}`true`, and {lit}`false` closing the string. -/
def leafBody (s : List Bool) : List Bool := s.flatMap (fun b ↦ [true, b]) ++ [false]

/-- The pair handler of the interpretation: a pair is spelled by {lit}`true`
followed by the continuation at each of its two directions. -/
def pairHandler (a : square.A) : Cont (List Bool) (square.B a) :=
  fun k ↦ (true :: ((k false).run ++ (k true).run) : List Bool)

/-- The encoding: the interpretation of a tree into the continuation monad by
{name}`pairHandler`, run at the leaf's spelling, which is {lit}`false`
followed by its {name}`leafBody`. -/
def spell (t : BitTree) : List Bool := (t.liftM pairHandler).run fun s ↦ false :: leafBody s

/-- The leaf body at a payload bit is {lit}`true`, the bit, and the body of the
rest. -/
@[simp] theorem leafBody_cons (b : Bool) (s : List Bool) :
    leafBody (b :: s) = true :: b :: leafBody s := rfl

/-- A bitstring is spelled by {lit}`false` followed by its body. -/
theorem spell_pure (s : List Bool) : spell (.pure s) = false :: leafBody s := rfl

/-- A pair is spelled by {lit}`true` followed by the spellings at its two
directions, in direction order. -/
theorem spell_liftBind (a : square.A) (c : square.B a → BitTree) :
    spell (.liftBind a c) = true :: (spell (c false) ++ spell (c true)) := rfl

/-- {name}`spell_pure` at {name}`leaf`. -/
theorem spell_leaf (s : List Bool) : spell (leaf s) = false :: leafBody s := rfl

/-- {name}`spell_liftBind` at {name}`pair`. -/
theorem spell_pair (l r : BitTree) : spell (pair l r) = true :: (spell l ++ spell r) := rfl

/-- The handler of a count: a pair sums the continuation at its two directions
and adds {lit}`c`. -/
def sumHandler (c : ℕ) (a : square.A) : Cont ℕ (square.B a) :=
  fun k ↦ ((k false).run + (k true).run + c : ℕ)

/-- A tree's count of pairs: one per pair, none per leaf. -/
def pairs (t : BitTree) : ℕ := (t.liftM (sumHandler 1)).run fun _ ↦ 0

/-- A tree's count of payload bits: the bitstring's length per leaf. -/
def payload (t : BitTree) : ℕ := (t.liftM (sumHandler 0)).run fun s ↦ s.length

/-- A leaf has no pair. -/
theorem pairs_pure (s : List Bool) : pairs (.pure s) = 0 := rfl

/-- A pair's pairs are its directions' and itself. -/
theorem pairs_liftBind (a : square.A) (c : square.B a → BitTree) :
    pairs (.liftBind a c) = pairs (c false) + pairs (c true) + 1 := rfl

/-- A leaf's payload is its bitstring's length. -/
theorem payload_pure (s : List Bool) : payload (.pure s) = s.length := rfl

/-- A pair's payload is its directions'. -/
theorem payload_liftBind (a : square.A) (c : square.B a → BitTree) :
    payload (.liftBind a c) = payload (c false) + payload (c true) := rfl

/-- A leaf body is two bits per payload bit and the closing bit. -/
theorem length_leafBody (s : List Bool) : (leafBody s).length = 2 * s.length + 1 :=
  List.rec (motive := fun s ↦ (leafBody s).length = 2 * s.length + 1) rfl
    (fun _ _ ih ↦ by
      rw [leafBody_cons, List.length_cons, List.length_cons, ih, List.length_cons]
      omega) s

/-- A tree of {lit}`p` pairs and {lit}`m` payload bits is spelled by
{lit}`3 * p + 2 * m + 2` bits: one per pair, and two per payload bit and two
more per leaf, of which there are {lit}`p + 1`. -/
theorem length_spell (t : BitTree) : (spell t).length = 3 * pairs t + 2 * payload t + 2 :=
  PFunctor.FreeM.rec
    (motive := fun t ↦ (spell t).length = 3 * pairs t + 2 * payload t + 2)
    (fun s ↦ by
      rw [spell_pure, List.length_cons, length_leafBody, pairs_pure, payload_pure]
      omega)
    (fun a k ih ↦ by
      rw [spell_liftBind, List.length_cons, List.length_append, ih false, ih true,
        pairs_liftBind, payload_liftBind]
      omega) t

end Geb.BitTreeScanner
