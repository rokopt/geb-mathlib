/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Tree.Ranked.Preorder
public import Geb.Mathlib.Data.Tree.Preorder
public import Mathlib.Data.Fin.VecNotation

/-!
# Binary trees as the terms of a two-symbol ranked alphabet

The alphabet of one nullary and one binary symbol, spelled by one bit each.
Its term algebra is equivalent to `BinTree`, and the equivalence carries
`RankedAlphabet.spell` to `BinTree.print` on the nose: the two encodings are
one function up to that equivalence, not merely bijections onto one language.

## Main definitions

* `RankedAlphabet.Binary.binRanked` — the alphabet.
* `RankedAlphabet.Binary.leaf`, `RankedAlphabet.Binary.node` — the two forms
  of its terms.
* `RankedAlphabet.Binary.termEquiv` — the equivalence with `BinTree`.

## Main statements

* `RankedAlphabet.Binary.spell_termEquiv` — the equivalence carries the
  spelling to `BinTree.print`.
* `RankedAlphabet.Binary.valid_iff` — and so carries the scan's language to
  `BinTree.Valid`.

## Implementation notes

`leafSym` and `nodeSym` name the two indices rather than each use site
writing `⟨0, by decide⟩`: a symbol index whose bound proof is still an
unassigned metavariable blocks `arity` from reducing, so the child family's
domain is then neither `Fin 0` nor `Fin 2` and the family does not elaborate.
Against a symbol index that is a pattern variable, a child index's bound is
ascribed rather than proved where it stands: the goal `0 < binRanked.arity
⟨1, h⟩` carries the free variable `h`, which `decide` refuses, and presents
the arity as an atom, which `omega` cannot unfold. `show (0 : ℕ) < 2` replaces
it with the definitionally equal closed goal.

`code_leafSym` and `code_nodeSym` are proved by `decide` rather than by `rfl`.
`Nat.land`, which `Nat.testBit` runs through, is not exposed, so a block does
not reduce during elaboration, while the kernel evaluates it.

## Tags

binary tree, ranked alphabet, term algebra, preorder, equivalence
-/

namespace RankedAlphabet.Binary

public section

/-- The alphabet of one nullary and one binary symbol, one bit to a block. -/
@[expose] def binRanked : RankedAlphabet := ⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩

/-- The nullary symbol. -/
@[expose] def leafSym : Fin binRanked.card := ⟨0, by decide⟩

/-- The binary symbol. -/
@[expose] def nodeSym : Fin binRanked.card := ⟨1, by decide⟩

/-- The term with the nullary head symbol. -/
@[expose] def leaf : binRanked.Term :=
  Term.mk binRanked leafSym fun d ↦ absurd (show d.val < 0 from d.isLt) (by omega)

/-- The term with the binary head symbol and children `l` and `r`. -/
@[expose] def node (l r : binRanked.Term) : binRanked.Term :=
  Term.mk binRanked nodeSym fun d ↦ if d.val = 0 then l else r

/-- The nullary symbol's block is the single `false` bit. -/
theorem code_leafSym : binRanked.code leafSym = [false] := by decide

/-- The binary symbol's block is the single `true` bit. -/
theorem code_nodeSym : binRanked.code nodeSym = [true] := by decide

@[simp] theorem spell_leaf : binRanked.spell leaf = [false] := by
  rw [leaf, spell_mk, code_leafSym]
  rfl

@[simp] theorem spell_node (l r : binRanked.Term) :
    binRanked.spell (node l r) = true :: (binRanked.spell l ++ binRanked.spell r) := by
  rw [node, spell_mk, code_nodeSym]
  change [true] ++ (binRanked.spell l ++ (binRanked.spell r ++ [])) = _
  rw [List.append_nil]
  rfl

/-- A binary tree read as a term. -/
@[expose] def ofBinTree : BinTree → binRanked.Term :=
  WType.elim binRanked.Term fun x ↦
    match x with
    | ⟨.leaf, _⟩ => leaf
    | ⟨.node, ch⟩ => node (ch (0 : Fin 2)) (ch (1 : Fin 2))

/-- A term read as a binary tree. -/
@[expose] def toBinTree : binRanked.Term → BinTree :=
  WType.elim BinTree fun x ↦
    match x with
    | ⟨⟨0, _⟩, _⟩ => BinTree.leaf
    | ⟨⟨1, _⟩, ch⟩ =>
      BinTree.node (ch ⟨0, show (0 : ℕ) < 2 by omega⟩) (ch ⟨1, show (1 : ℕ) < 2 by omega⟩)
    | ⟨⟨n + 2, h⟩, _⟩ => absurd (show n + 2 < 2 from h) (by omega)

/-- Reading a binary tree as a term and back recovers the tree. -/
theorem toBinTree_ofBinTree (t : BinTree) : toBinTree (ofBinTree t) = t :=
  BinTree.induction (motive := fun t ↦ toBinTree (ofBinTree t) = t)
    rfl
    (fun l r ihl ihr ↦ by
      change BinTree.node (toBinTree (ofBinTree l)) (toBinTree (ofBinTree r)) = _
      rw [ihl, ihr]) t

/-- Reading a term as a binary tree and back recovers the term. -/
theorem ofBinTree_toBinTree : ∀ u : binRanked.Term, ofBinTree (toBinTree u) = u :=
  Term.induction (motive := fun u ↦ ofBinTree (toBinTree u) = u)
    (fun i ch ih ↦ by
      match i with
      | ⟨0, hi⟩ =>
        change leaf = _
        exact congrArg _ (funext fun d ↦ absurd (show d.val < 0 from d.isLt) (by omega))
      | ⟨1, hi⟩ =>
        have h0 := ih ⟨0, show (0 : ℕ) < 2 by omega⟩
        have h1 := ih ⟨1, show (1 : ℕ) < 2 by omega⟩
        change node (ofBinTree (toBinTree (ch _))) (ofBinTree (toBinTree (ch _))) = _
        rw [h0, h1, node]
        exact congrArg _ (funext fun d ↦ by
          match d with
          | ⟨0, _⟩ => rfl
          | ⟨1, _⟩ => rfl)
      | ⟨n + 2, hi⟩ => exact absurd (show n + 2 < 2 from hi) (by omega))

/-- Binary trees are the terms of the two-symbol alphabet. -/
@[expose] def termEquiv : BinTree ≃ binRanked.Term where
  toFun := ofBinTree
  invFun := toBinTree
  left_inv := toBinTree_ofBinTree
  right_inv := ofBinTree_toBinTree

/-- The equivalence carries the spelling to `BinTree.print`. -/
theorem spell_termEquiv (t : BinTree) :
    binRanked.spell (termEquiv t) = BinTree.print t :=
  BinTree.induction (motive := fun t ↦ binRanked.spell (ofBinTree t) = BinTree.print t)
    spell_leaf
    (fun l r ihl ihr ↦ by
      change binRanked.spell (node (ofBinTree l) (ofBinTree r)) = _
      rw [spell_node, ihl, ihr, BinTree.print_node]) t

/-- The scan of the two-symbol alphabet accepts exactly the words
`BinTree.Valid` accepts. -/
theorem valid_iff (w : List Bool) : binRanked.Valid w ↔ BinTree.Valid w := by
  rw [valid_iff_exists_spell, BinTree.valid_iff_exists_print]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨termEquiv.symm u, ?_⟩, fun ⟨t, ht⟩ ↦ ⟨termEquiv t, ?_⟩⟩
  · rw [← hu, ← spell_termEquiv, Equiv.apply_symm_apply]
  · rw [spell_termEquiv, ht]

end

end RankedAlphabet.Binary
