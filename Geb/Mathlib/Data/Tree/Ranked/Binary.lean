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
* `RankedAlphabet.Binary.depth`, `RankedAlphabet.Binary.ok` — the validity
  scan's pending count and its liveness verdict, read off a whole word.

## Main statements

* `RankedAlphabet.Binary.spell_termEquiv` — the equivalence carries the
  spelling to `BinTree.print`.
* `RankedAlphabet.Binary.valid_iff` — and so carries the scan's language to
  `BinTree.Valid`.
* `RankedAlphabet.Binary.buf_scanFinal_eq_nil` — at width one no incomplete
  block survives a step.
* `RankedAlphabet.Binary.depth_le_length` — the pending count never exceeds
  the word length, which is the bound the recognizers' recursion asks for.
* `RankedAlphabet.Binary.valid_iff_ok_and_depth_eq_one` — validity is the two
  conditions on the counter form, the third holding of every word.
* `RankedAlphabet.Binary.ok_cons_false`,
  `RankedAlphabet.Binary.ok_cons_true`,
  `RankedAlphabet.Binary.depth_cons_false_of_ok`,
  `RankedAlphabet.Binary.depth_cons_true_of_ok_of_two_le_depth` — the counter
  form one bit at a time.

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

`depth` and `ok` are `@[expose]`, as the declarations they project are: a
consuming module's `rfl` and `decide` reduce through them only if they unfold
across the module boundary. `ok_cons_false` and `ok_cons_true` are `@[simp]`,
being unconditional rewrite rules on that form; the two depth `cons`-lemmas
are not, since neither `ok w = true` nor `2 ≤ depth w` is a side condition
`simp` discharges here, so as simp rules they would be inert.

`scanStep_of_not_live` holds at any width — a failed scan absorbs whatever
the block layout — and is stated here because here is where it is used.

`decide_length_eq_width` proceeds by `cases b` rather than `decide` alone:
`decide` refuses a goal carrying a free variable, so the case analysis is what
closes `b`, even though `[b].length` is `1` either way.

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

/-- The nullary term is spelled by the single `false` bit. -/
@[simp] theorem spell_leaf : binRanked.spell leaf = [false] := by
  rw [leaf, spell_mk, code_leafSym]
  rfl

/-- A binary term is spelled by a `true` bit and its children's spellings. -/
@[simp] theorem spell_node (l r : binRanked.Term) :
    binRanked.spell (node l r) = true :: (binRanked.spell l ++ binRanked.spell r) := by
  rw [node, spell_mk, code_nodeSym]
  change [true] ++ (binRanked.spell l ++ (binRanked.spell r ++ [])) = _
  rw [List.append_nil]
  rfl

/-- The count of pending subterms the validity scan leaves. -/
@[expose] def depth (w : List Bool) : ℕ := (binRanked.scanFinal w).depth

/-- Whether the validity scan has not failed. -/
@[expose] def ok (w : List Bool) : Bool := (binRanked.scanFinal w).live

/-- At width one every block completes as it is read, so no incomplete block
survives a step. -/
theorem buf_scanFinal_eq_nil (w : List Bool) : (binRanked.scanFinal w).buf = [] := by
  have h : (binRanked.scanFinal w).buf.length < 1 := binRanked.length_buf_scanFinal_lt w
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- The pending count never exceeds the word length. -/
theorem depth_le_length (w : List Bool) : depth w ≤ w.length :=
  binRanked.depth_scanFinal_le_length w

/-- Validity is the counter form's two conditions: at width one the third,
that no incomplete block remains, holds of every word. -/
theorem valid_iff_ok_and_depth_eq_one (w : List Bool) :
    binRanked.Valid w ↔ ok w = true ∧ depth w = 1 := by
  rw [valid_iff_scanFinal]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, buf_scanFinal_eq_nil w, h.2⟩⟩

/-- The block a bit completes has the alphabet's width. -/
theorem decide_length_eq_width (b : Bool) :
    decide (([b] : List Bool).length = binRanked.width) = true := by cases b <;> decide

/-- The nullary symbol's block denotes arity zero. -/
theorem arOf_decodeBits_false : binRanked.arOf (decodeBits [false]) = some 0 := by decide

/-- The binary symbol's block denotes arity two. -/
theorem arOf_decodeBits_true : binRanked.arOf (decodeBits [true]) = some 2 := by decide

/-- A leaf bit read by a live scan carrying no incomplete block: its arity is
zero, which every pending count admits. -/
theorem scanStep_false_of_live_of_buf_nil (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) : binRanked.scanStep false s = ⟨[], s.depth + 1, true⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_false]
  rfl

/-- A node bit read with two subterms pending pops both and pushes one. -/
theorem scanStep_true_of_live_of_buf_nil_of_two_le_depth (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) (h2 : 2 ≤ s.depth) :
    binRanked.scanStep true s = ⟨[], s.depth - 2 + 1, true⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_true]
  simp only []
  rw [decide_eq_true h2]

/-- A node bit read with fewer than two subterms pending fails the scan. -/
theorem scanStep_true_of_live_of_buf_nil_of_depth_lt_two (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) (h2 : s.depth < 2) :
    binRanked.scanStep true s = ⟨[], s.depth, false⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_true]
  simp only []
  rw [decide_eq_false (by omega : ¬ 2 ≤ s.depth)]

/-- A failed scan reads no further. -/
theorem scanStep_of_not_live (b : Bool) (s : Scan) (hl : s.live = false) :
    binRanked.scanStep b s = s := by
  rw [scanStep, hl]

/-- A leaf bit cannot fail. -/
@[simp] theorem ok_cons_false (w : List Bool) : ok (false :: w) = ok w := by
  rw [ok, ok, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live false _ h, h]
  · rw [scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

/-- A node bit fails exactly when fewer than two subterms are pending. -/
@[simp] theorem ok_cons_true (w : List Bool) :
    ok (true :: w) = (ok w && decide (2 ≤ depth w)) := by
  rw [ok, ok, depth, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live true _ h, h, Bool.false_and]
  · rcases Nat.lt_or_ge (binRanked.scanFinal w).depth 2 with h2 | h2
    · rw [scanStep_true_of_live_of_buf_nil_of_depth_lt_two _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_false (by omega : ¬ 2 ≤ (binRanked.scanFinal w).depth), Bool.true_and]
    · rw [scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_true h2, Bool.true_and]

/-- A leaf bit raises the pending count by one, the scan being live before
it. -/
theorem depth_cons_false_of_ok (w : List Bool) (h : ok w = true) :
    depth (false :: w) = depth w + 1 := by
  rw [depth, depth, scanFinal_cons,
    scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

/-- A node bit pops two pending subterms and pushes one, the scan being live
before it and two subterms pending. -/
theorem depth_cons_true_of_ok_of_two_le_depth (w : List Bool) (h : ok w = true)
    (h2 : 2 ≤ depth w) : depth (true :: w) = depth w - 1 := by
  simp only [depth] at h2 ⊢
  rw [scanFinal_cons,
    scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
  dsimp only
  omega

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
