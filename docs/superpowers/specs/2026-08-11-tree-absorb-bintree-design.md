# Absorbing `BinTree` into the two-symbol ranked term algebra

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [What is deleted](#what-is-deleted)
- [What `Ranked/Binary.lean` gains](#what-rankedbinarylean-gains)
- [The one place the shape changes](#the-one-place-the-shape-changes)
- [The consumers](#the-consumers)
- [Verification](#verification)
- [Documentation](#documentation)
- [Risks](#risks)
- [Out of scope](#out-of-scope)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

One branch over `Geb/Mathlib/Data/Tree/` and
`Geb/Mathlib/Computability/`, the item
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers records
as B4, on the line whose last segment is `feat/cobham-fold`. It depends
on B1 and B2, both in place.

After it, one encoding of binary trees is defined in the repository:
`RankedAlphabet.Binary.binRanked.Term` is the two-symbol tree,
`binRanked.spell` its preorder encoding, `binRanked.parse` its
fuel-bounded descent, and `binRanked.Valid` its language. The
`BinTree` type, its own encoding, and the equivalence bridging the two
developments are all deleted.

Every definition below is a projection or a specialization of a
declaration already in `Geb/Mathlib/Data/Tree/Ranked/`. No definition or
theorem is taken from published mathematics, so the branch adds no key to
[docs/references.bib](../../references.bib). The mathematical content is
unchanged: the theorem set of the two recognizers is preserved, restated
over the ranked development's names.

## What is deleted

- `Geb/Mathlib/Data/Tree/Binary.lean` — `BinTree.Shape`,
  `BinTree.Direction`, `BinTree`, `leaf`, `node`, `size`, `induction`,
  `size_leaf`, `size_node`. `RankedAlphabet.Term`, `Term.size`,
  `size_mk` and `Term.induction` cover every remaining use; grep confirms
  no consumer of a leaf-and-node induction principle or of `size` at
  `binRanked` survives the deletions below.
- `Geb/Mathlib/Data/Tree/Preorder.lean` — the whole module. `print`,
  `parseStep`, `parseAux`, `parse`, `depth`, `ok`, `Valid`, and every
  theorem about them.
- From `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` — `ofBinTree`,
  `toBinTree`, `toBinTree_ofBinTree`, `ofBinTree_toBinTree`, `termEquiv`,
  `spell_termEquiv`, `valid_iff`. Each has `BinTree` or `print` in its
  statement, so each loses its subject.
- `GebTests/Mathlib/Data/Tree/Preorder.lean` — the mirror of the deleted
  module. Its worked words are restated under § Verification.
- Two imports each from `Geb/Mathlib/Data/Tree.lean` and
  `GebTests/Mathlib/Data/Tree.lean`.

`binRanked`, `leafSym`, `nodeSym`, `leaf`, `node`, `code_leafSym`,
`code_nodeSym`, `spell_leaf` and `spell_node` stay: the alphabet is what
`Cobham/RankedTree.lean` instantiates at, and the constructors are what
the mirror's worked tree is built from.

## What `Ranked/Binary.lean` gains

The counter form of the validity scan at width one, as two projections and
their rewrite rules. Each is a corollary of a general theorem already in
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`; none is a second recursion
over a word.

The declarations below were compiled against
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean` before this document was
written, so their signatures are transcribed rather than proposed, per
[the session handoff](../plans/2026-08-10-tree-recognizer-session-handoff.md)
§ Context the next session will want.

| Declaration | Statement | Provenance |
| --- | --- | --- |
| `depth (w : List Bool) : ℕ` | `(binRanked.scanFinal w).depth` | projection |
| `ok (w : List Bool) : Bool` | `(binRanked.scanFinal w).live` | projection |
| `buf_scanFinal` | `(binRanked.scanFinal w).buf = []` | `length_buf_scanFinal_lt` at `width = 1`, through `Nat.lt_one_iff` |
| `depth_le_length` | `depth w ≤ w.length` | `depth_scanFinal_le_length` |
| `valid_iff_ok_and_depth` | `binRanked.Valid w ↔ ok w = true ∧ depth w = 1` | `valid_iff_scanFinal` with `buf_scanFinal` |
| `decide_length_eq_width` | `decide (([b] : List Bool).length = binRanked.width) = true` | `decide` |
| `arOf_decodeBits_false` | `binRanked.arOf (decodeBits [false]) = some 0` | `decide` |
| `arOf_decodeBits_true` | `binRanked.arOf (decodeBits [true]) = some 2` | `decide` |
| `scanStep_false` | from `s.live = true` and `s.buf = []`, `binRanked.scanStep false s = ⟨[], s.depth + 1, true⟩` | `scanStep` unfolded |
| `scanStep_true_of_le` | additionally from `2 ≤ s.depth`, `binRanked.scanStep true s = ⟨[], s.depth - 2 + 1, true⟩` | `scanStep` unfolded |
| `scanStep_true_of_lt` | additionally from `s.depth < 2`, `binRanked.scanStep true s = ⟨[], s.depth, false⟩` | `scanStep` unfolded |
| `scanStep_of_not_live` | from `s.live = false`, `binRanked.scanStep b s = s` | `scanStep` unfolded |
| `ok_cons_false` | `ok (false :: w) = ok w` | the four step lemmas |
| `ok_cons_true` | `ok (true :: w) = (ok w && decide (2 ≤ depth w))` | the four step lemmas |
| `depth_cons_false_of_ok` | from `ok w = true`, `depth (false :: w) = depth w + 1` | the four step lemmas |
| `depth_cons_true_of_ok` | from `ok w = true` and `2 ≤ depth w`, `depth (true :: w) = depth w - 1` | the four step lemmas |

Three facts the compilation settled, none of which prose would have
established:

- `decide (([b] : List Bool).length = binRanked.width)` does not
  iota-reduce inside `scanStep`'s `match`, so the scrutinee is rewritten
  to `true` explicitly. The three `scanStep` lemmas exist to do that
  reduction once rather than four times.
- A projection of a `Scan` constructor does not reduce syntactically, as
  [the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
  § Facts established by building item 12 states; `ok_cons_true` and
  `depth_cons_true_of_ok` each need a `dsimp only` after the step
  rewrite.
- `depth` unfolds under `simp only [depth]` at a hypothesis and the goal
  together, which `depth_cons_true_of_ok` needs so that `omega` sees
  `2 ≤ depth w` and `depth w - 2 + 1` in one language.

## The one place the shape changes

The deleted `depth` was a standalone counter with truncating subtraction,
so `depth (false :: v) = depth v + 1` held of every word. The scan
records failure in `live` and leaves `depth` alone thereafter, so the two
depth `cons`-lemmas carry an `ok w = true` hypothesis. The two `ok`
`cons`-lemmas are unconditional, and are the old ones verbatim.

This is not a weakening. Both recognizer proofs open with
`cases hok : ok v`, so the hypothesis is in hand at every site that
rewrites by a depth `cons`-lemma. In the node-bit branch the existing
`depth v = 0 ∨ depth v = 1 ∨ ∃ m, depth v = m + 2` split absorbs the
extra `2 ≤ depth v` side condition: the first two cases are exactly
where `ok (true :: v)` is false, and there the depth is not read.

The two counter forms agree where it matters, and this was measured
rather than argued: over every word of length at most eight, `ok` agrees
with the deleted `BinTree.ok` everywhere, and `depth` agrees with the
deleted `BinTree.depth` at every word where `ok` holds. They disagree
where `ok` fails, which is the freezing above and is why the agreement is
stated under that hypothesis.

## The consumers

`Geb/Mathlib/Computability/Cobham/Tree.lean` and
`Geb/Mathlib/Computability/BellantoniCook/Tree.lean` each carry the same
four statements over the counter form, and each changes the same way.

- `combSem_eq` — `BinTree.ok` and `BinTree.depth` become `Binary.ok` and
  `Binary.depth`. The `false`-bit branch rewrites by
  `depth_cons_false_of_ok` under the `ok v = true` case hypothesis; the
  `true`-bit branch's three-way depth split supplies `2 ≤ depth v` in the
  one case that reads the depth.
- `length_combSem_le` — `BinTree.depth_le_length` becomes
  `Binary.depth_le_length`.
- `isTreeSem_eq_singleton_iff_valid` and `isTreeSem_eq_ite` — stated over
  `binRanked.Valid`, with `valid_iff_ok_and_depth` in place of the
  deleted `Valid`'s definitional unfolding to a conjunction.
- `isTreeSem_eq_singleton_iff_exists_print` — restated as acceptance of
  exactly `{w | ∃ u : binRanked.Term, binRanked.spell u = w}`, composed
  through `valid_iff_exists_spell` rather than the deleted
  `BinTree.valid_iff_exists_print`. The name loses `print`: it becomes
  `isTreeSem_eq_singleton_iff_exists_spell`.

`Geb/Mathlib/Computability/Cobham/RankedTree.lean`'s
`isRankedSem_binRanked_eq_singleton_iff_isTreeSem` loses its `valid_iff`
hop, since both sides now speak of `binRanked.Valid`, and becomes a
direct composition.

`Geb/Mathlib/Computability/Cobham/Tree.lean`'s module docstring names
`BinTree` at nine places and `BellantoniCook/Tree.lean`'s at two; each is
restated.

## Verification

Every commit builds. `scripts/pre-push.sh` passes at the end of the
branch, `lake lint` included, so every new declaration measures within
`{propext, Quot.sound}`.

`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` keeps the worked-tree
assertions it has and gains those of the deleted mirror, restated over
the new names:

- the spelling of the worked tree, `[true, true, false, false, false]`;
- the two words separating the conjuncts of validity in both directions —
  `[false, true, false]`, whose `depth` is one and whose `ok` is false,
  and `[false, false]`, whose `depth` is two and whose `ok` is true;
- `depth` and `ok` at the empty word and at a word of leaf bits only, and
  `depth_le_length` at each;
- the `DecidablePred binRanked.Valid` instance accepting `[false]` and
  rejecting `[true, false]`.

The sweep in that mirror comparing `binRanked.validBool` against
`decide (BinTree.Valid w)` becomes vacuous, both sides being one
function, and is replaced by a sweep with a subject:
`Cobham.isTreeSem ![w] == [true]` against `binRanked.validBool w`, over
every word of length at most eight. This cross-checks the function
algebra against the scan, which the deleted sweep did not, and it is what
would catch a slip in `scanStep_true_of_le`'s arithmetic.

The budget was measured, not predicted, against the sweep-budget fact of
[the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
§ Facts established by building item 22: under
`set_option maxRecDepth 100000 in decide` the sweep closes in about three
seconds at length four, four at six, eight at seven and nineteen at
eight. Length eight is therefore the sweep's word length, the same as the
sweep it replaces.

The sweep names both a recognizer and the scan, so it belongs to
`GebTests/Mathlib/Computability/Cobham/Tree.lean`, which imports
`GebTests.Mathlib.Data.Tree.Ranked.Basic` for `wordsUpTo`, rather than to
the `Data/Tree/` mirror, which would otherwise import a `Computability/`
module.

## Documentation

`docs/index.md` loses its entries for the two deleted modules and has its
`Ranked/Binary.lean`, `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`
entries restated. [TODO.md](../../../TODO.md) is amended in the same
branch:

- § Extensions of the tree recognizers records B4 as done, leaving B5.
- § Binary trees and their preorder encoding item 3, which asks what an
  upstream PR would argue for a second binary tree beside mathlib's
  `BinaryTree` measured differently, dissolves: `BinTree.size` no longer
  exists, and `RankedAlphabet.Term.size` is a measure of a term over an
  arbitrary ranked alphabet rather than a second unlabelled binary tree.
  The residual question — whether `Term.size` at `binRanked` should be
  stated through a transfer to `numNodes` — is recorded in its place.
- § Binary trees item 2, defining `ConcreteSyntax.Ast` from `BinTree`, is
  restated over the labelled ranked alphabet its item 1 describes.
- § Binary trees item 4, relating `print` to `DyckWord.equivTree`, is
  restated over `binRanked.spell`.

## Risks

- **The recognizer proofs are the branch's only real work.** Everything
  else is deletion and renaming. Both `combSem_eq` proofs are restated
  against a conditional depth lemma where they had an unconditional one.
  The mitigation is the sweep above, which fails on any arithmetic slip,
  and the measured agreement of the two counter forms under § The one
  place the shape changes.
- **`Cobham/Tree.lean` is 613 lines and `BellantoniCook/Tree.lean` 356,**
  and the restatements touch their docstrings as well as their proofs. A
  task-scoped review does not see a module-scoped defect, as
  [the session handoff](../plans/2026-08-10-tree-recognizer-session-handoff.md)
  records; the branch budgets a review that reads each module whole.
- **Deleting a module that `main` carries** makes the branch's diff a
  removal against a merged state rather than an addition. Nothing depends
  on the deleted modules outside this line, so no rebase of other work is
  implied, but the commit order — additions, then consumer restatements,
  then deletions — is what keeps each commit building.

## Out of scope

- **Whether `Cobham/Tree.lean` is itself now redundant.**
  `Cobham/RankedTree.lean` recognizes `binRanked.Valid` at an arbitrary
  ranked alphabet, so the bespoke two-symbol recognizer is a
  specialization of it. What `Cobham/Tree.lean` carries that the generic
  one does not is `isTree_smashFree`, membership in the subalgebra
  `SmashFree` names, and with it the [Strahm2003] Theorem 1(2) corollary.
  Recorded in `TODO.md` as its own branch, not decided here.
- **A bridge to mathlib's `BinaryTree`.** Nothing in the repository needs
  one, and B4's purpose is to remove an encoding rather than add a
  second bridge.
- **The deferrals `TODO.md` already records** — the namespace prefix in a
  declaration body, the placement of the choice-free `Nat` residue
  lemmas, `oneAtOf` and `falseAtOf` duplicating `constAtOf`, and the
  citation status of `BarringtonCorbett1989` — none of which this branch
  touches.
