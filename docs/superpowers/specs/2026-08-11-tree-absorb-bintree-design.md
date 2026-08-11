# Absorbing `BinTree` into the two-symbol ranked term algebra

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [What is deleted](#what-is-deleted)
- [Imports](#imports)
- [Orphaned references](#orphaned-references)
- [What `Ranked/Binary.lean` gains](#what-rankedbinarylean-gains)
- [The one place the shape changes](#the-one-place-the-shape-changes)
- [The consumers](#the-consumers)
- [Verification](#verification)
- [Documentation](#documentation)
- [Risks](#risks)
- [Out of scope](#out-of-scope)
- [Appendix: the compiled declarations](#appendix-the-compiled-declarations)

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

mathlib's coding-style guide, binding on `Geb/Mathlib/` content per
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Authoritative
upstream guides, requires a publicly exposed declaration being removed to
be kept under `@[deprecated (since := "YYYY-MM-DD")]`, a rename to leave a
deprecated `alias`, and deletion to wait six months. That requirement
does not bind this branch: it protects downstream users of a released
library, and nothing in `Geb/Mathlib/Data/Tree/` has been submitted
upstream, so no such user exists. It will bind once any of that directory
has shipped, and this exemption is not to be reused after that point.

## What is deleted

- `Geb/Mathlib/Data/Tree/Binary.lean` — the whole module:
  `BinTree.Shape`, `BinTree.Direction`, `BinTree`, `leaf`, `node`, `size`,
  `induction`, `size_leaf`, `size_node`. `RankedAlphabet.Term`,
  `Term.size`, `size_mk` and `Term.induction` cover every remaining use:
  after the deletions in this section no consumer of a leaf-and-node
  induction principle or of `size` at `binRanked` survives.
- `Geb/Mathlib/Data/Tree/Preorder.lean` — the whole module. `print`,
  `parseStep`, `parseAux`, `parse`, `depth`, `ok`, `Valid`, the
  `DecidablePred Valid` instance, and every theorem about them.
- From `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` — `ofBinTree`,
  `toBinTree`, `toBinTree_ofBinTree`, `ofBinTree_toBinTree`, `termEquiv`,
  `spell_termEquiv`, `valid_iff`. Each names `BinTree` or `print` in its
  statement, so each loses its subject. The module's docstring is
  restated with them; see § Orphaned references.
- `GebTests/Mathlib/Data/Tree/Preorder.lean` — the mirror of the second
  deleted module. Its declarations are itemized in § Verification, each
  with its disposition.

`binRanked`, `leafSym`, `nodeSym`, `leaf`, `node`, `code_leafSym`,
`code_nodeSym`, `spell_leaf` and `spell_node` stay: the alphabet is what
`Cobham/RankedTree.lean` instantiates at, and the constructors are what
the mirror's worked tree is built from.

## Imports

Six import lines name a deleted module. One dies with its own module;
the other five are edited.

| Site | Line | Disposition |
| --- | --- | --- |
| `Geb/Mathlib/Data/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Binary` | removed |
| `Geb/Mathlib/Data/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | removed |
| `GebTests/Mathlib/Data/Tree.lean` | `import GebTests.Mathlib.Data.Tree.Preorder` | removed |
| `Geb/Mathlib/Data/Tree/Preorder.lean` | `public import Geb.Mathlib.Data.Tree.Binary` | dies with the module |
| `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | removed |
| `Geb/Mathlib/Computability/Cobham/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | replaced by `public import Geb.Mathlib.Data.Tree.Ranked.Binary` |
| `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | replaced by `public import Geb.Mathlib.Data.Tree.Ranked.Binary` |

Neither recognizer imports `Geb.Mathlib.Data.Tree.Ranked.Binary` today —
only `Cobham/RankedTree.lean` does — so for both this is a new import,
not a redirected one. Both replacements are `public`, matching what they
replace: each module's statements name `binRanked.Valid` and the counter
form, so a caller reading those statements needs them.

The recognizers refer to the counter form as `Binary.depth` and
`Binary.ok` under `open RankedAlphabet`, rather than opening
`RankedAlphabet.Binary` and writing `depth` and `ok` bare. Unqualified,
those two names are short enough to collide with something a later import
brings in, and the qualified form is what the restated statements are
budgeted against for the 100-character line limit.

## Orphaned references

Seven references to deleted names sit outside the modules being deleted.
Each is restated in this branch.

| Site | What it says | Restatement |
| --- | --- | --- |
| `Ranked/Basic.lean` module docstring | "The unlabelled binary trees of `Data/Tree/Binary.lean` are the terms of the alphabet of one symbol of arity zero and one of arity two." | the same sentence over `RankedAlphabet.Binary`, which is now where those terms live |
| `Ranked/Basic.lean` Implementation notes | "`Term` is `@[expose]`, as `BinTree` is" | the reason stated without the comparison |
| `Ranked/Preorder.lean` module docstring | "`Data/Tree/Preorder.lean` is the case of one symbol of arity zero and one of arity two." | the same, naming `RankedAlphabet.Binary` |
| `Ranked/Binary.lean` module docstring | title, summary, which states the term algebra is equivalent to `BinTree` and the spelling is `BinTree.print`, `## Main definitions` (`termEquiv`), `## Main statements` (`spell_termEquiv`, `valid_iff`), `## Tags` ("equivalence") | restated in full: the module's subject after this branch is the two-symbol alphabet and the counter form of its scan, not an equivalence |
| `docs/index.md`, `Ranked/Preorder.lean` entry | "generalising `Geb/Mathlib/Data/Tree/Preorder.lean` from two unlabelled shapes to any ranked alphabet" | the generalization stated without the deleted module |
| `TODO.md` § The Bellantoni-Cook tree recognizer item 6 | "any statement relating `BinTree.Valid` to that predicate" | `binRanked.Valid` |
| `TODO.md` § Extensions of the tree recognizers, B1's done-entry | "`RankedAlphabet.Binary.termEquiv` exhibiting `BinTree` as the two-symbol instance with `spell_termEquiv` and `valid_iff`" | B1's deliverable restated as the alphabet and its scan, the equivalence having been absorbed |

## What `Ranked/Binary.lean` gains

The counter form of the validity scan at width one, as two projections and
their rewrite rules. Each rests on a general theorem already in
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`; none is a second recursion
over a word.

Every declaration below is compiled. They sit in
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean` in the working tree for the
duration of the spec-and-plan review rounds, so a reviewer can build
them, and they are transcribed in full under § Appendix. They become the
branch's first implementation commit. `lake build` passes;
`RankedAlphabet.Binary.buf_scanFinal_eq_nil`,
`valid_iff_ok_and_depth_eq_one`, `ok_cons_true` and
`depth_cons_true_of_ok_of_two_le_depth` each measure
`{propext, Quot.sound}`.

| Declaration | Statement | Provenance |
| --- | --- | --- |
| `depth (w : List Bool) : ℕ` | `(binRanked.scanFinal w).depth` | projection |
| `ok (w : List Bool) : Bool` | `(binRanked.scanFinal w).live` | projection |
| `buf_scanFinal_eq_nil` | `(binRanked.scanFinal w).buf = []` | `length_buf_scanFinal_lt` named as a hypothesis, then `omega`, then `List.eq_nil_of_length_eq_zero` |
| `depth_le_length` | `depth w ≤ w.length` | `depth_scanFinal_le_length` |
| `valid_iff_ok_and_depth_eq_one` | `binRanked.Valid w ↔ ok w = true ∧ depth w = 1` | `valid_iff_scanFinal` with `buf_scanFinal_eq_nil` |
| `decide_length_eq_width` | `decide (([b] : List Bool).length = binRanked.width) = true` | `decide` |
| `arOf_decodeBits_false` | `binRanked.arOf (decodeBits [false]) = some 0` | `decide` |
| `arOf_decodeBits_true` | `binRanked.arOf (decodeBits [true]) = some 2` | `decide` |
| `scanStep_false_of_live_of_buf_nil` | `binRanked.scanStep false s = ⟨[], s.depth + 1, true⟩` | `scanStep` unfolded |
| `scanStep_true_of_live_of_buf_nil_of_two_le_depth` | `binRanked.scanStep true s = ⟨[], s.depth - 2 + 1, true⟩` | `scanStep` unfolded |
| `scanStep_true_of_live_of_buf_nil_of_depth_lt_two` | `binRanked.scanStep true s = ⟨[], s.depth, false⟩` | `scanStep` unfolded |
| `scanStep_of_not_live` | `binRanked.scanStep b s = s` | `scanStep` unfolded |
| `ok_cons_false` | `ok (false :: w) = ok w` | the four `scanStep` lemmas |
| `ok_cons_true` | `ok (true :: w) = (ok w && decide (2 ≤ depth w))` | the four `scanStep` lemmas |
| `depth_cons_false_of_ok` | `depth (false :: w) = depth w + 1` | the four `scanStep` lemmas |
| `depth_cons_true_of_ok_of_two_le_depth` | `depth (true :: w) = depth w - 1` | the four `scanStep` lemmas |

`buf_scanFinal_eq_nil` names its bound as a hypothesis and discharges it
by `omega` rather than applying `Nat.lt_one_iff`, per
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
Lean code, whose fourth rule bars taking a `Nat` order bound from the
single lemma that states it. `Ranked/Preorder.lean` reaches
`List.eq_nil_of_length_eq_zero` the same way at three sites.

`ok_cons_false` and `ok_cons_true` carry `@[simp]`, as the `ok`
`cons`-lemmas they replace did. The two depth `cons`-lemmas do not: each
is conditional, so as a simp rule it would leave a side goal, and this
repository's simp-set linters are errors rather than warnings, so a rule
that fires without discharging its hypothesis fails the build. The four
`scanStep` lemmas and the three `decide` lemmas are not simp rules; they
exist to be named in a `rw` chain. `Ranked/Binary.lean`'s Implementation
notes record the reason.

Three facts the compilation settled:

- `decide (([b] : List Bool).length = binRanked.width)` does not
  iota-reduce inside `scanStep`'s `match`, though `binRanked.width` does
  reduce to `1`. The scrutinee is rewritten to `true` explicitly, which
  is why `decide_length_eq_width` exists and why the three `scanStep`
  lemmas do that reduction once rather than the four `cons`-lemmas doing
  it four times.
- A projection of a `Scan` constructor does not reduce syntactically, as
  [the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
  § Facts established by building item 12 states; `ok_cons_true` and
  `depth_cons_true_of_ok_of_two_le_depth` each need a `dsimp only` after
  the step rewrite.
- `depth` unfolds under `simp only [depth]` at a hypothesis and the goal
  together, which `depth_cons_true_of_ok_of_two_le_depth` needs so that
  `omega` sees `2 ≤ depth w` and `depth w - 2 + 1` in one language.

## The one place the shape changes

The deleted `depth` was a standalone counter with truncating subtraction,
so `depth (false :: v) = depth v + 1` held of every word. The scan
records failure in `live` and leaves `depth` alone thereafter, so the two
depth `cons`-lemmas carry an `ok w = true` hypothesis. The two `ok`
`cons`-lemmas are unconditional, and are the old ones verbatim.

Both recognizer proofs open with `cases hok : ok v`, and in the
`ok v = false` branch neither depth lemma is used, so every site that
rewrites by one has `ok v = true` in scope.

The rewrite does move, though, and both proofs are restructured rather
than renamed. Each currently rewrites by the unconditional
`depth_cons_true` before its three-way split
`depth v = 0 ∨ depth v = 1 ∨ ∃ m, depth v = m + 2`, and
`depth_cons_true_of_ok_of_two_le_depth` cannot be applied there, since
`2 ≤ depth v` becomes available only inside the split's third case. The
rewrite moves after the `obtain`; the first two cases close without
rewriting the depth of `true :: v` at all, the `ite` reducing on its
`Decidable` instance without forcing the branch that would read it.

The two counter forms agree where it matters, and this was measured
rather than argued: over every word of length at most eight, `ok` agrees
with the deleted `BinTree.ok` everywhere, and `depth` agrees with the
deleted `BinTree.depth` at every word where `ok` holds. They disagree
where `ok` fails, which is the freezing above and is why the agreement is
stated under that hypothesis.

## The consumers

The two recognizers do not change the same way, and one of the two
changes is larger than the other.

`Geb/Mathlib/Computability/Cobham/Tree.lean` — five statements:

- `combSem_eq` — `BinTree.ok` and `BinTree.depth` become `Binary.ok` and
  `Binary.depth`, with the depth rewrite moved inside the three-way split
  as § The one place the shape changes describes.
- `length_combSem_le` — `BinTree.depth_le_length` becomes
  `Binary.depth_le_length`. This is the branch's only consumer of the
  depth bound.
- `isTreeSem_eq_ite` and `isTreeSem_eq_singleton_iff_valid` — stated over
  `binRanked.Valid`. Neither reads the predicate's components, the second
  going through the first, so `valid_iff_ok_and_depth_eq_one` lands at
  two sites here.
- `isTreeSem_eq_singleton_iff_exists_print` — restated as acceptance of
  exactly `{w | ∃ u : binRanked.Term, binRanked.spell u = w}`, composed
  through `valid_iff_exists_spell` rather than the deleted
  `BinTree.valid_iff_exists_print`, and renamed
  `isTreeSem_eq_singleton_iff_exists_spell`.

`Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — four statements,
and no consumer of the depth bound: its `combRaw` is a `safeRec` node and
carries no recursion bound, so nothing here corresponds to
`length_combSem_le`.

- `combSem_eq` — as above.
- `isTreeSem_eq_singleton_iff_valid` and `isTreeSem_eq_ite` — these read
  the deleted `Valid`'s two conjuncts apart at five sites between them, by
  `⟨h, hd⟩`, `rintro ⟨-, hd'⟩`, `rintro ⟨h', -⟩`, `if_pos ⟨h, hd⟩` and two
  projections `hv.1`, `hv.2`. `binRanked.Valid` is a `Bool`
  equation rather than a conjunction, so each of the five goes through
  `valid_iff_ok_and_depth_eq_one`. This is the branch's largest single
  edit and the reason the two modules are specified separately.
- `isTreeSem_eq_singleton_iff_exists_print` — renamed and recomposed as
  above.

Both module docstrings name `BinTree` — in each case the summary
paragraph and several `## Main statements` bullets — and both are
restated.

## Verification

Every commit builds. `scripts/pre-push.sh` passes at the end of the
branch, `lake lint` included, so every new declaration measures within
`{propext, Quot.sound}`.

The deleted mirror `GebTests/Mathlib/Data/Tree/Preorder.lean` holds
nineteen declarations. Each is accounted for:

| Declarations | Disposition |
| --- | --- |
| `preorderSample` | redefined at `binRanked.Term` as `node (node leaf leaf) leaf`, in the surviving mirror as `binarySample` already is |
| `print_leaf_eq`, `print_node_leaf_leaf_eq`, `print_preorderSample_eq` | restated over `binRanked.spell`, by `decide` rather than `rfl`: `Nat.land`, which `code` runs through, is not exposed, so a block does not reduce during elaboration while the kernel evaluates it — the reason `Ranked/Binary.lean`'s own `code_leafSym` is `by decide` |
| `parse_print_leaf`, `parse_print_node_leaf_leaf`, `parse_print_preorderSample`, `parse_nil`, `parse_truncated`, `parse_trailing` | restated over `binRanked.parse` in `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`. `GebTests/…/Ranked/Preorder.lean` sweeps `validBool` against `isSome parse` but asserts no parse value and exhibits none of the three rejection mechanisms — empty input, a child's failure, trailing input — so these are restated rather than dropped, at the two-symbol alphabet where each mechanism is legible |
| `depth_node_at_depth_one`, `ok_node_at_depth_one`, `depth_two_leaves`, `ok_two_leaves` | restated over `Binary.depth` and `Binary.ok`. These are the words separating validity's two conjuncts in both directions, and both survive the counter change: at `[false, true, false]` the scan reads `false` to depth one, then fails on `true` at depth one and freezes there, giving `depth = 1` and `ok = false`; at `[false, false]`, `depth = 2` and `ok = true` |
| `valid_print_preorderSample`, `not_valid_two_leaves` | restated over `binRanked.Valid`. The first was `⟨rfl, rfl⟩` against a conjunction and becomes a `decide`, the predicate now being a `Bool` equation |
| `depth_le_length_nil`, `depth_le_length_leaves`, `depth_le_length_mixed` | all three restated over `Binary.depth_le_length`, at the empty word, at leaf bits only, and at a mixed word |
| `decide_valid_leaf`, `decide_not_valid_two_leaves` | restated against the `DecidablePred binRanked.Valid` instance |

`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` is restated in full
rather than extended: `binarySample`'s type is deleted, so it is
redefined at `binRanked.Term`; `spell_termEquiv_binarySample` names
`termEquiv` and becomes `spell_binarySample`; `print_binarySample` is the
other half of an agreement statement and goes; the sweep is replaced
below; and the module docstring's title, summary, `## Main definitions`,
`## Main statements` and `## Tags` all describe the equivalence and are
rewritten.

The sweep in that mirror comparing `binRanked.validBool` against
`decide (BinTree.Valid w)` loses its subject, both sides becoming one
function, and is replaced by `Cobham.isTreeSem ![w] == [true]` against
`binRanked.validBool w`, over every word of length at most eight, which
`wordsUpTo` makes 511 words.

What that sweep is and is not evidence for. It is not a check on the
arithmetic of `scanStep_true_of_live_of_buf_nil_of_two_le_depth`: every
declaration between that lemma and the recognizer is a theorem the kernel
checks, so a mis-stated step lemma either fails to prove or is true, and
no sweep can catch it. Nor is its proposition independent of the branch's
own theorems — once `isTreeSem_eq_singleton_iff_valid` is restated over
`binRanked.Valid`, and `binRanked.Valid w` is by definition
`binRanked.validBool w = true`, the sweep is a decidable instance of a
theorem in its own import closure. What it does check is that the two
sides still agree when computed rather than proved: it evaluates the
interpreter over the expression tree once per word and the scan's fold
once per word, by two routes, so it fails on an `@[expose]` regression or
a divergence between what `decide` reduces and what the proofs are about.
That is the warrant, and it is narrower than a correctness check.

The mitigation for the recognizer restatements is therefore not the
sweep. It is that the restated proofs must compile, together with the
module-whole review § Risks budgets, and the measured agreement of the
two counter forms under § The one place the shape changes.

The sweep's budget was measured, not predicted, against the sweep-budget
fact of
[the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
§ Facts established by building item 22: under
`set_option maxRecDepth 100000 in decide`, and with no other option set,
it closes in about three seconds at length four, five at six, ten at
seven and twenty at eight. Item 22's failure at 511 words was the fold
sweep reaching the heartbeat limit, a different computation; this one
does not reach it. Length eight is therefore the sweep's word length, the
same as the sweep it replaces.

The sweep names a recognizer and a scan, so it belongs to
`GebTests/Mathlib/Computability/Cobham/Tree.lean` rather than to a
`Data/Tree/` mirror, which would otherwise import a `Computability/`
module. That module has one import today, so the sweep adds two:
`public import GebTests.Mathlib.Data.Tree.Ranked.Basic` for `wordsUpTo`,
which sits inside that module's exposed public section, and
`Geb.Mathlib.Data.Tree.Ranked.Binary` for `binRanked.validBool`. Both are
permitted by
[docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md)'s
import table for `GebTests/Mathlib/`. That module's docstring is restated
to cover the sweep.

## Documentation

`docs/index.md` loses its entries for the two deleted modules, has its
`Ranked/Binary.lean`, `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`
entries restated, and has the reference to the deleted module removed
from its `Ranked/Preorder.lean` entry. [TODO.md](../../../TODO.md) is
amended in the same branch:

- § Extensions of the tree recognizers records B4 as done, leaving B5,
  and restates B1's done-entry per § Orphaned references.
- § The Bellantoni-Cook tree recognizer item 6 names `binRanked.Valid`.
- § Binary trees and their preorder encoding item 3, which asks what an
  upstream PR would argue for a second binary tree beside mathlib's
  `BinaryTree` measured differently, dissolves: `BinTree.size` no longer
  exists, and `RankedAlphabet.Term.size` measures a term over an
  arbitrary ranked alphabet rather than being a second unlabelled binary
  tree. The residual question — whether `Term.size` at `binRanked` should
  be stated through a transfer to `numNodes` — is recorded in its place.
- § Binary trees item 2, defining `ConcreteSyntax.Ast` from `BinTree`, is
  restated over the labelled ranked alphabet its item 1 describes.
- § Binary trees item 4, relating `print` to `DyckWord.equivTree`, is
  restated over `binRanked.spell`.
- § The namespace prefix in a declaration body cites four
  `BinTree.induction` sites inside `Geb/Mathlib/Data/Tree/Preorder.lean`
  and one `Term.mk` site inside `Ranked/Basic.lean`. This branch deletes
  the module carrying four of the five, so that section is restated over
  the surviving site alone. Whether one site still warrants a branch of
  its own, rather than a correction in passing, is recorded there and not
  decided here.

## Risks

- **The recognizer proofs are the branch's only work.** Everything else
  is deletion and renaming. Both `combSem_eq` proofs are restated against
  a conditional depth lemma where they had an unconditional one, with the
  rewrite moved inside a case split, and `BellantoniCook/Tree.lean`
  additionally routes five readings of the conjunction through
  `valid_iff_ok_and_depth_eq_one`. The mitigation is compilation plus the
  module-whole review below; § Verification states why the sweep is not
  it.
- **`Cobham/Tree.lean` and `BellantoniCook/Tree.lean` are long,** and the
  restatements touch their docstrings as well as their proofs. A
  task-scoped review does not see a module-scoped defect, as
  [the session handoff](../plans/2026-08-10-tree-recognizer-session-handoff.md)
  records; the branch budgets a review that reads each module whole.
- **Deleting a module that `main` carries** makes part of the branch's
  diff a removal against a merged state rather than an addition. Nothing
  outside this line depends on the deleted modules, so no rebase of other
  work is implied, but the commit order — additions, then consumer
  restatements, then deletions — is what keeps each commit building.
- **The counter form's names are short.** `depth` and `ok` in
  `RankedAlphabet.Binary` do not collide with anything today: the `Scan`
  fields of the same names are reachable only by field notation on a
  `Scan`, and neither recognizer's namespace declares either. § Imports
  states the qualified form the recognizers use, which is what keeps that
  true under a later import.

## Out of scope

- **Whether `Cobham/Tree.lean` is itself now redundant.**
  `Cobham/RankedTree.lean` recognizes `binRanked.Valid` at an arbitrary
  ranked alphabet, so the bespoke two-symbol recognizer is a
  specialization of it. What `Cobham/Tree.lean` carries that the generic
  one does not is `isTree_smashFree`, membership in the subalgebra
  `SmashFree` names, and with it the [Strahm2003] Theorem 1(2) corollary.
  Recorded in `TODO.md` as its own branch, not decided here.
- **A bridge to mathlib's `BinaryTree`.** Nothing in the repository needs
  one, and this branch's purpose is to remove an encoding rather than add
  a second bridge.
- **The `.vale.ini` in the tree that no gate runs.** Its default package
  set contradicts this repository's house style, flagging the spaced
  em-dash that every committed document uses and the filename `TODO.md`;
  `scripts/pre-push.sh` runs `doctoc` and `markdownlint-cli2` and not
  Vale. Adopting that configuration with those rules downgraded, or removing
  it, is its own branch.
- **The remaining deferrals `TODO.md` records** — the placement of the
  choice-free `Nat` residue lemmas, `oneAtOf` and `falseAtOf`
  duplicating `constAtOf`, and the citation status of
  `BarringtonCorbett1989` — none of which this branch touches. The
  namespace-prefix deferral is not among them; § Documentation amends it.

A note on concern shape. Replacing the sweep is arguably a second
concern: it introduces a subject the deletion does not otherwise touch,
lands in a module the deletion does not otherwise edit, and carries the
branch's only build-time cost. Deleting the sweep that loses its subject
belongs to this branch either way. Adding the replacement here is a
deliberate choice, on the ground that a branch removing a cross-check
should not leave the tree with less computational evidence than it found,
and it is recorded as a choice rather than a necessity.

## Appendix: the compiled declarations

Transcribed from `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`, where they
compile. Each declaration's docstring is elided here and present in the source.

```lean
@[expose] def depth (w : List Bool) : ℕ := (binRanked.scanFinal w).depth

@[expose] def ok (w : List Bool) : Bool := (binRanked.scanFinal w).live

theorem buf_scanFinal_eq_nil (w : List Bool) : (binRanked.scanFinal w).buf = [] := by
  have h : (binRanked.scanFinal w).buf.length < 1 := binRanked.length_buf_scanFinal_lt w
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem depth_le_length (w : List Bool) : depth w ≤ w.length :=
  binRanked.depth_scanFinal_le_length w

theorem valid_iff_ok_and_depth_eq_one (w : List Bool) :
    binRanked.Valid w ↔ ok w = true ∧ depth w = 1 := by
  rw [valid_iff_scanFinal]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, buf_scanFinal_eq_nil w, h.2⟩⟩

theorem decide_length_eq_width (b : Bool) :
    decide (([b] : List Bool).length = binRanked.width) = true := by cases b <;> decide

theorem arOf_decodeBits_false : binRanked.arOf (decodeBits [false]) = some 0 := by decide

theorem arOf_decodeBits_true : binRanked.arOf (decodeBits [true]) = some 2 := by decide

theorem scanStep_false_of_live_of_buf_nil (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) : binRanked.scanStep false s = ⟨[], s.depth + 1, true⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_false]
  rfl

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

theorem scanStep_true_of_live_of_buf_nil_of_depth_lt_two (s : Scan) (hl : s.live = true)
    (hb : s.buf = []) (h2 : s.depth < 2) :
    binRanked.scanStep true s = ⟨[], s.depth, false⟩ := by
  rw [scanStep, hl, hb]
  simp only []
  rw [decide_length_eq_width]
  simp only []
  rw [arOf_decodeBits_true]
  simp only []
  rw [decide_eq_false (Nat.not_le_of_lt h2)]

theorem scanStep_of_not_live (b : Bool) (s : Scan) (hl : s.live = false) :
    binRanked.scanStep b s = s := by
  rw [scanStep, hl]

@[simp] theorem ok_cons_false (w : List Bool) : ok (false :: w) = ok w := by
  rw [ok, ok, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live false _ h, h]
  · rw [scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

@[simp] theorem ok_cons_true (w : List Bool) :
    ok (true :: w) = (ok w && decide (2 ≤ depth w)) := by
  rw [ok, ok, depth, scanFinal_cons]
  cases h : (binRanked.scanFinal w).live
  · rw [scanStep_of_not_live true _ h, h, Bool.false_and]
  · rcases Nat.lt_or_ge (binRanked.scanFinal w).depth 2 with h2 | h2
    · rw [scanStep_true_of_live_of_buf_nil_of_depth_lt_two _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_false (Nat.not_le_of_lt h2), Bool.true_and]
    · rw [scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
      dsimp only
      rw [decide_eq_true h2, Bool.true_and]

theorem depth_cons_false_of_ok (w : List Bool) (h : ok w = true) :
    depth (false :: w) = depth w + 1 := by
  rw [depth, depth, scanFinal_cons,
    scanStep_false_of_live_of_buf_nil _ h (buf_scanFinal_eq_nil w)]

theorem depth_cons_true_of_ok_of_two_le_depth (w : List Bool) (h : ok w = true)
    (h2 : 2 ≤ depth w) : depth (true :: w) = depth w - 1 := by
  simp only [depth] at h2 ⊢
  rw [scanFinal_cons,
    scanStep_true_of_live_of_buf_nil_of_two_le_depth _ h (buf_scanFinal_eq_nil w) h2]
  dsimp only
  omega
```
