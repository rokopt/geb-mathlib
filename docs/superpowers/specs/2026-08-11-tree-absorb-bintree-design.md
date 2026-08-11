# Absorbing `BinTree` into the two-symbol ranked term algebra

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [What is deleted](#what-is-deleted)
- [Imports](#imports)
- [Orphaned references](#orphaned-references)
- [What `Ranked/Binary.lean` gains](#what-rankedbinarylean-gains)
- [Where the shape changes](#where-the-shape-changes)
- [The consumers](#the-consumers)
- [Verification](#verification)
- [Documentation](#documentation)
- [Risks](#risks)
- [Out of scope](#out-of-scope)
- [Appendix: what is in the tree, and what is not](#appendix-what-is-in-the-tree-and-what-is-not)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

One branch over `Geb/Mathlib/Data/Tree/`,
`Geb/Mathlib/Computability/` and their `GebTests/` mirrors, with entries in
`docs/index.md` and `TODO.md`; the item
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers records
as B4.

It depends on more than that entry states. B1 and B2 are named there; the
branch also restates `Cobham/RankedTree.lean`, which is B6's deliverable and
which reaches the case combinator, so B4 sits after B1, B2, the case
combinator and B6 in the dependency-ordered sequence
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Floodgate test promises. All
four are in place and none is merged: `main` carries `Data/Tree/Binary.lean`,
`Data/Tree/Preorder.lean` and earlier forms of the two recognizers — B2
rebuilt `Cobham/Tree.lean` on the scan combinator and that too is unpushed —
while the whole of `Data/Tree/Ranked/` and
`Cobham/{Scan,Cases,RankedTree,Fold}.lean` are unpushed on the line this
branch extends.

After it, one unlabelled binary-tree encoding is defined under
`Geb/Mathlib/`:
`RankedAlphabet.Binary.binRanked.Term` is the two-symbol tree,
`binRanked.spell` its preorder encoding, `binRanked.parse` its
fuel-bounded descent, and `binRanked.Valid` its language. The
`BinTree` type, its own encoding, and the equivalence bridging the two
developments are all deleted. `Geb/Internal/ConcreteSyntax.lean` keeps its
own labelled `Ast` with its own printer and descent; that duplication is
`TODO.md` § Binary trees item 2's subject and is untouched here.

Every definition below is a projection or a specialization of a
declaration already in `Geb/Mathlib/Data/Tree/Ranked/`. No definition or
theorem is taken from published mathematics, so the branch adds no key to
[docs/references.bib](../../references.bib). The mathematical content is
unchanged up to the equivalence the branch absorbs. Each recognizer keeps
every statement it has: two per module are restated over `binRanked.Valid`
(`isTreeSem_eq_ite` and `isTreeSem_eq_singleton_iff_valid`), and one per
module is renamed (`isTreeSem_eq_singleton_iff_exists_print` becomes
`…_exists_spell`), its existential re-typed from `BinTree` to
`binRanked.Term`. Each form follows from the other exactly through
`termEquiv` and `spell_termEquiv`, which this branch deletes, so after it
nothing in the repository derives one from the other.

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

Eight import lines name a module this branch deletes; two of those die with
their own module and the rest are edited. A ninth line names a module the
branch keeps, and is removed because the only use it serves goes with the
retired sweep.

| Site | Line | Disposition |
| --- | --- | --- |
| `Geb/Mathlib/Data/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Binary` | removed |
| `Geb/Mathlib/Data/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | removed |
| `GebTests/Mathlib/Data/Tree.lean` | `import GebTests.Mathlib.Data.Tree.Preorder` | removed |
| `Geb/Mathlib/Data/Tree/Preorder.lean` | `public import Geb.Mathlib.Data.Tree.Binary` | dies with the module |
| `GebTests/Mathlib/Data/Tree/Preorder.lean` | `import Geb.Mathlib.Data.Tree.Preorder` | dies with the module |
| `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | removed |
| `Geb/Mathlib/Computability/Cobham/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | replaced by `public import Geb.Mathlib.Data.Tree.Ranked.Binary` |
| `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` | `public import Geb.Mathlib.Data.Tree.Preorder` | replaced by `public import Geb.Mathlib.Data.Tree.Ranked.Binary` |
| `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` | `public import GebTests.Mathlib.Data.Tree.Ranked.Basic` | removed: `wordsUpTo` was its only use, in the sweep § Verification retires |

That last line is not optional. `scripts/pre-push.sh` runs
`lake shake --add-public --keep-implied --keep-prefix Geb GebTests`, and no
other import of that mirror implies it, so leaving it fails the branch's own
gate.

Neither recognizer imports `Geb.Mathlib.Data.Tree.Ranked.Binary` today; of
the source modules only `Cobham/RankedTree.lean` and the directory index
`Data/Tree/Ranked.lean` do. For both recognizers, then, this is a new
import rather than a redirected one. Both replacements are `public`,
matching what they replace: each module's statements name the alphabet's
language and the counter form, so a caller reading those statements needs
them. No module ends with a
`public import` beside a plain one, so the grouping rule
[the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
§ Facts established by building item 11 states does not arise; the one module
that has both loses its `public` line, and the blank line separating the
groups goes with it.

Both recognizers open `RankedAlphabet.Binary` and nothing else, and write
`depth`, `ok` and `binRanked` bare. The alternative — opening
`RankedAlphabet` as well so that the counter form can be written
`Binary.depth` — was compiled and rejected: the qualified form needs the
wider open, and `open RankedAlphabet` brings `mod_two_mul` and `add_one_mod`
bare beside `Nat`'s own residue API, which is the subject of a deferral
`TODO.md` already records, so taking it would widen that deferral's surface
across two long modules. Under the narrow open `Binary.ok` does not resolve
at all, and bare `ok` and `depth` collide with nothing: neither recognizer's
namespace declares either, which the build confirms. `valid_iff_exists_spell` is
then reached by generalized field notation, `binRanked.valid_iff_exists_spell`,
at its one use.

## Orphaned references

References to deleted names sit outside the modules being deleted. Each is
restated in this branch.

| Site | What it says | Restatement |
| --- | --- | --- |
| `Ranked/Basic.lean` module docstring | "The unlabelled binary trees of `Data/Tree/Binary.lean` are the terms of the alphabet of one symbol of arity zero and one of arity two." | the same sentence over `RankedAlphabet.Binary`, which is now where those terms live |
| `Ranked/Basic.lean` Implementation notes | "`Term` is `@[expose]`, as `BinTree` is" | the reason stated without the comparison |
| `Ranked/Preorder.lean` module docstring | "`Data/Tree/Preorder.lean` is the case of one symbol of arity zero and one of arity two." | the same, naming `RankedAlphabet.Binary` |
| `Cobham/Tree.lean`, `isTree_smashFree`'s docstring, as implemented | states the corollary over `RankedAlphabet.Valid` at `binRanked` rather than over a `binRanked.Valid` spelling | as implemented; the row above it describes the same edit |
| `Ranked/Binary.lean` module docstring | title, summary, which states the term algebra is equivalent to `BinTree` and the spelling is `BinTree.print`, `## Main definitions` (`termEquiv`), `## Main statements` (`spell_termEquiv`, `valid_iff`), `## Tags` ("equivalence") | restated in full: the module's subject after this branch is the two-symbol alphabet and the counter form of its scan, not an equivalence |
| `Cobham/RankedTree.lean`, `isRankedSem_binRanked_eq_singleton_iff_isTreeSem`'s docstring | "neither `binRanked`'s `width` and `maxArity` nor the two scans' differing failure conventions need reconciling" | false once one scan remains; restated as the two recognizers deciding one predicate |
| `Cobham/Tree.lean`, `isTree_smashFree`'s docstring | "the decision of `BinTree.Valid` is computable simultaneously in polynomial time and linear space" | restated over `binRanked.Valid`. This is a declaration docstring, not the module's, and it carries the [Strahm2003] Theorem 1(2) attribution § Out of scope treats as the residue justifying the module's survival, so the restatement is load-bearing |
| `Cobham/Tree.lean` Implementation notes, and its smash-free paragraph | name `BinTree.depth_le_length` and `BinTree.Valid` | restated over the counter form and the alphabet's language |
| `Cobham/Tree.lean`, `length_combSem_le`'s docstring | "the depth never exceeds the word length (`BinTree.depth_le_length`)" | the counter form's bound |
| `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`, `isTreeSem_eq_singleton_iff_valid`'s docstring in each | "The recognizer accepts exactly the words satisfying `BinTree.Valid`." | the words the two-symbol alphabet's scan accepts |
| `BellantoniCook/Tree.lean`, `isTreeSem_eq_ite`'s docstring | "The recognizer is the indicator of `BinTree.Valid`" | the indicator of `binRanked.Valid` |
| `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`, each `## Main statements` bullet for the renamed theorem | name `isTreeSem_eq_singleton_iff_exists_print` | the new name |
| `GebTests/…/Ranked/Basic.lean`, `length_wordsUpTo_eight`'s docstring | "The enumeration the `Preorder` and `Binary` mirrors sweep" | it names the two siblings in `GebTests/…/Ranked/`, and the `Binary` one's sweep is retired; the docstring names `Ranked/Preorder.lean`, which still sweeps there, alone |
| `docs/index.md`, `Ranked/Preorder.lean` entry | "generalising `Geb/Mathlib/Data/Tree/Preorder.lean` from two unlabelled shapes to any ranked alphabet" | the generalization stated without the deleted module |
| `TODO.md` § The Bellantoni-Cook tree recognizer item 6 | "any statement relating `BinTree.Valid` to that predicate" | `binRanked.Valid` |
| `TODO.md` § Extensions of the tree recognizers, B1's done-entry | "`RankedAlphabet.Binary.termEquiv` exhibiting `BinTree` as the two-symbol instance with `spell_termEquiv` and `valid_iff`" | B1's deliverable restated as the alphabet and its scan, the equivalence having been absorbed |

Some persistent documentation, as against names, exists only in the deleted
modules. Deleting them would lose content the ranked development does
not carry, so each moves rather than dying.

- **The `DyckWord` comparison** (`Data/Tree/Preorder.lean`, echoed in
  `docs/index.md`): validity is stated as two conditions in the manner of
  mathlib's `DyckWord`, whose `count_U_eq_count_D` and `count_D_le_count_U`
  play the roles the depth and the underflow verdict play here. That is the
  record of an adjacent mathlib abstraction deliberately not reused, which
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost asks a module to
  keep, together with its second clause — that validity is stated in the
  direction a single right-to-left pass carrying a counter can scan.
  `Ranked/Preorder.lean` does not mention `DyckWord`; both clauses move to its
  module docstring, generalized to the pending count and the liveness flag.
  `docs/index.md` echoes it inside the entry for the deleted
  module, so the echo moves to that module's entry with it — deleting the
  entry alone would leave the record in one of its two homes.
- **The argument that fuel exhaustion is not a rejection mechanism of its
  own** (`Data/Tree/Preorder.lean` Implementation notes): each descent layer
  consumes at least the head bit before delegating, so the invariant that the
  fuel is at least the remaining length holds from the initial length down,
  and at zero fuel the remaining input is already empty.
  `Ranked/Preorder.lean` carries the fuel-bounded descent but not this
  argument. It moves there generalized: a layer consumes a whole block, which
  `width_pos` makes at least one bit, and the generic descent's rejections
  are `decodeBlock`'s two — input short of a block, and a block spelling no
  symbol — together with a child's failure and the trailing input `parse`
  rejects. The count of three belongs to `binRanked`, where a block is one
  bit and every block spells a symbol, and § Verification uses it only
  there.
- **The initial-algebra characterization** (`Data/Tree/Binary.lean`
  docstring): that these trees are the initial algebra of `F X = 1 + X × X`.
  Nothing surviving says that of `binRanked.Term`, and `TODO.md` § Binary
  trees items 1 and 2 are phrased in those terms, so it moves to
  `Ranked/Binary.lean`'s restated docstring. Two neighbouring notes die with
  their subject rather than moving: that `Direction` follows the
  polynomial-functor modules' fibre-naming convention, and that it sends
  `leaf` to `Fin 0` rather than `Empty` so both fibres lie in one family. The
  ranked family is `fun i ↦ Fin (R.arity i)` by construction, so neither
  observation has anything left to be about.
- **`size`'s upstream adjacency** (`Data/Tree/Binary.lean`): that extracted
  upstream it would sit beside `BinaryTree.numNodes`, `numLeaves` and
  `height` and is none of the three. The observation now concerns
  `RankedAlphabet.Term.size`; § Documentation records where it lands in
  `TODO.md`.

## What `Ranked/Binary.lean` gains

The counter form of the validity scan at width one, as two projections and
their rewrite rules. The projections are `depth` and `ok`; the facts about
the whole scan (`buf_scanFinal_eq_nil`, `depth_le_length`,
`valid_iff_ok_and_depth_eq_one`) and the four `cons`-lemmas rest on general
theorems already in
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`; the two `arOf_decodeBits_*` lemmas
rest on `Ranked/Code.lean` and kernel evaluation, and `decide_length_eq_width`
on kernel evaluation alone; and three of the four `scanStep`
lemmas are that module's `scanStep` unfolded at width one. The fourth,
`scanStep_of_not_live`, holds at any width — a failed scan absorbs whatever
the block layout — and is stated at `binRanked` because that is where its two
consumers are; it moves to `Ranked/Preorder.lean` if a second alphabet ever
needs it. None is a second
recursion over a word.

Every declaration below is compiled, and so is its use. The counter form
sits in `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` in the working tree, and
`Cobham/Tree.lean` and `Cobham/RankedTree.lean` are restated on it there
too — the whole of § The consumers bar the Bellantoni-Cook module. A
reviewer builds them rather than reading a transcription; § Appendix lists
what is where. They become the branch's first implementation commits.

`lake build` passes, and `lake lint` passes over both `Geb` and `GebTests`,
which is the scope the axiom linter runs over, so every declaration below
measures within the permitted `{propext, Quot.sound}` rather than a chosen
few measuring it narrowly.
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
Lean code's first rule asks for the measurement to be taken in the closure
of the module that consumes the declarations. That closure is the restated
`Cobham/Tree.lean`'s, which is enlarged by the import swap — see § Risks —
and the passing lint is taken with the swap in place, so it is the
measurement that binds rather than a narrow one. It is run again at the end
of the branch, when `BellantoniCook/Tree.lean` joins that closure.

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

The two names are the deleted module's. `depth` projects `Scan.depth` and
matches it; `ok` projects `Scan.live` and does not, and the parent namespace's
convention for a `Bool` beside a `Prop` is `validBool` beside `Valid`. `live`
was considered and rejected: liveness is a property of a scan state, whereas
these are functions of a word, and `ok w` reads as a verdict on `w` where
`live w` reads as a category error. `validBool` is taken and means something
stronger — validity is the verdict together with an empty buffer and one
pending subterm — so the pair stays `depth` and `ok`.

Defining `depth` and `ok` at all was weighed against writing
`(binRanked.scanFinal w).depth` and `.live` at every site and stating the four
`cons`-lemmas over those projections, which would add no names beside the
`Scan` fields and raise no collision question. The two definitions are kept
because the `cons`-lemmas need a subject to be about — a rewrite rule over a
projection of a `foldr` reads as a fact about the fold rather than about a
counter — and because the recognizers' statements are what a reader reads, and
they carry the counter's meaning better at one word than at a projection.
`depth_le_length` is a wrapper — `Nat.succ_le_succ
(binRanked.depth_scanFinal_le_length u)` closes its one proof site without it
— and it earns its place by being named rather than applied: it is the bound
`Cobham/Tree.lean`'s Implementation notes and `length_combSem_le`'s docstring
cite as the reason the recursion bound holds, and the bound the restated
mirror instances at three words. A cited name is what those five references
need; an inlined term would leave them citing a generic lemma about a scan
state where the reader is reading about a counter.

`buf_scanFinal_eq_nil` names its bound as a hypothesis and discharges it
by `omega` rather than applying `Nat.lt_one_iff`, per
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
Lean code, whose fourth rule bars taking a `Nat` order bound from the
single lemma that states it. `ok_cons_true` takes its two-way split from
`Nat.lt_or_ge`, which needs no exemption: case analysis is the other route
that rule permits outright.

`Ranked/Preorder.lean` reaches `List.eq_nil_of_length_eq_zero` at three
sites by routes other than this one, one of them `Nat.le_zero.mp` — which is
the single lemma stating its bound, and so is the thing the fourth rule bars.
That predates this branch and is not fixed here; § Documentation records it
in `TODO.md` instead.

`ok_cons_false` and `ok_cons_true` carry `@[simp]`. No proof in this branch
reaches them that way — both recognizers name them in `rw` chains — so the
ground is forward-looking rather than historical: they are unconditional
rewrite rules on a public counter form, which is the shape a caller's `simp`
is entitled to reach, and the shape mathlib registers `_cons` lemmas in. No
counterpart of the deleted `depth_nil` and
`ok_nil` is
added: the recognizers' base case closes by `rfl` through the projections
without one, which was compiled, and a lemma no proof names is a
registration without a return. The two depth `cons`-lemmas carry no `@[simp]`
either, and the reason is not that a conditional simp rule misbehaves — one
whose hypothesis
`simp` cannot discharge does not fire at all, leaving no side goal. It is
that neither `ok w = true` nor `2 ≤ depth w` is a side condition `simp`
discharges on its own here, so as simp rules the two would be inert
wherever they were reached, and an inert rule is a registration without a
return. The four `scanStep` lemmas and the three `decide` lemmas are not
simp rules either; they exist to be named in a `rw` chain.
`Ranked/Binary.lean`'s Implementation notes record the reason.

The two depth `cons`-lemmas being unregistered shrinks the simp set: their
deleted counterparts `BinTree.depth_cons_false` and `BinTree.depth_cons_true`
were `@[simp]`. No surviving proof reaches them through `simp`; both
recognizers name them in `rw` chains, which is why the restatement is a
rewrite substitution rather than a simp-set migration.

Facts the compilation settled:

- `decide (([b] : List Bool).length = binRanked.width)` does not
  iota-reduce inside `scanStep`'s `match`, though `binRanked.width` does
  reduce to `1`. The scrutinee is rewritten to `true` explicitly, which
  is why `decide_length_eq_width` exists and why the three `scanStep`
  lemmas do that reduction once rather than the four `cons`-lemmas doing
  it four times.
- A projection of a `Scan` constructor does not reduce syntactically, as
  [the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
  § Facts established by building item 12 states;
  `depth_cons_true_of_ok_of_two_le_depth` needs a `dsimp only` after the
  step
  rewrite, and `ok_cons_true` one in each branch of its case split.
- `depth` unfolds under `simp only [depth]` at a hypothesis and the goal
  together, which `depth_cons_true_of_ok_of_two_le_depth` needs so that
  `omega` sees `2 ≤ depth w` and `depth w - 2 + 1` in one language.
- `decide_length_eq_width`'s `cases b` is not decoration, though
  `([b] : List Bool).length` is `1` whatever `b` is. `decide` refuses a goal
  carrying a free variable, as
  [the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
  § Facts established by building item 2 records of a symbol index that is
  itself a pattern variable — the same refusal, not that item's separate
  unassigned-metavariable failure. The case analysis is what closes `b`, and
  dropping it fails elaboration on a free-variable expected type.

## Where the shape changes

The deleted `depth` was a standalone counter with truncating subtraction,
so `depth (false :: v) = depth v + 1` held of every word. The scan
records failure in `live` and leaves `depth` alone thereafter, so the two
depth `cons`-lemmas carry an `ok w = true` hypothesis. The two `ok`
`cons`-lemmas are unconditional, and are the old ones verbatim.

Both recognizer proofs drive their recursion with `List.rec` and then case on
`hok : ok v`, and in the `ok v = false` branch neither depth lemma is used,
so every site that
rewrites by one has `ok v = true` in scope.

The rewrite does move, though, and both proofs are restructured rather
than renamed. Each currently rewrites by the unconditional
`depth_cons_true` before its three-way split
`depth v = 0 ∨ depth v = 1 ∨ ∃ m, depth v = m + 2`, and
`depth_cons_true_of_ok_of_two_le_depth` cannot be applied there, since
`2 ≤ depth v` becomes available only inside the split's third case. The
rewrite moves after the `obtain`, where `hm : depth v = m + 2` supplies the
hypothesis by `omega`; the first two cases close without rewriting the depth
of `true :: v` at all.

That restructuring is compiled, not projected: `Cobham/Tree.lean`'s
`combSem_eq` is restated in the working tree in exactly this shape and
builds, as do `length_combSem_le` — whose `cases` on the verdict changes
name along with its rewrite — `isTreeSem_eq_ite` with
`valid_iff_ok_and_depth_eq_one` at its three conjunct readings,
`isTreeSem_eq_singleton_iff_valid` over `binRanked.Valid`, the rename to
`isTreeSem_eq_singleton_iff_exists_spell`, and
`Cobham/RankedTree.lean`'s collapsed bridge. The base case needed no change:
both proofs open `refine List.rec (motive := …) rfl ?_ w`, and that `rfl`
still closes, `binRanked`, `depth`, `ok`, `scanFinal`, `scanFrom` and
`scanStep` all being `@[expose]`, which is what decides whether they unfold
across a module boundary.

`BellantoniCook/Tree.lean` is the one consumer not yet restated. Its
`combSem_eq` has the same shape as Cobham's, so the same restructuring
applies; what is particular to it is the number of conjunct readings, and
those are substitutions rather than restructurings.

The two counter forms agree where it matters, by one induction rather than
two. The two claims are not separable: `ok_cons_true` reads
`decide (2 ≤ depth w)` on each side, with a different `depth` on each, so
the `ok` agreement cannot be established before the depth agreement, and
the depth agreement holds only where `ok` does. The statement proved by
induction on the word is therefore the conjunction, guarded:
`ok w = BinTree.ok w`, and `depth w = BinTree.depth w` whenever `ok w`.
At `[]` the scan is `⟨[], 0, true⟩` and the deleted counters are `0` and
`true`. At `false :: v` both push. At `true :: v` the case split on `ok v`
carries it, the two depths coinciding because `depth v - 2 + 1` and
`depth v - 1` agree wherever `2 ≤ depth v`, which is the conjunct of
`ok (true :: v)` rather than of `ok v`. Below that threshold the scan does not
compute `depth v - 2 + 1` at all: it freezes the count and clears the liveness
flag, while the deleted counter keeps subtracting. At `v = [false]` that is
the difference between a frozen `1` and a subtracted `0`.

That conjunction was also checked by computation during design, over every
word of length at most eight, in the guarded form the induction takes. The
check cannot land: it names `BinTree.ok`, which this branch deletes. It is
carried in § Appendix so that it can be re-run, and it is not among the
branch's evidence — the induction above is.

## The consumers

Three modules consume what this branch deletes, and none changes the same
way as another.

`Geb/Mathlib/Computability/Cobham/Tree.lean`:

- `combSem_eq` — `BinTree.ok` and `BinTree.depth` become `Binary.ok` and
  `Binary.depth`, with the depth rewrite moved inside the three-way split
  as § Where the shape changes describes.
- `length_combSem_le` — `BinTree.depth_le_length` becomes
  `Binary.depth_le_length`, unconditionally. This is the branch's only
  consumer of the depth bound: `BellantoniCook/Tree.lean`'s `combRaw` is a
  `safeRec` node and carries no recursion bound.
- `isTreeSem_eq_ite` — stated over `binRanked.Valid`, and it reads the
  deleted predicate's conjuncts at three places: `if_pos ⟨h, hd⟩`, and
  `hv.2` and `hv.1` inside two `if_neg` arguments. Each goes through
  `valid_iff_ok_and_depth_eq_one`.
- `isTreeSem_eq_singleton_iff_valid` — stated over `binRanked.Valid`. It
  goes through `isTreeSem_eq_ite` and reads no conjunct itself.
- `isTreeSem_eq_singleton_iff_exists_print` — restated as acceptance of
  exactly `{w | ∃ u : binRanked.Term, binRanked.spell u = w}`, composed
  through `valid_iff_exists_spell` rather than the deleted
  `BinTree.valid_iff_exists_print`, and renamed
  `isTreeSem_eq_singleton_iff_exists_spell`.

`Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — the same statements
bar the depth bound, its own
`isTreeSem_eq_singleton_iff_exists_print` renamed and recomposed exactly as
Cobham's is, and it reads the conjuncts at more places than Cobham does:
`⟨h, hd⟩`, `rintro ⟨-, hd'⟩` and `rintro ⟨h', -⟩` in
`isTreeSem_eq_singleton_iff_valid`, and `if_pos ⟨h, hd⟩` with the
projections `hv.2` and `hv.1` in `isTreeSem_eq_ite`. `binRanked.Valid` is
a `Bool` equation rather than a conjunction, so every one of them goes
through `valid_iff_ok_and_depth_eq_one`. Its `combSem_eq` changes as
Cobham's does, and it has no `length_combSem_le`.

`Geb/Mathlib/Computability/Cobham/RankedTree.lean` —
`isRankedSem_binRanked_eq_singleton_iff_isTreeSem` is proved as
`(isRankedSem_eq_singleton_iff_valid _ w).trans
((RankedAlphabet.Binary.valid_iff w).trans (isTreeSem_eq_singleton_iff_valid
w).symm)`, and `valid_iff` is deleted.
The middle link does not need replacing: once
`isTreeSem_eq_singleton_iff_valid` is stated over `binRanked.Valid`, both
outer links speak of the same predicate and the proof collapses to
`(isRankedSem_eq_singleton_iff_valid _ w).trans
(isTreeSem_eq_singleton_iff_valid w).symm`. Its docstring is restated per
§ Orphaned references, and the collapse bears on § Out of scope's
redundancy question: after this branch the two recognizers decide one
predicate rather than two predicates shown equivalent, which strengthens
that question rather than leaving it as it was.

Both recognizers' module docstrings name `BinTree`: in each the summary
paragraph and several `## Main statements` bullets, and in Cobham's also the
smash-free paragraph and the Implementation notes. Both are restated, along
with the declaration docstrings § Orphaned references lists.

## Verification

Every commit builds. `scripts/pre-push.sh` passes at the end of the
branch — `lake shake` and `lake lint` included, so no import is left
unused and every declaration measures within `{propext, Quot.sound}`.

The deleted mirror `GebTests/Mathlib/Data/Tree/Preorder.lean` holds
twenty-one declarations. Each is accounted for, and every restatement lands
in `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`.

| Declarations | Disposition |
| --- | --- |
| `preorderSample` | redefined at `binRanked.Term` as `node (node leaf leaf) leaf`, merging with the `binarySample` that mirror already declares. Its docstring records that its `size` is five, counting leaves alongside internal nodes; that carries over to `RankedAlphabet.Term.size`, which counts the same way |
| `print_leaf_eq` | dropped: restated over `spell` it is `binRanked.spell leaf = [false]`, which is `RankedAlphabet.Binary.spell_leaf`, an `@[simp]` theorem the branch keeps. A mirror restating a library lemma is code without a return |
| `print_node_leaf_leaf_eq` | restated over `binRanked.spell`, by `decide` rather than `rfl`: `Nat.land`, which `code` runs through, is not exposed, so a block does not reduce during elaboration while the kernel evaluates it — the reason `Ranked/Binary.lean`'s own `code_leafSym` is `by decide` |
| `print_preorderSample_eq` | collapses into the surviving mirror's `spell_binarySample`: once `preorderSample` and `binarySample` are one term, the two statements are the same equation. The surviving name is kept |
| `parse_print_leaf`, `parse_print_node_leaf_leaf`, `parse_print_preorderSample` | restated over `binRanked.parse`, by `decide`, in the form `(binRanked.parse w).map binRanked.spell = some w` that `GebTests/…/Ranked/Preorder.lean` already uses for its two descent assertions |
| `parse_nil`, `parse_truncated`, `parse_trailing` | restated over `binRanked.parse`, by `decide`, in the form `(binRanked.parse w).map binRanked.spell = none` rather than `binRanked.parse w = none`: the latter is an equation in `Option binRanked.Term`, needing a `DecidableEq` on the W-type that the sibling mirror's Implementation notes record avoiding. These are the descent's three rejection mechanisms — empty input, a child's failure, trailing input. `GebTests/…/Ranked/Preorder.lean` asserts two descent values and sweeps `validBool` against `isSome parse`, but exhibits no rejection value, so these are restated rather than dropped |
| `depth_node_at_depth_one`, `ok_node_at_depth_one`, `depth_two_leaves`, `ok_two_leaves` | restated over `Binary.depth` and `Binary.ok`. These are the words separating validity's two conjuncts in both directions, and both survive the counter change: at `[false, true, false]` the scan reads `false` to depth one, then fails on `true` at depth one and freezes there, giving `depth = 1` and `ok = false`; at `[false, false]`, `depth = 2` and `ok = true` |
| `valid_print_preorderSample`, `not_valid_two_leaves` | restated over `binRanked.Valid`, both changing shape: the first was `⟨rfl, rfl⟩` against a conjunction and the second `fun h ↦ absurd h.2 (by decide)`, and the predicate is now a `Bool` equation, so each becomes a `decide` |
| `depth_le_length_nil`, `depth_le_length_leaves`, `depth_le_length_mixed` | all three restated over `Binary.depth_le_length`, at the empty word, at leaf bits only, and at a mixed word |
| `decide_valid_leaf`, `decide_not_valid_two_leaves` | restated against the `DecidablePred binRanked.Valid` instance. The second is renamed while it is restated: its word is `[true, false]`, a node bit and a leaf bit, not two leaves |

`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` is restated in full rather
than extended: `binarySample`'s type is deleted, so it is redefined at
`binRanked.Term`; `spell_termEquiv_binarySample` names `termEquiv` and
becomes `spell_binarySample`; `print_binarySample` is the other half of an
agreement statement and goes; the sweep is replaced below; the
`GebTests.Mathlib.Data.Tree.Ranked.Basic` import goes with it, per
§ Imports; and the module docstring's title, summary, `## Main definitions`,
`## Main statements` and `## Tags` all describe the equivalence and are
rewritten.

The sweep in that mirror is
`(wordsUpTo 8).all (fun w ↦ binRanked.validBool w == decide (BinTree.Valid w))`
— the ranked scan against the deleted counter, over 511 words, which is
`valid_iff` checked by computation. Its subject is `BinTree.Valid`, so once
that is deleted the sweep is not merely vacuous but inexpressible. It is
deleted with nothing put in its place.

What is lost is one word length, not a kind of check. A cross-check of
`binRanked.validBool` against an independent implementation of the same
language survives the branch untouched:
`GebTests/…/Cobham/RankedTree.lean`'s `isRankedSem_eq_validBool_binRanked`
sweeps `Cobham.isRankedSem binRanked ![w] == [true]` against
`binRanked.validBool w` over every word of length at most six, which
`wordsUpTo` makes 127. `isRankedSem` at that alphabet is a Cobham expression
evaluated through `C.eval`, so it is a second implementation in exactly the
sense the retired sweep's `BinTree.Valid` was. Computational coverage of
`validBool` at `binRanked` therefore drops from 511 words to 127, plus the
worked words the mirrors pin — not to the worked words alone. The sweeps in
`GebTests/…/Ranked/Preorder.lean` are at `sampleAlphabet` and
`narrowAlphabet` and bear on the generic scan rather than on this alphabet.

That is the whole of the loss, and the ground for accepting it is that 511
words buy nothing over 127 for a check whose subject is a definitional
agreement rather than a boundary: the scan at `binRanked` is an instance of
the generic scan, and the recognizer over it is proved rather than sampled.

The `isTreeSem` variant of that sweep — `Cobham.isTreeSem ![w] == [true]`
against `binRanked.validBool w` — is the replacement a reader would
reach for first, and it earns nothing. At every word it follows from
`isRankedSem_eq_validBool_binRanked` together with
`isRankedSem_binRanked_eq_singleton_iff_isTreeSem`, the bridge theorem this
branch collapses; asserting it would restate a consequence of two theorems the
repository already carries. § Out of scope declines it on that ground.

What such a sweep would check beyond redundancy is that `decide` reduces each
side to what its proofs are about. The branch has that at three words, from
assertions it restates anyway. A literal value assertion buys it more strongly
than an agreement assertion, since an agreement can hold with both sides wrong
while a value cannot, and a pair of literal assertions at one word implies the
agreement there. The requirement this places on the branch is not new code but
a constraint on which words the two mirrors pin: they must keep meeting at an
accepting word and at a rejecting one.

| Word | `isTreeSem` pinned in `GebTests/…/Cobham/Tree.lean` | the scan pinned in `GebTests/…/Ranked/Binary.lean` |
| --- | --- | --- |
| `[false]` | `isTreeSem_leaf`, `= [true]`, by `rfl` | `decide (binRanked.Valid [false]) = true`, restated from `decide_valid_leaf` |
| `[false, true, false]` | `isTreeSem_underflow`, `= []`, by `rfl` | `depth = 1`, `ok = false`, and `¬ binRanked.Valid`, the first two restated from `depth_node_at_depth_one` and `ok_node_at_depth_one` and the third added, so that this word pins the predicate by reduction as the other two do rather than only through `valid_iff_ok_and_depth_eq_one` |
| `[false, false]` | `isTreeSem_wrong_depth`, `= []`, by `rfl` | `depth = 2`, `ok = true`, and `¬ binRanked.Valid`, restated from `depth_two_leaves`, `ok_two_leaves` and `not_valid_two_leaves` |

Each is kernel-evaluated, by `rfl` on the recognizer side and `decide` on the
scan side, so a drift in either route's reduction fails one of them.

`GebTests/Mathlib/Computability/Cobham/Tree.lean` is therefore not edited at
all, and needs no new import, no `open` and no docstring change: its
docstrings' bare `ok` remains true of the counter form, which agrees with the
deleted verdict everywhere.

`GebTests/Mathlib/Computability/BellantoniCook/Tree.lean` is edited, for its
names rather than its statements: `isTreeSem_print_leaf`,
`isTreeSem_print_node` and `isTreeSem_print_asymmetric` are built on
`BinTree.print` and become `isTreeSem_spell_*`. Its values and tactics are
unchanged, the words being the same bitstrings either way. A
sweep-scale cross-check of the recognizer against the scan is recorded in
`TODO.md` as its own branch, for whoever wants one; it is not this branch's
concern, and the argument for adding it here did not survive stating what it
would be evidence for.

## Documentation

`docs/index.md` loses its entries for the two deleted modules and has its
`Ranked/Binary.lean`, `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`
entries restated. Its `Cobham/RankedTree.lean` entry needs no change: it
describes what the bridge theorem states, which this branch does not alter,
only how it is proved. Its `Ranked/Preorder.lean` entry
changes twice: the reference to the deleted module comes out, and the
`DyckWord` comparison § Orphaned references moves goes in, since the entry
that echoes it today is one of the two being deleted.

`Geb/Mathlib/Data/Tree.lean` is left re-exporting one module, itself an
index, and `GebTests/Mathlib/Data/Tree.lean` importing one. They stay: the
narrow-and-deep convention gives each directory one indexing file, and
`Geb/Mathlib/Data/Tree/` remains a directory whose contents may grow — the
labelled-alphabet item of `TODO.md` § Binary trees would add to it. Nothing
about the pair is changed beyond the import removals.

[TODO.md](../../../TODO.md) is amended in the same branch:

- § Extensions of the tree recognizers records B4 as done, leaving B5, and
  restates B1's done-entry per § Orphaned references.
- § Extensions of the tree recognizers gains the deferral § Out of scope
  names: whether `Cobham/Tree.lean`'s recognizer is redundant beside
  `Cobham/RankedTree.lean`'s, with `isTree_smashFree` and the
  [Strahm2003] Theorem 1(2) corollary as the residue that is not. Without
  this entry the deferral is lost at merge, the spec being transient.
- § Extensions of the tree recognizers gains three further deferrals: a
  sweep-scale cross-check of `Cobham.isTreeSem` against `binRanked.validBool`,
  which § Verification declines to add here, and the `Nat.le_zero.mp` site in
  `Ranked/Preorder.lean` that takes a bound from the single lemma stating it,
  against § Constructive-only Lean code's fourth rule; and whether to adopt
  the `.vale.ini` in the tree with its house-style-contradicting rules
  downgraded or to remove it, per § Out of scope.
- § The Bellantoni-Cook tree recognizer item 6 names `binRanked.Valid`.
- § Binary trees and their preorder encoding item 3 is retired whole. It asks
  what an upstream PR would argue for a second binary tree beside mathlib's
  `BinaryTree` measured differently, whether `size` should be stated through
  a transfer to `numNodes`, and whether the name `size` survives beside
  `numNodes`, `numLeaves` and `height`; its premise is resolving the overlap
  with `Mathlib/Data/Tree/Basic.lean`, and it observes that `Binary.lean` is
  a free filename. Every part rests on `BinTree` existing. What replaces it,
  `RankedAlphabet.Term.size`, is a node count of a term over an arbitrary
  ranked alphabet: it has no adjacency to `numNodes`, `numLeaves` and
  `height`, no transfer to `numNodes` to consider, and no filename or name
  contest with them. The item records that the overlap dissolved with
  `BinTree` rather than re-homing its questions, and the upstream-adjacency
  observation § Orphaned references moves is recorded there as what the
  overlap was. § Binary trees opens by counting its items, and that line goes
  with item 3 — a count over a set the project keeps amending is what
  [docs/rules/markdown-writing.md](../../rules/markdown-writing.md)
  § Prose style bars, so the remaining items are named rather than counted.
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
  rewrite moved inside a case split, and both modules
  route every reading of the deleted predicate's conjunction through
  `valid_iff_ok_and_depth_eq_one`, `BellantoniCook/Tree.lean` at twice as
  many sites as Cobham. The mitigation is compilation plus the
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
- **The import swap enlarges both recognizers' closures.** They reach
  `Data/Tree/Preorder.lean` today, and through it `Data/Tree/Binary.lean` and
  `Mathlib.Data.W.Basic`; after the swap they reach `Ranked/Binary.lean` and
  through it `Ranked/{Basic,Code,Preorder}.lean`, hence
  `Mathlib.Computability.Encoding`, `Mathlib.Algebra.BigOperators.Ring.List`
  and `Mathlib.Algebra.GroupWithZero.Nat`. `Mathlib.Data.Fin.VecNotation` is
  not part of the delta: both recognizers write `![…]` today. This
  repository treats closure growth as
  its principal axiom hazard —
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
  Lean code's first rule warns that a narrow measurement can be the opposite
  of the one that binds, and its sixth that `LawfulBEq (Fin n)` selection is
  closure-dependent — and both recognizers are full of `by decide`
  admissibility discharges and `omega` calls whose axioms follow their
  closure. For `Cobham/Tree.lean` the hazard is discharged rather than
  assessed: the swap is in the working tree and `lake lint` passes over both
  `Geb` and `GebTests` with it in place. `BellantoniCook/Tree.lean` takes the
  same swap and is not yet restated, so its lint is the one still owed, and it
  is owed before the deletion commit rather than at the end of the branch.
- **The `open` brings more than the counter form bare.** `open
  RankedAlphabet.Binary` puts `depth`, `ok`, `binRanked`, `leaf`, `node`,
  `leafSym`, `nodeSym` and the four `code`/`spell` lemmas into both
  recognizers unqualified — and, until the deletion commit, `termEquiv` and
  its companions too. Nothing collides today: neither recognizer's namespace
  declares any of them, and the build confirms it. `leaf` and `node` are the
  plausible future collision in modules whose prose is about leaf and node
  steps. The repair would be to narrow the `open` to an explicit list rather
  than to rename anything.

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
  em-dash that every committed document using one writes that way, a house
  practice no rule states either way, and flagging the filename `TODO.md`;
  `scripts/pre-push.sh` runs `doctoc` and `markdownlint-cli2` and not
  Vale. Adopting that configuration with those rules downgraded, or removing
  it, is its own branch.
- **A sweep-scale cross-check of the recognizer against the scan.**
  § Verification gives the reason it is not added here and § Documentation
  records it in `TODO.md`.
- **The deferrals `TODO.md` records**, among them the placement of the
  choice-free `Nat` residue lemmas, `oneAtOf` and `falseAtOf` duplicating
  `constAtOf`, `predPred` duplicating `predIter 2`, the citation status of
  `BarringtonCorbett1989` and the three succinct-tree references, the
  Bellantoni-Cook port of the scan combinator, the paramorphism, a fold at an
  infinite carrier, and the degree-sequence encoding. One deserves naming
  because this branch comes close to it: whether `combSem` generates an
  equation lemma, whose resolution would correct a docstring in
  `Cobham/Tree.lean` — a module this branch rewrites docstrings in. It is not
  settled here, and the docstring in question is left as it stands. The
  namespace-prefix deferral is not on this list; § Documentation amends it.

## Appendix: what is in the tree, and what is not

Most of this branch is in the working tree, uncommitted, and is what a
reviewer builds rather than reading a copy of. This document is removed
before merge, so it does not transcribe it.

- `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` carries the counter form,
  between `spell_node` and `ofBinTree`, and its module docstring restated for
  it. In source order:

  - `depth`
  - `ok`
  - `buf_scanFinal_eq_nil`
  - `depth_le_length`
  - `valid_iff_ok_and_depth_eq_one`
  - `decide_length_eq_width`
  - `arOf_decodeBits_false`
  - `arOf_decodeBits_true`
  - `scanStep_false_of_live_of_buf_nil`
  - `scanStep_true_of_live_of_buf_nil_of_two_le_depth`
  - `scanStep_true_of_live_of_buf_nil_of_depth_lt_two`
  - `scanStep_of_not_live`
  - `ok_cons_false`
  - `ok_cons_true`
  - `depth_cons_false_of_ok`
  - `depth_cons_true_of_ok_of_two_le_depth`

- `Geb/Mathlib/Computability/Cobham/Tree.lean` carries the import swap, the
  `open`, every statement § The consumers lists for it, and all of its
  docstrings — the module docstring and each declaration docstring naming a
  deleted name. It contains no occurrence of `BinTree` or of the pre-rename
  theorem name.
- `Geb/Mathlib/Computability/Cobham/RankedTree.lean` carries the collapsed
  bridge and its restated docstring.

Not in the tree: the Bellantoni-Cook module and its mirror, both
`Data/Tree/` mirrors, the deletions, `Ranked/{Basic,Preorder}.lean`'s
docstring restatements, and the `docs/index.md` and `TODO.md` edits.

One check cannot be in the tree at all, since it names `BinTree.ok`, which
this branch deletes. It is the computational half of the counter-form
agreement § Where the shape changes proves, in the guarded form that
induction takes. Pasting it into
`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` as that module stands, before
any of this branch's deletions, reproduces it.

```lean
theorem counter_form_agrees :
    (wordsUpTo 8).all (fun w ↦
      (ok w == BinTree.ok w) &&
        (!ok w || (depth w == BinTree.depth w))) = true := by
  set_option maxRecDepth 100000 in decide
```
