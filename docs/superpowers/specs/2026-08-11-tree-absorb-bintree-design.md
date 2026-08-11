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
`Data/Tree/Preorder.lean` and the two recognizers, while the whole of
`Data/Tree/Ranked/` and `Cobham/{Scan,Cases,RankedTree,Fold}.lean` are
unpushed on the line this branch extends.

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
unchanged up to the equivalence the branch absorbs: each recognizer keeps
every statement it has, four of them restated over `binRanked.Valid` and one
renamed, its existential re-typed from `BinTree` to `binRanked.Term`. Each
form follows from the other exactly through `termEquiv` and
`spell_termEquiv`, which this branch deletes, so after it nothing in the
repository derives one from the other.

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
them. Where a
module gains a `public import` beside a plain one, the `public` group comes
first, separated by a blank line, per
[the workstream record](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md)
§ Facts established by building item 11.

Both recognizers open `RankedAlphabet` and `RankedAlphabet.Binary`, and
write `Binary.depth`, `Binary.ok` and `binRanked` — the alphabet
unqualified, the counter form qualified. Opening only `RankedAlphabet` would
leave the alphabet reachable as `Binary.binRanked` alone, which is the reason
for the second open: `binRanked` is what every statement about the language
names, and it reads better bare. Opening `RankedAlphabet.Binary` also makes
`depth` and `ok` resolvable bare, and nothing prevents that; writing them
qualified is a convention this branch adopts rather than a property the opens
enforce.

## Orphaned references

References to deleted names sit outside the modules being deleted. Each is
restated in this branch.

| Site | What it says | Restatement |
| --- | --- | --- |
| `Ranked/Basic.lean` module docstring | "The unlabelled binary trees of `Data/Tree/Binary.lean` are the terms of the alphabet of one symbol of arity zero and one of arity two." | the same sentence over `RankedAlphabet.Binary`, which is now where those terms live |
| `Ranked/Basic.lean` Implementation notes | "`Term` is `@[expose]`, as `BinTree` is" | the reason stated without the comparison |
| `Ranked/Preorder.lean` module docstring | "`Data/Tree/Preorder.lean` is the case of one symbol of arity zero and one of arity two." | the same, naming `RankedAlphabet.Binary` |
| `Ranked/Binary.lean` module docstring | title, summary, which states the term algebra is equivalent to `BinTree` and the spelling is `BinTree.print`, `## Main definitions` (`termEquiv`), `## Main statements` (`spell_termEquiv`, `valid_iff`), `## Tags` ("equivalence") | restated in full: the module's subject after this branch is the two-symbol alphabet and the counter form of its scan, not an equivalence |
| `Cobham/RankedTree.lean`, `isRankedSem_binRanked_eq_singleton_iff_isTreeSem`'s docstring | "neither `binRanked`'s `width` and `maxArity` nor the two scans' differing failure conventions need reconciling" | false once one scan remains; restated as the two recognizers deciding one predicate |
| `Cobham/Tree.lean`, `isTree_smashFree`'s docstring | "the decision of `BinTree.Valid` is computable simultaneously in polynomial time and linear space" | restated over `binRanked.Valid`. This is a declaration docstring, not the module's, and it carries the [Strahm2003] Theorem 1(2) attribution § Out of scope treats as the residue justifying the module's survival, so the restatement is load-bearing |
| `Cobham/Tree.lean` Implementation notes, and its smash-free paragraph | name `BinTree.depth_le_length` and `BinTree.Valid` | restated over the counter form and the alphabet's language |
| `GebTests/…/Ranked/Basic.lean`, `length_wordsUpTo_eight`'s docstring | "The enumeration the `Preorder` and `Binary` mirrors sweep" | both named mirrors stop sweeping at that length — one is deleted, the other's sweep is retired — while `GebTests/…/Ranked/Preorder.lean` still sweeps there; the docstring names that mirror instead |
| `docs/index.md`, `Ranked/Preorder.lean` entry | "generalising `Geb/Mathlib/Data/Tree/Preorder.lean` from two unlabelled shapes to any ranked alphabet" | the generalization stated without the deleted module |
| `docs/index.md`, `Cobham/RankedTree.lean` entry | describes the bridge theorem as identifying two languages | restated as the collapsed composition § The consumers gives |
| `TODO.md` § The Bellantoni-Cook tree recognizer item 6 | "any statement relating `BinTree.Valid` to that predicate" | `binRanked.Valid` |
| `TODO.md` § Extensions of the tree recognizers, B1's done-entry | "`RankedAlphabet.Binary.termEquiv` exhibiting `BinTree` as the two-symbol instance with `spell_termEquiv` and `valid_iff`" | B1's deliverable restated as the alphabet and its scan, the equivalence having been absorbed |

Three pieces of persistent documentation, as against names, exist only in the
deleted modules. Deleting them would lose content the ranked development does
not carry, so each moves rather than dying.

- **The `DyckWord` comparison** (`Data/Tree/Preorder.lean`, echoed in
  `docs/index.md`): validity is stated as two conditions in the manner of
  mathlib's `DyckWord`, whose `count_U_eq_count_D` and `count_D_le_count_U`
  play the roles the depth and the underflow verdict play here. That is the
  record of an adjacent mathlib abstraction deliberately not reused, which
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost asks a module to
  keep. `Ranked/Preorder.lean` does not mention `DyckWord`; the comparison
  moves to its module docstring, generalized to the pending count and the
  liveness flag. `docs/index.md` echoes it inside the entry for the deleted
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
- **`size`'s upstream adjacency** (`Data/Tree/Binary.lean`): that extracted
  upstream it would sit beside `BinaryTree.numNodes`, `numLeaves` and
  `height` and is none of the three. The observation now concerns
  `RankedAlphabet.Term.size`; § Documentation records where it lands in
  `TODO.md`.

## What `Ranked/Binary.lean` gains

The counter form of the validity scan at width one, as two projections and
their rewrite rules. The projections are `depth` and `ok`; the facts about
the whole scan (`buf_scanFinal_eq_nil`, `depth_le_length`,
`valid_iff_ok_and_depth_eq_one`) and the `cons`-lemmas at `nil`, `false ::`
and `true ::` rest on general theorems already in
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`; the `decide` lemmas
(`decide_length_eq_width`, `arOf_decodeBits_false`, `arOf_decodeBits_true`)
rest on `Ranked/Code.lean` and kernel evaluation; and the `scanStep` lemmas
are that module's `scanStep` unfolded at width one. None is a second
recursion over a word.

Every declaration below is compiled. They sit in
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean` in the working tree for the
duration of the spec-and-plan review rounds, so a reviewer can build
them, and they are transcribed in full under § Appendix. They become the
branch's first implementation commit.

`lake build` passes and `lake lint` passes over the `Geb` umbrella's import
closure, which is the scope the axiom linter itself runs over, so every
declaration below
measures within the permitted `{propext, Quot.sound}` rather than a chosen
few of them measuring it narrowly.
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
Lean code's first rule asks for the measurement to be taken in the closure
of the module that will consume the declarations; that closure is complete
only once the two recognizers import them, so `lake lint` is run again at
the end of the branch and the measurement here is the one available before
the consumers are restated.

| Declaration | Statement | Provenance |
| --- | --- | --- |
| `depth (w : List Bool) : ℕ` | `(binRanked.scanFinal w).depth` | projection |
| `ok (w : List Bool) : Bool` | `(binRanked.scanFinal w).live` | projection |
| `depth_nil` | `depth [] = 0` | `rfl`; carries both recognizers' base case, which the deleted `depth_nil` carried |
| `ok_nil` | `ok [] = true` | `rfl`; likewise |
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
single lemma that states it. `ok_cons_true` takes its two-way split from
`Nat.lt_or_ge`, which is case analysis rather than a bound taken from a
lemma, and so is the rule's other permitted route.

`Ranked/Preorder.lean` reaches `List.eq_nil_of_length_eq_zero` at three
sites by routes other than this one, one of them `Nat.le_zero.mp` — which is
the single lemma stating its bound, and so is the thing the fourth rule bars.
That predates this branch and is not fixed here; § Documentation records it
in `TODO.md` instead.

`depth_nil`, `ok_nil`, `ok_cons_false` and `ok_cons_true` carry `@[simp]`,
as the four unconditional lemmas they replace did. The two depth
`cons`-lemmas do not, and the reason is not that a conditional simp rule
misbehaves — one whose hypothesis
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
  § Facts established by building item 12 states; `ok_cons_true` and
  `depth_cons_true_of_ok_of_two_le_depth` each need a `dsimp only` after
  the step rewrite.
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
`cons`-lemmas are unconditional, and are the old ones verbatim, as are
`ok_nil` and `depth_nil`.

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

The base case is the second site that changes, and it changes by nothing.
Both proofs are `refine List.rec (motive := …) rfl ?_ w`, and that `rfl`
closed because the deleted `depth` and `ok` were `List.rec`s that
iota-reduce at `[]`. The replacements are projections of a `foldr`, so the
base case is carried by `depth_nil` and `ok_nil` instead; both are `rfl`,
compiled, so the `refine`'s base argument stands unchanged.

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
`depth v - 1` agree wherever `2 ≤ depth v` — which is the conjunct of
`ok (true :: v)`, not of `ok v`: at `v = [false]`, `ok v` holds and
`1 - 2 + 1` is `1` while `1 - 1` is `0`. Where `ok` fails the two diverge,
the deleted counter continuing to subtract while the scan freezes.

That conjunction was also checked by computation, over every word of length
at most eight, in the guarded form the induction takes. The check cannot
land: it names `BinTree.ok`, which this branch deletes. It is reproducible
from § Appendix, which carries it.

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

`Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — the same four
statements bar the depth bound, and it reads the conjuncts at more places
than Cobham does: `⟨h, hd⟩`, `rintro ⟨-, hd'⟩` and `rintro ⟨h', -⟩` in
`isTreeSem_eq_singleton_iff_valid`, and `if_pos ⟨h, hd⟩` with the
projections `hv.2` and `hv.1` in `isTreeSem_eq_ite`. `binRanked.Valid` is
a `Bool` equation rather than a conjunction, so every one of them goes
through `valid_iff_ok_and_depth_eq_one`. Its `combSem_eq` changes as
Cobham's does.

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
in `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` unless the row says
otherwise.

| Declarations | Disposition |
| --- | --- |
| `preorderSample` | redefined at `binRanked.Term` as `node (node leaf leaf) leaf`, merging with the `binarySample` that mirror already declares |
| `print_leaf_eq`, `print_node_leaf_leaf_eq`, `print_preorderSample_eq` | restated over `binRanked.spell`, by `decide` rather than `rfl`: `Nat.land`, which `code` runs through, is not exposed, so a block does not reduce during elaboration while the kernel evaluates it — the reason `Ranked/Binary.lean`'s own `code_leafSym` is `by decide` |
| `parse_print_leaf`, `parse_print_node_leaf_leaf`, `parse_print_preorderSample` | restated over `binRanked.parse`, by `decide`, in the form `(binRanked.parse w).map binRanked.spell = some w` that `GebTests/…/Ranked/Preorder.lean` already uses for its two descent assertions |
| `parse_nil`, `parse_truncated`, `parse_trailing` | restated over `binRanked.parse`, by `decide`. These are the descent's three rejection mechanisms — empty input, a child's failure, trailing input. `GebTests/…/Ranked/Preorder.lean` asserts two descent values and sweeps `validBool` against `isSome parse`, but exhibits no rejection value, so these are restated rather than dropped |
| `depth_node_at_depth_one`, `ok_node_at_depth_one`, `depth_two_leaves`, `ok_two_leaves` | restated over `Binary.depth` and `Binary.ok`. These are the words separating validity's two conjuncts in both directions, and both survive the counter change: at `[false, true, false]` the scan reads `false` to depth one, then fails on `true` at depth one and freezes there, giving `depth = 1` and `ok = false`; at `[false, false]`, `depth = 2` and `ok = true` |
| `valid_print_preorderSample`, `not_valid_two_leaves` | restated over `binRanked.Valid`, both changing shape: the first was `⟨rfl, rfl⟩` against a conjunction and the second `fun h ↦ absurd h.2 (by decide)`, and the predicate is now a `Bool` equation, so each becomes a `decide` |
| `depth_le_length_nil`, `depth_le_length_leaves`, `depth_le_length_mixed` | all three restated over `Binary.depth_le_length`, at the empty word, at leaf bits only, and at a mixed word |
| `decide_valid_leaf`, `decide_not_valid_two_leaves` | restated against the `DecidablePred binRanked.Valid` instance |

`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` is restated in full rather
than extended: `binarySample`'s type is deleted, so it is redefined at
`binRanked.Term`; `spell_termEquiv_binarySample` names `termEquiv` and
becomes `spell_binarySample`; `print_binarySample` is the other half of an
agreement statement and goes; the sweep is replaced below; the
`GebTests.Mathlib.Data.Tree.Ranked.Basic` import goes with it, per
§ Imports; and the module docstring's title, summary, `## Main definitions`,
`## Main statements` and `## Tags` all describe the equivalence and are
rewritten.

The sweep in that mirror comparing `binRanked.validBool` against
`decide (BinTree.Valid w)` loses its subject, both sides becoming one
function once the two developments are one, and is deleted with nothing put
in its place.

Nothing replaces it because nothing needs to. What the deleted sweep gave
that the worked words do not is a check that the recognizer and the scan
still agree when computed rather than proved — that `decide` reduces each to
what its proofs are about, so that an `@[expose]` regression or a
definitional drift fails a test rather than passing silently. A literal value
assertion does that strictly better than an agreement assertion: `isTreeSem
![w] = [true]` fails if that side's reduction drifts, while an agreement can
hold with both sides wrong, and a pair of literal assertions at one word
implies the agreement at that word. The check is therefore bought by pinning
both routes at shared words, which this branch does anyway.

It holds at three words, one accepting and two rejecting. Nothing here is a
new assertion; the requirement is only that the two sets of worked words
continue to meet, which the restatements above must preserve.

| Word | `isTreeSem` pinned in `GebTests/…/Cobham/Tree.lean` | the scan pinned in `GebTests/…/Ranked/Binary.lean` |
| --- | --- | --- |
| `[false]` | `isTreeSem_leaf`, `= [true]`, by `rfl` | `decide (binRanked.Valid [false]) = true`, restated from `decide_valid_leaf` |
| `[false, true, false]` | `isTreeSem_underflow`, `= []`, by `rfl` | `Binary.depth = 1` and `Binary.ok = false`, restated from `depth_node_at_depth_one` and `ok_node_at_depth_one` |
| `[false, false]` | `isTreeSem_wrong_depth`, `= []`, by `rfl` | `Binary.depth = 2`, `Binary.ok = true`, and `¬ binRanked.Valid`, restated from `depth_two_leaves`, `ok_two_leaves` and `not_valid_two_leaves` |

Each is kernel-evaluated, by `rfl` on the recognizer side and `decide` on the
scan side, so a drift in either route's reduction fails one of them. The
scan keeps its own sweep-scale assertion independently: `GebTests/…/Ranked/
Preorder.lean` sweeps `validBool` against `isSome parse` over every word of
length at most eight, and that sweep is untouched by this branch.

`GebTests/Mathlib/Computability/Cobham/Tree.lean` is therefore not edited at
all, and needs no new import, no `open` and no docstring change. A
sweep-scale cross-check of the recognizer against the scan is recorded in
`TODO.md` as its own branch, for whoever wants one; it is not this branch's
concern, and the argument for adding it here did not survive stating what it
would be evidence for.

## Documentation

`docs/index.md` loses its entries for the two deleted modules, has its
`Ranked/Binary.lean`, `Cobham/Tree.lean`, `BellantoniCook/Tree.lean` and
`Cobham/RankedTree.lean` entries restated, and has the reference to the
deleted module removed from its `Ranked/Preorder.lean` entry.

`Geb/Mathlib/Data/Tree.lean` and `GebTests/Mathlib/Data/Tree.lean` are each
left re-exporting one module, itself an index. They stay: the
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
- § Extensions of the tree recognizers gains two further deferrals: a
  sweep-scale cross-check of `Cobham.isTreeSem` against `binRanked.validBool`,
  which § Verification declines to add here, and the `Nat.le_zero.mp` site in
  `Ranked/Preorder.lean` that takes a bound from the single lemma stating it,
  against § Constructive-only Lean code's fourth rule.
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
  overlap was.
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
  em-dash that this repository's committed documents use for delineation,
  as [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Style and references
  prescribes, and flagging the filename `TODO.md`;
  `scripts/pre-push.sh` runs `doctoc` and `markdownlint-cli2` and not
  Vale. Adopting that configuration with those rules downgraded, or removing
  it, is its own branch.
- **A sweep-scale cross-check of the recognizer against the scan.**
  § Verification gives the reason it is not added here and § Documentation
  records it in `TODO.md`.
- **The remaining deferrals `TODO.md` records** — the placement of the
  choice-free `Nat` residue lemmas, `oneAtOf` and `falseAtOf`
  duplicating `constAtOf`, and the citation status of
  `BarringtonCorbett1989` — none of which this branch touches. The
  namespace-prefix deferral is not among them; § Documentation amends it.

## Appendix: what is in the tree, and what is not

The declarations this document specifies are in
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean` in the working tree,
uncommitted, between `spell_node` and `ofBinTree`, and become the branch's
first implementation commit. They are not transcribed here: the file is the
artifact, a reviewer builds it rather than reading a copy, and this document
is removed before merge. In source order:

- `depth`
- `ok`
- `depth_nil`
- `ok_nil`
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

One check is not in the tree, and cannot be: it names `BinTree.ok`, which
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
