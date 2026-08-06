# The preorder encoding of binary trees — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Sources](#sources)
  - [Per-definition classification](#per-definition-classification)
  - [Why mathlib's `DyckWord` is cited and not reused](#why-mathlibs-dyckword-is-cited-and-not-reused)
- [Design](#design)
  - [Alternatives considered](#alternatives-considered)
  - [Placement and file manifest](#placement-and-file-manifest)
  - [The tree](#the-tree)
  - [The encoding](#the-encoding)
  - [The validity predicate](#the-validity-predicate)
  - [The parser](#the-parser)
  - [The theorems](#the-theorems)
  - [Exposure](#exposure)
  - [Reuse](#reuse)
- [Verification evidence](#verification-evidence)
- [Tests](#tests)
- [Documentation](#documentation)
- [Non-goals](#non-goals)
- [Deferred](#deferred)
- [Constraints](#constraints)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

Define in Lean the unlabelled binary tree as a W-type, its preorder
encoding as a bitstring, a fuel-bounded recursive-descent decoding, and
the characterization of the encoding's image by a two-condition validity
predicate.

The consumer is the Bellantoni-Cook tree recognizer, whose spec is
created on the next segment of this branch stack. That recognizer's
correctness is stated against `Valid`, and its corollary — that the
recognizer accepts exactly the spellings of trees — is
`valid_iff_exists_print` composed with the recognizer's own theorem.
Nothing else in the tree consumes this module yet; the justification
under CONTRIBUTING.md § Code is cost is that consumer.

This module mentions nothing from `Geb/Mathlib/Computability/`, and is an
independently shippable PR candidate.

## Sources

The encoding is classical. It is prefix notation, in which a symbol is
followed by exactly as many operands as its arity, applied to the two
unlabelled shapes: the node bit takes two operands and the leaf bit
none. [Knuth1997] is the standard reference for trees and their
traversals and is cited as a pointer to that material.

No claim here rests on the content of any particular section of
[Knuth1997]: no copy was reachable when this spec was written, so the
spec attributes nothing to it beyond being that pointer. The word is
also called a Łukasiewicz word in the enumerative literature; that name
is in common use and is not attributed to a source here.

mathlib carries an adjacent bijection in
`Mathlib/Combinatorics/Enumerative/DyckWord.lean`:
`DyckWord.equivTree : DyckWord ≃ BinaryTree Unit`, computable, with both
round-trips proved (`ofTree_toTree`, `toTree_ofTree`) and the size
measures related (`numNodes_toTree`). Its `DyckWord` structure carries
three fields — `toList`, `count_U_eq_count_D`, and `count_D_le_count_U`
— the last two being the balance and prefix-nonnegativity conditions
that `depth w = 1` and `ok` play the roles of here.

### Per-definition classification

CONTRIBUTING.md § Cite the literature when transcribing requires each
definition to be marked transcription or novel.

| Definition | Classification |
| --- | --- |
| the preorder encoding `print` | novel presentation of a standard object; [Knuth1997] as a general pointer |
| `Shape`, `Direction`, `BinTree`, `leaf`, `node`, `size`, `induction` | novel presentation of a standard object |
| `depth`, `ok`, `Valid` | novel presentation of a standard object; the two conditions correspond to `DyckWord`'s two proof fields |
| `parseStep`, `parseAux`, `parse` | novel |
| every theorem and `@[simp]` computation rule of the two modules | novel |
| the named `def` § Tests calls for | novel |

Nothing here is classified transcription. Prefix notation is standard,
but no source consulted defines this two-symbol encoding of unlabelled
binary trees, and `depth` and `ok` are standard conditions that no source
states in this right-to-left, truncated-subtraction form. mathlib source
is not citable literature.

### Why mathlib's `DyckWord` is cited and not reused

Four independent obstructions, any one of which would force a local
definition:

1. Alphabet. `DyckWord` carries `List DyckStep` over a bespoke
   two-element inductive. The Bellantoni-Cook class computes on
   `List Bool`.
2. Word length. A Dyck word of semilength `n` has `2n` symbols; the
   Polish-prefix word of a tree with `n` internal nodes has `2n + 1`, the
   difference being the trailing leaf symbol. The two are related by a
   bijection that would itself have to be built and proved.
3. Decomposition, and reducibility. `DyckWord.toTree` splits its argument
   through `firstReturn`, `insidePart` and `outsidePart` under
   `termination_by p.semilength`. The recognizer needs a prefix parser
   returning the unconsumed remainder, which mathlib does not provide;
   and well-founded recursion does not reduce in the kernel, so
   assertions closing by `rfl` would be unavailable.
4. Datatype discipline. `BinaryTree` is a self-referential `inductive`.
   Calling mathlib's is permitted, but placing it at the centre of this
   development would put the subject outside the polynomial-functor
   framework that `docs/rules/lean-coding.md` § Recursion and induction
   through recursors exists to maintain.

What is reused is the concept: `Valid` is stated as the same two
conditions `DyckWord` carries as proof fields.

## Design

### Alternatives considered

A tree type indexed by its own spelling. A slice W-type over `List Bool`,
with `Shape = leaf | node (u v : List Bool)` and
`q (node u v) = true :: u ++ v`, so that `print t = w` holds by
construction. Rejected: the gain is one direction of one theorem, and the
cost is transport at every site relating two differently-built indices,
over a `++` that is associative only propositionally. The
Bellantoni-Cook module documents that cost already — its `transport`
exists because a child's index is equal but not definitionally equal to
the prescribed one.

Reusing `Geb/Internal/ConcreteSyntax.lean`'s `Ast 1`. That module carries
the initial algebra of `Fin k + X × X` with `leaf`, `fork`, an induction
principle, and a proved parse/print retraction. It is not on `main`: it
exists only on the unmerged branch `feat/concrete-syntax-design`, change
`prlwmqsqonus`. Two obstructions therefore stand — the module is
unavailable here, and the import rules bar `Geb/Mathlib/` from reaching
`Geb/Internal/` even once it lands. The duplication is deliberate and
tracked: once both are on `main`, `Ast` should be defined from `BinTree`.
§ Deferred records this.

Labelled `k + id²` first. Rejected as the starting point. A `Fin k` label
field forces a phase into the recognizer's scanning state, and the
recognizer's state cannot hold a pair, since two safe bitstrings cannot
be concatenated in the Bellantoni-Cook class. § Deferred records the
labelled variant.

`#guard` assertions rather than theorems closing by `rfl`. Rejected: the
`rfl` form needs neither a `DecidableEq BinTree` instance nor the
`public meta import` that cross-module `#guard` evaluation requires, and
it fails at elaboration rather than at `lake build`. This follows the
Bellantoni-Cook spec's own constraint for the sibling module.

### Placement and file manifest

| File | Contents |
| --- | --- |
| `Geb/Mathlib/Data/Tree.lean` | index; added |
| `Geb/Mathlib/Data/Tree/Binary.lean` | `Shape`, `Direction`, `BinTree`, `leaf`, `node`, `size`, `induction` |
| `Geb/Mathlib/Data/Tree/Preorder.lean` | `print`, the parser, `depth`, `ok`, `Valid`, the theorems |
| `GebTests/Mathlib/Data/Tree.lean` | test index; added |
| `GebTests/Mathlib/Data/Tree/Preorder.lean` | the assertions of § Tests |
| `Geb/Mathlib/Data.lean` | gains `public import Geb.Mathlib.Data.Tree` |
| `GebTests/Mathlib/Data.lean` | gains `import GebTests.Mathlib.Data.Tree` |
| `docs/references.bib` | gains `Knuth1997` |
| `docs/index.md`, `TODO.md` | § Documentation |
| `docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md` | this spec; added, then removed |
| `docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md` | the plan; added, then removed |

Commit order: this spec, then the plan, then the implementation commits,
then the documentation commit, then a final commit removing this spec and
the plan (CONTRIBUTING.md § Concern shape).

The recognizer's spec, plan, and code are created on the next segment
of the stack, above this branch's bookmark, so that merging this branch
puts none of them on `main`'s working tree. The `Hofmann2000` and
`Marion2003` bibliography entries belong to that segment for the same
reason: nothing here cites them.

The namespace is `BinTree` throughout; no index title or docstring
carries the `Geb.Mathlib.` self-prefix, which
`scripts/lint-imports.sh` rejects outside `^import` lines.

`Geb/Mathlib/Data/Tree/Binary.lean` extracts to
`Mathlib/Data/Tree/Binary.lean`, beside mathlib's existing
`Mathlib/Data/Tree/Basic.lean`, which declares `BinaryTree` with
`numNodes`, `numLeaves` and `height`. `BinTree.size` is not any of those:
mathlib's `numNodes` counts internal nodes only (`numNodes nil = 0`),
whereas `size leaf = 1`, so at `BinaryTree Unit` `size` is
`numNodes + numLeaves`, which mathlib's `numLeaves_eq_numNodes_succ`
makes `2 * numNodes + 1`. `size` is the length of `print t`, of which
`size_le_length_print` proves the inequality the parser's fuel bound
needs, and that is the measure this development uses.
`Mathlib/Data/Tree/` holds `Basic.lean`, `Get.lean`, `RBMap.lean` and
`Traversable.lean`, so the target filename is free and
there is no name clash; what an upstream PR would have to argue is the
overlap in subject, a second binary tree beside `BinaryTree` measured
differently. § Deferred item 3 records it.

### The tree

`Shape` has two constructors and derives `DecidableEq`, under
`docs/rules/lean-coding.md` § Structure and typeclass patterns, which
derives the standard classes where applicable. Nothing in this
development consumes it — § Reuse records that the `rfl` test form
removes the `DecidableEq` obligation on `BinTree` — so it is there for a
downstream caller, not for a proof here. `Direction` sends
`leaf` to `Fin 0` and `node` to `Fin 2` — `Fin 0` rather than `Empty` so
that both fibres lie in one family. The name follows the convention of
this repository's polynomial-functor modules, where a shape's fibre is
its `Direction`.

`Direction` is `@[expose]`, and must be: the module system does not
unfold a non-exposed definition, so without it `WType.mk .leaf Fin.elim0`
does not elaborate, `Fin.elim0` failing to check against
`Direction Shape.leaf`. Reducibility is neither given nor needed — no
instance is sought at `Direction`.

`BinTree := WType BinTree.Direction`. `leaf` and `node` are `WType.mk`
wrappers, `size` is a `WType.elim`, and `induction` gives induction in
the two-constructor presentation so that no downstream proof mentions
`WType.rec`.

### The encoding

    print leaf = [false]
    print (node l r) = true :: (print l ++ print r)

Both equations hold by `rfl` and are registered `@[simp]`.

### The validity predicate

`Valid` is stated in the direction a bounded-state automaton scans —
right to left — and with truncated subtraction, so that it is
simultaneously the classical two-condition presentation and a transcript
of what the recognizer computes.

    depth [] = 0
    depth (false :: v) = depth v + 1
    depth (true :: v) = depth v - 1        -- truncated

    ok [] = true
    ok (false :: v) = ok v
    ok (true :: v) = ok v && (2 ≤ depth v)

    Valid w := ok w = true ∧ depth w = 1

`ok` states that every node bit is read at depth at least two, so that
popping two operands is defined. It is strictly stronger than absence of
truncation, and the spec records the separating instance because the
weaker reading is the one the definition suggests: `[true, false]` truncates nowhere,
since `depth [false] = 1` and `1 - 1` is exact, yet fails `ok`.

Stating `Valid` this way places the direction mismatch between the
right-to-left scan and the left-to-right parser on this branch, where the
recursion is over `List`, rather than on the recognizer branch, where
every eliminator sits at a function motive.

### The parser

`parseStep` reads one tree and returns it with the unconsumed remainder;
`parseAux` is `Nat.rec (fun _ ↦ none) fun _ ih ↦ parseStep ih`; `parse`
supplies the input's length as fuel and rejects a non-empty remainder.

The fuel is forced. The second child is parsed from a
remainder the first call computes, which is not a structural subterm, so
Lean's structural recursion does not accept the definition, and
`docs/rules/lean-coding.md` § Recursion and induction through recursors
bars `termination_by`. `size_le_length_print` shows the supplied bound
admits every tree `print` emits.

### The theorems

| Theorem | Statement |
| --- | --- |
| `size_le_length_print` | `t.size ≤ (print t).length` |
| `parseAux_print` | `t.size ≤ f → parseAux f (print t ++ rest) = some (t, rest)` |
| `parse_print` | `parse (print t) = some t` |
| `print_injective` | `Function.Injective print` |
| `depth_print` | `depth (print t ++ rest) = depth rest + 1` |
| `ok_print` | `ok (print t ++ rest) = ok rest` |
| `exists_print_append_of_ok_of_one_le_depth` | `w.length ≤ n → ok w = true → 1 ≤ depth w → ∃ t rest, print t ++ rest = w ∧ depth rest + 1 = depth w ∧ ok rest = true` |
| `eq_nil_of_ok_of_depth_eq_zero` | `ok w = true → depth w = 0 → w = []` |
| `exists_print_of_valid` | `Valid w → ∃ t, print t = w` |
| `valid_print` | `Valid (print t)` |
| `valid_iff_exists_print` | `Valid w ↔ ∃ t, print t = w` |
| `size_leaf`, `size_node` | the two `@[simp]` computation rules for `size` |

`print_injective` is what makes the uniqueness half of `Valid`'s reading
— that a valid word spells one tree, not merely at least one — a
theorem rather than a claim.

### Exposure

Every definition carrying computational content is `@[expose]` inside a
`public section`. Two are not: `Shape`, an `inductive`, and `BinTree`
itself, which is `@[expose] public def` at the top level because a type
cannot be declared inside its own namespace. `Direction` requires
exposure for elaboration, as § The tree records.

### Reuse

`Geb/Mathlib/Data/W/Basic.lean` supplies `WType.elim_mk`,
`WType.elim_unique`, `WType.para` and `WType.instDecidableEq` over
mathlib's `WType`. This development consumes `WType.elim` and
`WType.rec` directly and needs none of the four: `size` and `print` are
plain folds whose computation rules hold by `rfl`, no proof here appeals
to uniqueness, no paramorphism arises, and the `rfl` test form of
§ Alternatives considered removes the `DecidableEq` obligation. The
module is named here so that a later reviewer need not re-derive that
it was considered.

## Verification evidence

Every declaration below was built by `lake build` against the repository
toolchain (v4.33.0-rc2) at its library path, under the repository's
option set, with copyright headers and module docstrings. Zero
diagnostics on both modules. Measured:

- `Geb.Mathlib.Data.Tree.Binary` and `Geb.Mathlib.Data.Tree.Preorder`
  both build clean.
- `print_leaf`, `print_node`, `parseAux_succ`, `depth_nil`,
  `depth_cons_false`, `depth_cons_true`, `ok_nil`, `ok_cons_true` all
  hold by `rfl`. `ok_cons_false` needs `simp [ok]`.
- Every theorem of § The theorems elaborates.
- `#print axioms`, measured over all 36 authored declarations of the two
  modules, gives three groups. Twelve depend on no axiom at all:
  `BinTree`, `Shape`, `Direction`, `Valid`, `leaf`, `depth` with its
  three computation rules, and `ok` with `ok_nil` and `ok_cons_true`.
  Eleven depend on `[propext]`: `node`, `size`, `print`, `parseStep`,
  `parseAux`, `parse` and their `@[simp]` computation rules. Thirteen
  depend on `[propext, Quot.sound]`: `induction`, `ok_cons_false`, and
  the remaining eleven theorems. No declaration depends
  on `Classical.choice`, so no `GebMeta.classicalAllowedModules` entry is
  needed.
- That measurement is taken by importing the modules directly, because
  neither is yet in `Geb`'s import closure; until the index files of
  § Placement exist, `lake lint` does not reach them and Constraint 1 is
  established by this measurement alone.
- The separating instance in § The validity predicate was evaluated:
  `(depth [false], depth [true, false], ok [true, false])` is
  `(1, 0, false)`.

Two recorded properties, each of which cost an iteration:

- `Direction` must be `@[expose]`. Without it, `WType.mk .leaf Fin.elim0`
  fails to elaborate, reporting `the following definitions were not
  unfolded because their definition is not exposed: Direction`. The
  module system, not reducibility, is what blocks it.
- `parseAux_print`'s node case needs `simp only []` between the two child
  rewrites, to reduce the `match` on the `some` the first rewrite
  produced before the second can fire.

`exists_print_append_of_ok_of_one_le_depth` is the branch's longest
proof and its shape is recorded because it is not the direct one. It is
stated with an explicit `ℕ` bound and driven by `Nat.rec`, not by
well-founded recursion on the word: the node case applies the inductive
hypothesis twice, once to a proper suffix and once to a suffix of that,
and both uses are at the same bound, so `Nat.rec` suffices. `omega`
treats `depth (true :: v)` as an opaque atom, so `depth_cons_true` must
be rewritten into the goal before arithmetic.

## Tests

`GebTests/Mathlib/Data/Tree/Preorder.lean`. Each assertion is a
`theorem` closing by `rfl`, following the Bellantoni-Cook test module;
see § Alternatives considered for why not `#guard`.

- `print` of the leaf, of `node leaf leaf`, and of an asymmetric tree of
  two nodes and three leaves, each against a written-out bitstring.
- `parse` inverting each of those.
- `parse` rejecting, one case per mechanism it can fail by: the empty
  word, on which the descent has nothing to read; a truncated word, on
  which a child's descent runs out of input; and a word with trailing
  input, on which the descent succeeds but the remainder is non-empty.
  A word failing `ok` is not a fourth mechanism — `parse` has no counter,
  and such a word reaches it as one of these three.
- `depth` and `ok` on a word failing only `ok` and on a word failing only
  `depth`, so that the two conjuncts of `Valid` are separated.

The last item is the non-vacuity control: without it no assertion would
distinguish the two conjuncts.

`lake shake` reports an import as removable when nothing in the olean
references it, so the test module names a `def` built from the module
under test rather than relying on anonymous assertions alone. That `def`
is novel, and is the only definition this segment ships outside
`Geb/Mathlib/`.

## Documentation

`docs/index.md` gains the module in topological order. `TODO.md` gains
the § Deferred items below. `docs/references.bib` gains `Knuth1997`
(author, title, edition, publisher, year, ISBN).

## Non-goals

- The Bellantoni-Cook recognizer, and any statement about polynomial
  time. That is the next segment of the stack.
- Any connection to mathlib's `DyckWord` or `BinaryTree` beyond the
  citation in § Sources.
- `Repr` or `DecidableEq` instances for `BinTree`. The `rfl` test form
  needs neither.

## Deferred

1. Labelled trees, the initial algebra of `Fin k + X × X`, and the
   corresponding encoding. Requires a decision on the label field's
   spelling, and a recognizer whose scanning state carries a phase.
2. Define `ConcreteSyntax.Ast` from `BinTree` once both are on `main`,
   removing the duplication § Alternatives considered records.
3. Resolve the overlap with `Mathlib/Data/Tree/Basic.lean`: whether a
   second binary tree belongs beside `BinaryTree`, and whether `size`
   should be stated in terms of `BinaryTree.numNodes` through a
   transfer.
4. Relate `print` to `DyckWord.equivTree`, connecting this encoding to
   mathlib's Catalan-number apparatus. Wanted only if a counting result
   is ever needed.

## Constraints

1. No `noncomputable`. `#print axioms` on every declaration lies within
   `{propext, Quot.sound}`, measured monomorphically in the consuming
   closure.
2. No self-referential `inductive` and no self-calling `def`. `BinTree`
   is a `WType`; `parseAux` and
   `exists_print_append_of_ok_of_one_le_depth` recurse by `Nat.rec`;
   every tree recursion is `WType.elim` or `BinTree.induction`.
3. No `induction` tactic. Case analysis on `List` and `Bool` uses
   `match`, which is non-recursive.
4. `Geb/Mathlib/` import rules: only `Mathlib.*`, `Batteries.*` and
   `Geb.Mathlib.*`; the `Geb.Mathlib.` prefix appears only in `import`
   lines, and no namespace, docstring or comment carries it.
5. Every `def`, `structure`, `inductive` and every theorem of public
   interest carries a docstring; each module carries a module docstring
   with the mandated sections.
6. `lake shake` reports no redundant import.
7. Names follow mathlib's conventions: `UpperCamelCase` for `Shape`,
   `Direction`, `BinTree`, `Valid`; `lowerCamelCase` for `leaf`, `node`,
   `size`, `print`, `parse`, `depth`, `ok`; `snake_case` for every
   theorem, with hypotheses named after `_of_` in the order they appear.
