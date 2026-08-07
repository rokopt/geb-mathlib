# The preorder encoding of binary trees — implementation plan

> For agentic workers: this plan is executed task-by-task under
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans`. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Complete the first segment of the branch stack — the unlabelled
binary tree, its preorder encoding, the fuel-bounded parser and the
`Valid` characterization — so that `feat/binary-tree-preorder` is an
independently shippable PR candidate carrying nothing of the
Bellantoni-Cook segment.

**Architecture:** The two library modules already exist and build. What
remains is everything around them: the directory index that puts them in
`Geb`'s import closure, the test modules, the persistent documentation,
and the branch-shape repair that puts this plan's commit between the spec
commit and the implementation commit.

**Tech Stack:** Lean 4 (toolchain v4.33.0-rc2), mathlib, `jj` for version
control, `doctoc` and `markdownlint-cli2` for Markdown.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [How a task makes its commit](#how-a-task-makes-its-commit)
- [Commit sequence](#commit-sequence)
- [File structure](#file-structure)
- [Deltas from the spec](#deltas-from-the-spec)
- [Task 1: Verify the repaired branch shape](#task-1-verify-the-repaired-branch-shape)
- [Task 2: The directory index and the import closure](#task-2-the-directory-index-and-the-import-closure)
- [Task 3: The test modules](#task-3-the-test-modules)
- [Task 4: Documentation](#task-4-documentation)
- [Task 5: The pre-push gate](#task-5-the-pre-push-gate)
- [Task 6: Remove the spec and the plan](#task-6-remove-the-spec-and-the-plan)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Global constraints

Every task's requirements implicitly include these. They are
`docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md`
§ Constraints, plus the repository conventions the spec assumes.

1. No `noncomputable`. `#print axioms` on every declaration lies within
   `{propext, Quot.sound}`, measured monomorphically in the consuming
   closure. `Quot.sound` is permitted, not excluded.
2. No self-referential `inductive` and no self-calling `def`. `BinTree`
   is a `WType`; `parseAux` and
   `exists_print_append_of_ok_of_one_le_depth` recurse by `Nat.rec`;
   every tree recursion is `WType.elim` or `BinTree.induction`.
3. No `induction` tactic. Case analysis on `List` and `Bool` uses
   `match`, which is non-recursive.
4. `Geb/Mathlib/` import rules: only `Mathlib.*`, `Batteries.*` and
   `Geb.Mathlib.*`; `GebTests/Mathlib/` additionally `GebTests.Mathlib.*`.
   The `Geb.Mathlib.` and `GebTests.Mathlib.` prefixes appear only in
   `^import` lines — not in a namespace, docstring or comment.
5. Every `def`, `structure`, `inductive` and every theorem of public
   interest carries a docstring; each module carries a module docstring
   with the mandated sections, each present when it has content and
   omitted (never a placeholder) when vacuous.
6. `lake shake` reports no redundant import.
7. Names follow mathlib's conventions: `UpperCamelCase` for `Shape`,
   `Direction`, `BinTree`, `Valid`; `lowerCamelCase` for `leaf`, `node`,
   `size`, `print`, `parse`, `depth`, `ok`; `snake_case` for every
   theorem.
8. No `#guard`; every test assertion is a `theorem` closing by `rfl`.
   The spec's § Alternatives considered records why.
9. Lambda notation uses `↦`, not `=>`, in `fun`. Lines are at most 100
   characters. Indentation is two spaces.
10. All new `.lean` files declare `module` after the copyright block.
    Library modules use `public import` and a `public section`; test
    modules use plain `import` and carry
    `set_option linter.privateModule false`, following the existing
    `GebTests/Mathlib/Computability/BellantoniCook.lean`.
11. Copyright headers take the form used throughout the tree:

    ```lean
    /-
    Copyright (c) 2026 Terence Rokop. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Terence Rokop
    -/
    ```

12. Commit messages follow the repository's Conventional-Commits-shaped
    convention (`feat` / `fix` / `doc` / `style` / `refactor` / `test` /
    `chore` / `perf` / `ci`), imperative present tense, no capital, no
    period, subject at most 72 characters.
13. Version control is `jj`, not `git`: a PreToolUse hook blocks mutating
    `git` subcommands.
14. No push. AGENTS.md § No `jj git push` without user line-by-line
    review.

## How a task makes its commit

`jj` has no staging area. The working copy is itself a commit — the one
`jj log` marks `@` — and jj snapshots edits into it continuously. A file
written now lands in whatever `@` is now. Every task below therefore
begins by creating its change and only then edits files:

```bash
jj new --insert-after <the previous task's change id> -m "<message>"
```

`jj new --insert-after X` creates a new change between `X` and `X`'s
children, rebases those children onto it, and — without `--no-edit` —
checks it out, so `@` becomes the new change. That is what keeps this
segment's commits below the `feat/bc-tree-recognizer` segment instead of
on top of the whole stack.

Do not use `jj commit` here. It describes `@` and creates a child of it,
which is the right shape only when `@` is already the head of the stack;
in this segment `@` is in the middle, so the new child would be a second
head beside the segment-2 commits rather than a continuation.

The working copy always materialises `@`'s tree alone. Commits above `@`
contribute nothing to it, so while these tasks run, the segment-2 spec,
plan and measured-Lean files are absent from the working tree. That is
expected, not a sign of a broken stack.

## Commit sequence

`CONTRIBUTING.md` § Concern shape orders a topic branch spec → plan →
implementation → removal. The stack already has the first three commits
in that order; Tasks 2, 3, 4 and 6 add the rest, each between the
segment-1 head and the segment-2 spec commit. Task 5 adds no commit.

Target state at the end of this plan:

```text
doc: add the preorder-encoding design spec
doc: add the preorder-encoding implementation plan
feat(tree): add the binary tree and its preorder encoding
feat(tree): index the tree modules under Geb.Mathlib.Data
test(tree): assert the encoding, the parser and the validity conjuncts
doc: record the tree modules and their follow-on work
doc: remove the preorder-encoding spec and plan          ← feat/binary-tree-preorder
```

The bookmark presently sits on the implementation commit and moves to the
removal commit in Task 6.

The `feat/bc-tree-recognizer` segment sits above that removal commit and
is the subject of a separate plan. Nothing this plan writes may reach the
segment-2 commits, and nothing of segment 2 may reach this branch.
Merging `feat/binary-tree-preorder` would put on `main` the ten paths
Task 6 Step 6 enumerates — the two library modules, the two new index
files, the one new test module, the two index files it edits,
`docs/references.bib`'s `Knuth1997` entry, `docs/index.md` and `TODO.md`
— and no path under `docs/superpowers/`, since Task 6 removes the spec
and this plan.

## File structure

| Path | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/Tree/Binary.lean` | exists; `Shape`, `Direction`, `BinTree`, `leaf`, `node`, `size`, `induction` |
| `Geb/Mathlib/Data/Tree/Preorder.lean` | exists; `print`, the parser, `depth`, `ok`, `Valid`, the theorems |
| `Geb/Mathlib/Data/Tree.lean` | new; directory index over the two above |
| `Geb/Mathlib/Data.lean` | gains one `public import` |
| `GebTests/Mathlib/Data/Tree/Preorder.lean` | new; the thirteen assertions |
| `GebTests/Mathlib/Data/Tree.lean` | new; test directory index |
| `GebTests/Mathlib/Data.lean` | gains one `import` |
| `docs/index.md` | two bullets |
| `TODO.md` | one `###` subsection carrying the spec's § Deferred |
| `docs/references.bib` | already carries `Knuth1997`; untouched here |
| `docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md` | exists; removed in Task 6 |
| `docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md` | this plan; removed in Task 6 |

There is no `GebTests/Mathlib/Data/Tree/Binary.lean`. `Binary.lean`
declares two `@[simp]` computation rules that hold by `rfl` and an
induction principle; the spec's § Tests asks for assertions about the
encoding, and every one of them exercises `Binary.lean` through `print`.

## Deltas from the spec

One, and it was applied to the spec rather than carried here: the spec's
§ Placement and file manifest said `GebTests/Mathlib/Data.lean` gains a
`public import`. Every line of that file is a plain `import`, as in every
other `GebTests` index, so the spec's row was corrected to `import` in
the spec's own commit. Nothing else in this plan departs from the spec.

---

## Task 1: Verify the repaired branch shape

**Files:**

- Modify: none (version-control inspection only)

**Interfaces:**

- Consumes: nothing
- Produces: evidence that the branch order is spec → plan →
  implementation, so that Tasks 2-6 append to a well-formed stack

The two library modules were written during the brainstorming phase, to
produce the spec's § Verification evidence, and were committed before this
plan existed. That inverts `CONTRIBUTING.md` § Concern shape. The plan
commit has been inserted between the spec commit and the implementation
commit; this task confirms it.

- [ ] **Step 1: Print the stack**

```bash
jj log -r 'main::feat/bc-tree-recognizer' --no-pager \
  -T 'change_id.short() ++ "  " ++ bookmarks ++ "  " ++ description.first_line() ++ "\n"'
```

Expected, reading bottom to top: `main`, then

```text
                             doc: add the preorder-encoding design spec
                             doc: add the preorder-encoding implementation plan
feat/binary-tree-preorder    feat(tree): add the binary tree and its preorder encoding
                             doc: add the tree-recognizer design spec
feat/bc-tree-recognizer      doc: add the tree-recognizer implementation plan
```

(change ids elided; the template prints them first, then the bookmark,
then the description.)

Record the five change ids. Task 2 names the implementation commit's;
Tasks 3, 4 and 6 name the change ids of commits that do not exist yet,
each created by the preceding task.

If the plan commit is absent or sits above the implementation commit,
repair it before continuing:

```bash
jj new --insert-after <spec-1 change id> --no-edit \
  -m "doc: add the preorder-encoding implementation plan"
jj squash --use-destination-message \
  --from <change holding the plan file> --into <the new change> \
  docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md
```

`--use-destination-message` matters: moving the plan file out empties the
source change, jj abandons it, and with two non-empty descriptions it
would otherwise prompt for a combined one and stall a non-interactive
run.

- [ ] **Step 2: Confirm each of the three lower commits carries only its own files**

```bash
jj diff --stat -r <spec-1 change id>
jj diff --stat -r <plan-1 change id>
jj diff --stat -r <impl change id>
```

Expected: the spec commit touches
`docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md` and
`docs/references.bib`; the plan commit touches only
`docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md`; the
implementation commit touches only `Geb/Mathlib/Data/Tree/Binary.lean`
and `Geb/Mathlib/Data/Tree/Preorder.lean`.

- [ ] **Step 3: Confirm the two modules still build**

Run: `lake build Geb.Mathlib.Data.Tree.Preorder`
Expected: exit 0, no diagnostics. `Preorder.lean` publicly imports
`Binary.lean`, so this builds both.

---

## Task 2: The directory index and the import closure

**Files:**

- Create: `Geb/Mathlib/Data/Tree.lean`
- Modify: `Geb/Mathlib/Data.lean`

**Interfaces:**

- Consumes: `Geb.Mathlib.Data.Tree.Binary` and
  `Geb.Mathlib.Data.Tree.Preorder`, both already on the branch
- Produces: `Geb.Mathlib.Data.Tree`, and the property that both modules
  lie in `Geb`'s import closure, so that `lake lint` — and with it
  `GebMeta.detectNonstandardAxiom` — reaches them

`Tree/` is the only subdirectory of `Geb/Mathlib/Data/` with no sibling
index, which `CONTRIBUTING.md` § Repo structure requires ("one indexing
file per directory"). The consequence beyond tidiness is the axiom
linter: until this task lands, neither module is reachable from `Geb`, so
`lake lint` never sees them and Constraint 1 rests on the direct
`#print axioms` measurement recorded in the spec alone.

- [ ] **Step 1: Create the change**

```bash
jj new --insert-after <impl change id> \
  -m "feat(tree): index the tree modules under Geb.Mathlib.Data"
```

Confirm the new change is checked out and sits where intended:

```bash
jj log -r 'main::feat/bc-tree-recognizer' --no-pager \
  -T 'change_id.short() ++ "  " ++ description.first_line() ++ "\n"'
```

Expected: `@` marks the new change, immediately above the implementation
commit and immediately below the segment-2 spec commit. `jj log -r @`
alone would not show this: it prints one commit and its elided parents,
never its children.

- [ ] **Step 2: Create the directory index**

Create `Geb/Mathlib/Data/Tree.lean`, following
`Geb/Mathlib/Data/Vector.lean`'s form — every sibling listed, in
alphabetical order:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Tree.Binary
public import Geb.Mathlib.Data.Tree.Preorder

/-!
# Tree — index
-/
```

- [ ] **Step 3: Add the import to the `Data` index**

In `Geb/Mathlib/Data.lean`, insert between the `PFunctor` and
`UnionFind` lines, keeping the list alphabetical:

```lean
public import Geb.Mathlib.Data.Tree
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: exit 0, no diagnostics. A failure here means the module was
never in the closure and something it relies on is unavailable when
`Geb` is built as a whole.

- [ ] **Step 5: Run the axiom linter over the newly reachable modules**

Run: `lake lint`
Expected: exit 0. `GebMeta.detectNonstandardAxiom` now reaches both
modules — the 36 authored declarations and the auto-generated ones
alongside them — the recursors, eliminators and `noConfusion` family of
`BinTree.Shape`, the `deriving DecidableEq` instance and its `_proof_`
companions, the equation lemmas of `ok`, `parseStep` and `parse`, and the
match auxiliaries. A failure names any declaration whose axioms leave
`{propext, Quot.sound}`.

- [ ] **Step 6: Re-measure the axiom groups**

The spec's § Verification evidence records three groups over the 36
authored declarations, measured before the modules were in the closure.
Task 4 writes those groups into `docs/index.md`, so re-take them here
rather than copying the spec. Use the `lean-lsp` MCP's `lean_run_code`
with a snippet that imports `Geb.Mathlib.Data.Tree` and runs
`#print axioms` on each of the 36 names. (`lean_run_code` needs the
project path initialised: call `lean_diagnostic_messages` on an existing
`.lean` file once before the first `lean_run_code` call. A file written
outside the lake package cannot resolve `Geb.*` imports, so a throwaway
module under a temporary directory is not an alternative.)

Expected, from the spec's own measurement — treat a disagreement as a
finding, not as a reason to adjust the expectation:

- no axiom: `BinTree`, `Shape`, `Direction`, `Valid`, `leaf`, `depth`,
  `depth_nil`, `depth_cons_false`, `depth_cons_true`, `ok`, `ok_nil`,
  `ok_cons_true` — twelve.
- `[propext]`: `node`, `size`, `size_leaf`, `size_node`, `print`,
  `print_leaf`, `print_node`, `parseStep`, `parseAux`, `parseAux_succ`,
  `parse` — eleven.
- `[propext, Quot.sound]`: `induction`, `ok_cons_false` and the eleven
  theorems of the spec's § The theorems other than `size_leaf` and
  `size_node` — thirteen.

`ok_cons_false` sits in the third group and not with `ok`'s other two
computation rules because it is proved by `simp [ok]` rather than by
`rfl`. Record the measured lists; Task 4 consumes them.

- [ ] **Step 7: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: two paths, `Geb/Mathlib/Data/Tree.lean` added and
`Geb/Mathlib/Data.lean` modified.

---

## Task 3: The test modules

**Files:**

- Create: `GebTests/Mathlib/Data/Tree/Preorder.lean`
- Create: `GebTests/Mathlib/Data/Tree.lean`
- Modify: `GebTests/Mathlib/Data.lean`

**Interfaces:**

- Consumes: `BinTree.leaf`, `BinTree.node`, `BinTree.print`,
  `BinTree.parse`, `BinTree.depth`, `BinTree.ok` from
  `Geb.Mathlib.Data.Tree.Preorder`
- Produces: `preorderSample : BinTree`, the asymmetric tree the
  assertions are stated at, and thirteen theorems

Every assertion below was measured by `rfl` against the modules as
committed, at toolchain v4.33.0-rc2. `parse` rejects for three distinct
reasons and the spec's § Tests asks for one word per reason; a word
failing `ok` is not a fourth reason, since `parse` has no counter and
reaches such a word as one of the three.

The first two `print` assertions restate the library's own `@[simp]`
lemmas `print_leaf` and `print_node` at closed arguments. The spec's
§ Tests asks for them, and they hold the two computation rules to
written-out bitstrings, so a change to either lemma's right-hand side
fails here rather than silently changing the encoding.

- [ ] **Step 1: Create the change**

```bash
jj new --insert-after <Task 2's change id> \
  -m "test(tree): assert the encoding, the parser and the validity conjuncts"
```

- [ ] **Step 2: Write the test module**

Create `GebTests/Mathlib/Data/Tree/Preorder.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Preorder

/-!
# The preorder encoding on worked trees

The encoding and its parser on the leaf, on the two-leaf node and on an
asymmetric tree; the parser's three rejection mechanisms; and `depth` and
`ok` on words separating the two conjuncts of `Valid`.

## Main statements

The thirteen assertions below.

## Tags

binary tree, preorder, prefix notation, encoding
-/

set_option linter.privateModule false

open BinTree

/-- The asymmetric tree the assertions below are stated at: a node whose
left child is a two-leaf node and whose right child is a leaf. Its `size`
is five, counting leaves alongside internal nodes. -/
def preorderSample : BinTree := node (node leaf leaf) leaf

/-- A leaf is spelled by one `false` bit. -/
theorem print_leaf_eq : print leaf = [false] := rfl

/-- A node is spelled by a `true` bit and its children's spellings. -/
theorem print_node_leaf_leaf_eq :
    print (node leaf leaf) = [true, false, false] := rfl

/-- The asymmetric tree's spelling, which no symmetric tree has. -/
theorem print_preorderSample_eq :
    print preorderSample = [true, true, false, false, false] := rfl

/-- The parser inverts the printer on the leaf. -/
theorem parse_print_leaf : parse [false] = some leaf := rfl

/-- The parser inverts the printer on the two-leaf node. -/
theorem parse_print_node_leaf_leaf :
    parse [true, false, false] = some (node leaf leaf) := rfl

/-- The parser inverts the printer on the asymmetric tree. -/
theorem parse_print_preorderSample :
    parse [true, true, false, false, false] = some preorderSample := rfl

/-- The parser rejects the empty word: the descent has nothing to read. -/
theorem parse_nil : parse ([] : List Bool) = none := rfl

/-- The parser rejects a truncated word: the second child's descent runs
out of input. -/
theorem parse_truncated : parse [true, false] = none := rfl

/-- The parser rejects trailing input: the descent succeeds and leaves a
non-empty remainder. -/
theorem parse_trailing : parse [false, false] = none := rfl

/-- A word failing `ok` alone: its depth is one, yet it reads a node bit
at depth one. -/
theorem depth_node_at_depth_one : depth [false, true, false] = 1 := rfl

/-- The `ok` half of that word. -/
theorem ok_node_at_depth_one : ok [false, true, false] = false := rfl

/-- A word failing the depth conjunct alone: two leaves and no node leave
two trees on the stack. -/
theorem depth_two_leaves : depth [false, false] = 2 := rfl

/-- The `ok` half of that word. Together with the two above, the
conjuncts of `Valid` are separated in both directions. -/
theorem ok_two_leaves : ok [false, false] = true := rfl
```

- [ ] **Step 3: Write the test directory index**

Create `GebTests/Mathlib/Data/Tree.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.Tree.Preorder

/-!
# Tree tests — index
-/
```

- [ ] **Step 4: Add the import to the `Data` test index**

In `GebTests/Mathlib/Data.lean`, insert between the `PFunctor` and
`UnionFind` lines:

```lean
import GebTests.Mathlib.Data.Tree
```

- [ ] **Step 5: Build the tests**

Run: `lake build GebTests`
Expected: exit 0, no diagnostics. Any `rfl` that fails is a measurement
disagreement: report the computed value rather than adjusting the
assertion to whatever elaborates.

- [ ] **Step 6: Run the test target and the axiom linter over the tests**

Run: `lake test` then `lake lint -- GebTests`
Expected: exit 0 from each. The test module's declarations are
module-private, so `#print axioms` cannot reach them from another file;
`lake lint -- GebTests` is what holds them to the axiom budget.

- [ ] **Step 7: Confirm `lake shake` does not report the module**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: `GebTests/Mathlib/Data/Tree/Preorder.lean` is absent from the
reported list. The module's thirteen theorem statements reference
`print`, `parse`, `depth` and `ok`, so the import leaves constants in the
olean for `shake` to see; `preorderSample` additionally names `node` and
`leaf`. `shake`'s known blind spot is an anonymous `example`, which this
module does not use.

`lake shake` may print a `PANIC at Option.get!` trace from
`Lake.Shake.visitModule` when the first module under a new
`GebTests/Mathlib/<Dir>/` appears. It exits 0 when that happens. A
non-zero exit is a real failure.

- [ ] **Step 8: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: three paths — the two new test modules added,
`GebTests/Mathlib/Data.lean` modified.

---

## Task 4: Documentation

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: the axiom measurement from Task 2 Step 6
- Produces: the persistent record of what this branch adds, and the
  follow-on work the spec defers

`docs/index.md` lists implemented content in topological order; `TODO.md`
§ Next up holds work not yet started. The spec's § Deferred items land in
`TODO.md` before the removal commit, since that is the only place they
persist once the spec is gone.

- [ ] **Step 1: Create the change**

```bash
jj new --insert-after <Task 3's change id> \
  -m "doc: record the tree modules and their follow-on work"
```

- [ ] **Step 2: Add the two `docs/index.md` bullets**

Add to `docs/index.md` § Implemented content, immediately after the
`Geb/Mathlib/Data/W/Basic.lean` bullet and before the
`Geb/Mathlib/Data/PFunctor/Univariate/` bullet — the two modules depend
on mathlib's `WType` and on nothing else in the repository, so that is
their place in the topological order:

```markdown
- `Geb/Mathlib/Data/Tree/Binary.lean` — unlabelled binary trees as the
  W-type of a two-element shape family: `BinTree.Shape`,
  `BinTree.Direction` (`Fin 0` at a leaf, `Fin 2` at a node),
  `BinTree := WType Direction`, the constructors `leaf` and `node`,
  `size` counting nodes and leaves alike, and `BinTree.induction`, which
  gives induction in the two-constructor presentation so that no
  downstream proof mentions `WType.rec`. `Direction` is `@[expose]`
  because the module system does not unfold a non-exposed definition and
  `WType.mk .leaf Fin.elim0` would not elaborate without it. Depends on
  mathlib's `Mathlib/Data/W/Basic.lean`. `BinTree`, `Shape`, `Direction`
  and `leaf` depend on no axiom; `node`, `size` and the two `@[simp]`
  size rules on `propext`; `induction` on `propext` and `Quot.sound`.
- `Geb/Mathlib/Data/Tree/Preorder.lean` — the preorder encoding of
  binary trees as bitstrings and its inverse. `BinTree.print` spells a
  leaf `[false]` and a node a `true` bit followed by its children;
  `parseStep`, `parseAux` and `parse` are the fuel-bounded
  recursive descent, bounded by an explicit `ℕ` because a child is
  parsed from a remainder the previous call computes;
  `depth` and `ok` are the stack depth read right to left and the
  condition that every node bit is read at depth at least two, and
  `Valid w` is their conjunction with `depth w = 1`. `parse_print` and
  `print_injective` give the retraction and injectivity;
  `valid_iff_exists_print` characterizes the encoding's image, and is
  what the Bellantoni-Cook recognizer's correctness is stated against.
  Cites [Knuth1997] as the standard reference for trees and their
  traversals, and mathlib's `DyckWord` as the adjacent bijection it does
  not reuse. Depends on `Geb.Mathlib.Data.Tree.Binary`.
  `Valid`, `depth` with its three computation rules, and `ok`
  with `ok_nil` and `ok_cons_true` depend on no axiom; `print`, the
  parser and their `@[simp]` rules on `propext`; `ok_cons_false`, which
  is proved by `simp` rather than by `rfl`, and the eleven theorems on
  `propext` and `Quot.sound`.
```

Correct any axiom claim above that Task 2 Step 6 measured differently.

- [ ] **Step 3: Add the `TODO.md` subsection**

Add as the last `###` subsection of `## Next up` in `TODO.md`, after
`### Bellantoni-Cook`, in the form the neighbouring subsections use:

```markdown
### Binary trees and their preorder encoding

Four items over `Geb/Mathlib/Data/Tree/`.

1. Labelled trees, the initial algebra of `Fin k + X × X`, and the
   corresponding encoding. Requires a decision on the label field's
   spelling, and a recognizer whose scanning state carries a phase.
2. Define `ConcreteSyntax.Ast` from `BinTree`, removing the duplication
   between them. `Geb/Internal/ConcreteSyntax.lean` is not on `main`: it
   exists on the unmerged branch `feat/concrete-syntax-design`, where it
   carries the initial algebra of `Fin k + X × X` with its own `leaf`,
   `fork`, induction principle and parse/print retraction. The item
   becomes actionable once that branch lands, the import rules barring
   `Geb/Mathlib/` from reaching `Geb/Internal/` so the dependency runs
   the other way.
3. Resolve the overlap with `Mathlib/Data/Tree/Basic.lean`, which
   declares `BinaryTree` with `numNodes`, `numLeaves` and `height`.
   `Mathlib/Data/Tree/` holds `Basic.lean`, `Get.lean`, `RBMap.lean` and
   `Traversable.lean`, so `Binary.lean` is a free filename and there is
   no name clash; what an upstream PR would have to argue is a second
   binary tree beside `BinaryTree`, measured differently — `BinTree.size`
   counts leaves alongside internal nodes, so at `BinaryTree Unit` it is
   `numNodes + numLeaves`, which `numLeaves_eq_numNodes_succ` makes
   `2 * numNodes + 1`. Whether `size` should instead be stated through a
   transfer to `numNodes` is the second half of the question.
4. Relate `print` to `DyckWord.equivTree`, connecting this encoding to
   mathlib's Catalan-number apparatus. Wanted only if a counting result
   is ever needed.
```

- [ ] **Step 4: Regenerate the tables of contents and lint the Markdown**

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` from `doctoc` and `Summary: 0 issues` from
`markdownlint-cli2`. `TODO.md` carries a doctoc TOC and gains a heading,
so its TOC changes; jj snapshots that change into this commit with the
rest.

- [ ] **Step 5: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: exactly `docs/index.md` and `TODO.md`.

---

## Task 5: The pre-push gate

**Files:**

- Modify: none

**Interfaces:**

- Consumes: everything above
- Produces: evidence that the branch is shippable

This task creates no commit, and needs none. `scripts/pre-push.sh` leaves
no lasting change to a tracked file: its `doctoc` step runs `--dryrun`,
which reports drift and exits non-zero rather than rewriting, and its one
step that does write — `scripts/tests/test-lake-shake.sh`, which injects
an unused import into `Geb/Cslib.lean` to check that `lake shake` still
flags it — restores the file under a trap. Step 3 confirms the
restoration. If a step fails, fix the cause in whichever commit
introduced it — with `jj edit`, or by amending `@` when that is Task 4's
commit — rather than adding a commit here.

- [ ] **Step 1: Run the full checklist**

Run: `scripts/pre-push.sh`
Expected: every step passes and the script exits 0.

The checklist runs, among other steps, `lake exe cache get`,
`lake build`, `lake test`, `lake lint`, `lake build GebTests`,
`lake lint -- GebTests`, `lake shake`, `scripts/lint-imports.sh`, the
repository's script smoke tests, the commit-message check over this
branch's commits, and the `doctoc` and `markdownlint-cli2` checks. It
also emits non-fatal reminders, which do not affect its exit status.
Nothing further need be run separately.

- [ ] **Step 2: Read the commit-message check's input**

The checklist feeds `jj log -r 'fork_point(main | @)..@ ~ merges()'` to
`scripts/check-commit-msg.sh`. `@` sits inside segment 1, so the messages
checked are segment 1's alone, and there are six of them: the spec, this
plan, the implementation, and Tasks 2, 3 and 4. Confirm the printed list
is those six subjects and that each is imperative, uncapitalised,
unpunctuated and at most 72 characters.

- [ ] **Step 3: Confirm the gate left nothing behind**

Run: `jj diff --stat -r @`
Expected: `docs/index.md` and `TODO.md`, exactly as at the end of Task 4.
`Geb/Cslib.lean` appearing here means `scripts/tests/test-lake-shake.sh`
did not restore it; restore it before continuing.

---

## Task 6: Remove the spec and the plan

**Files:**

- Delete: `docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md`
- Delete: `docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md`

**Interfaces:**

- Consumes: nothing
- Produces: a branch whose working tree carries only persistent content,
  and a bookmark on its head

`CONTRIBUTING.md` § Concern shape: specs and plans record how the current
state was reached, not what it is, so they belong in history and not on
an active branch. Both remain reachable in the two commits Task 1
verified.

The segment-2 spec, its plan and its measured-Lean companion are left
alone. They belong to the commits above this one, and the working copy at
`@` does not contain them at all.

- [ ] **Step 1: Create the removal change**

```bash
jj new --insert-after <Task 4's change id> \
  -m "doc: remove the preorder-encoding spec and plan"
```

- [ ] **Step 2: Delete both files**

```bash
rm docs/superpowers/specs/2026-08-06-binary-tree-preorder-design.md
rm docs/superpowers/plans/2026-08-06-binary-tree-preorder-plan.md
```

- [ ] **Step 3: Confirm nothing else changed**

Run: `jj status`
Expected: under `Working copy changes:`, two `D` lines and nothing else.

```bash
ls docs/superpowers/specs docs/superpowers/plans
```

Expected: both directories empty. The segment-2 files are not here: the
working copy materialises `@`'s tree, and `@` sits below the commits that
add them.

- [ ] **Step 4: Re-check the Markdown**

The removal touches no `.lean` file, so only the Markdown steps of Task 5
can be affected.

```bash
doctoc --dryrun --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` and `Summary: 0 issues`.

- [ ] **Step 5: Move the bookmark to this commit**

```bash
jj bookmark set feat/binary-tree-preorder -r @
```

- [ ] **Step 6: Confirm the split between the two segments**

```bash
jj log -r 'main::feat/bc-tree-recognizer' --no-pager \
  -T 'change_id.short() ++ "  " ++ bookmarks ++ "  " ++ description.first_line() ++ "\n"'
jj diff --stat -r 'main..feat/binary-tree-preorder'
```

Expected: `feat/binary-tree-preorder` points at the removal commit, and
the cumulative diff against `main` names exactly ten paths —
`Geb/Mathlib/Data/Tree/Binary.lean`,
`Geb/Mathlib/Data/Tree/Preorder.lean`, `Geb/Mathlib/Data/Tree.lean`,
`Geb/Mathlib/Data.lean`, `GebTests/Mathlib/Data/Tree/Preorder.lean`,
`GebTests/Mathlib/Data/Tree.lean`, `GebTests/Mathlib/Data.lean`,
`docs/references.bib`, `docs/index.md` and `TODO.md` — and nothing under
`docs/superpowers/`.

`docs/references.bib` appears in that diff either way, since segment 1's
spec commit adds `Knuth1997`, so `--stat` cannot say which entries it
carries. Check the content:

```bash
jj file show -r feat/binary-tree-preorder docs/references.bib \
  | grep -q 'Knuth1997' || echo "BIB UNREADABLE"
jj file show -r feat/binary-tree-preorder docs/references.bib \
  | grep -q 'Hofmann2000\|Marion2003' && echo LEAK || echo clean
```

Expected: `clean`, with nothing before it. `LEAK` means those entries
have leaked down from segment 2; move them back up before proceeding.
`BIB UNREADABLE` means the first command failed and the second one's
`clean` is meaningless. (`grep -c` is the wrong instrument for the second
check: it prints `0` and exits 1, so a checker reading the exit status
sees the pass as a failure.)

- [ ] **Step 7: Check this commit's own message**

Task 5's gate ran before this commit existed, so the checklist never saw
its subject. Run the check again over the completed segment:

```bash
jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
  -T 'description.first_line() ++ "\n"' | bash scripts/check-commit-msg.sh
```

Expected: exit 0 over seven subjects.

- [ ] **Step 8: Reach the segment-2 plan**

`@` is now segment 1's removal commit, in the middle of the stack, and
the working copy materialises `@`'s tree alone — so
`docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md` is not on
disk, and neither is the segment-2 spec. To continue with segment 2, put
the working copy on its head:

```bash
jj edit feat/bc-tree-recognizer
ls docs/superpowers/specs docs/superpowers/plans
```

Expected: the segment-2 spec, plan and measured-Lean companion are
present again, and segment 1's spec and plan are not. That plan's Task 1
re-verifies the stack from there.

No push. AGENTS.md § No `jj git push` without user line-by-line review:
every push, including a first creation, waits on the user reading the
diff.
