# The Bellantoni-Cook tree recognizer — implementation plan

> For agentic workers: this plan is executed task-by-task under
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans`. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Define, as expressions of the Bellantoni-Cook class `B`, a
recognizer deciding whether a bitstring is the preorder spelling of a
binary tree, and prove it correct against
`Geb/Mathlib/Data/Tree/Preorder.lean`'s `Valid` — hence, composed with
`valid_iff_exists_print`, against the spellings themselves.

**Architecture:** Four expressions of `B`, built as raw `sig`-trees and
bound as admissible `BC` terms: `count`, a `safeRec` returning the stack
depth in unary; `noUnderflow`, a `safeRec` whose `true`-step guards on
`pred (count v)` recomputed from the normal tail; `eqOne`, two nested
conditionals; and `isTree`, their conjunction. Correctness runs through
per-constructor unfolding lemmas that hold by `rfl`, one
`funext`-based environment-normalization lemma per expression, and two
`List.rec` inductions.

**Tech Stack:** Lean 4 (toolchain v4.33.0-rc2), mathlib,
`Geb.Mathlib.Computability.BellantoniCook`,
`Geb.Mathlib.Data.PFunctor.Slice.Decidable`,
`Geb.Mathlib.Data.Tree.Preorder`, `jj` for version control.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [How a task makes its commit](#how-a-task-makes-its-commit)
- [Commit sequence](#commit-sequence)
- [File structure](#file-structure)
- [Deltas from the spec](#deltas-from-the-spec)
  - [What this plan's measurements changed in the spec](#what-this-plans-measurements-changed-in-the-spec)
  - [Two measurements restated](#two-measurements-restated)
- [The three unfolding devices](#the-three-unfolding-devices)
- [Task 1: Verify the stack and take the working copy to the segment head](#task-1-verify-the-stack-and-take-the-working-copy-to-the-segment-head)
- [Task 2: The directory restructure](#task-2-the-directory-restructure)
- [Task 3: The four expressions](#task-3-the-four-expressions)
- [Task 4: The counter and the underflow test](#task-4-the-counter-and-the-underflow-test)
- [Task 5: The one-test and the recognizer](#task-5-the-one-test-and-the-recognizer)
- [Task 6: The test module](#task-6-the-test-module)
- [Task 7: Documentation](#task-7-documentation)
- [Task 8: The pre-push gate](#task-8-the-pre-push-gate)
- [Task 9: Remove the spec, the plan and the measured Lean](#task-9-remove-the-spec-the-plan-and-the-measured-lean)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Global constraints

Every task's requirements implicitly include these. They are
`docs/superpowers/specs/2026-08-06-bc-tree-recognizer-design.md`
§ Constraints, plus the repository conventions the spec assumes.

1. No `noncomputable`. `#print axioms` on every declaration lies within
   `{propext, Quot.sound}`, measured monomorphically in the consuming
   closure. No `Computability` module is in
   `GebMeta.classicalAllowedModules`, so any `Classical.choice`
   dependence fails `lake lint`.
2. No self-referential `inductive` and no self-calling `def`.
3. No `induction` tactic; general characterizations are driven by
   explicit `List.rec` applications.
4. `Geb/Mathlib/` import rules: only `Mathlib.*`, `Batteries.*` and
   `Geb.Mathlib.*`; `GebTests/Mathlib/` additionally
   `GebTests.Mathlib.*`. The `Geb.Mathlib.` and `GebTests.Mathlib.`
   prefixes appear only in `^import` lines — not in a namespace,
   docstring or comment.
5. Every unfolding lemma is per-constructor with the recursive value
   exposed, and is stated at canonical or `Fin.cons`-shaped
   environments. See § The three unfolding devices.
6. Every `def` and every theorem of public interest carries a docstring;
   each module carries a module docstring with the mandated sections,
   each present when it has content and omitted (never a placeholder)
   when vacuous.
7. Names follow mathlib's conventions: `lowerCamelCase` for the
   expressions, `snake_case` for every theorem.
8. No `#guard`; every test assertion is a `theorem` closing by `rfl`.
9. Lambda notation uses `↦`, not `=>`, in `fun`. Lines are at most 100
   characters. Indentation is two spaces.
10. All `.lean` files declare `module` after the copyright block. The
    library modules use `public import` and a `public section`; test
    modules use plain `import` with
    `set_option linter.privateModule false`.
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
15. `unusedSimpArgs` and `unnecessarySimpa` are errors under this
    repository's warning-as-error setting, so a `simp only` list that
    over- or under-specifies fails the build. Every `simp only` list
    below was measured as written.
16. Discharge an arithmetic side condition with `omega` or by cases, not
    with a bare `simp`, per `docs/rules/lean-coding.md`
    § Constructive-only Lean code. The case that arises here is a `simp`
    left to decide an `if` whose condition is an arithmetic proposition:
    closing `([] : List Bool) = if (b :: c :: v).length = 1 then [true]
    else []` by `simp` measures `[propext, Classical.choice, Quot.sound]`,
    while `rw [if_neg (by simp only [List.length_cons]; omega)]` measures
    `[propext, Quot.sound]`. A `simp` that merely rewrites an arithmetic
    equation is not affected — `(true :: v).length = v.length + 1` by
    `simp` measures `[propext]` — and `noUnderflowSem_gen` below closes with
    `simp` given an `omega`-proved hypothesis and stays clean. `by nofun`
    discharges `¬ (([] : List Bool) = [true])` with no axiom at all. The
    dependence is silent at elaboration and surfaces only at
    `lake lint`, so re-measure after any change to a proof.

## How a task makes its commit

`jj` has no staging area. The working copy is itself a commit — the one
`jj log` marks `@` — and jj snapshots edits into it continuously. A file
written now lands in whatever `@` is now. Every task below therefore
begins by creating its change and only then edits files.

This segment is the top of the stack, so once Task 1 has put `@` on the
segment head the idiom is

```bash
jj new -m "<message>"
```

which creates a child of `@` and checks it out. `jj commit` would do the
same thing in two steps, but it describes `@` — the previous task's
commit — with the message belonging to the new task, so it is not used
here.

Task 1 must run first in any session, because it is what establishes
where `@` is. The preceding plan's last step leaves it on this segment's
head, but a session that resumes from elsewhere — or that reached this
plan another way — will not have it there.

## Commit sequence

This segment sits above `feat/binary-tree-preorder`'s bookmark. The spec
fixes the order: spec, plan, restructure, implementation commits,
documentation, then a final commit removing the spec, the plan and the
measured-Lean companion.

```text
…segment 1, ending in its own removal commit  ← feat/binary-tree-preorder
doc: add the tree-recognizer design spec
doc: add the tree-recognizer implementation plan
refactor(computability): index the class module and hoist compChildren
feat(computability): add the tree recognizer's expressions
feat(computability): characterize the counter and underflow test
feat(computability): characterize the recognizer against Valid
test(computability): assert the recognizer and its rejections
doc: record the tree recognizer and its follow-on work
doc: remove the tree-recognizer spec, plan and measured Lean  ← feat/bc-tree-recognizer
```

Tasks 2, 3, 4, 5, 6, 7 and 9 each add one commit. Tasks 1 and 8 add none:
Task 1 only inspects and repositions the working copy, and Task 8 runs
the gate against Task 7's commit.

## File structure

| Path | Responsibility |
| --- | --- |
| `Geb/Mathlib/Computability/BellantoniCook.lean` | becomes the directory index over `Basic` and `Tree` |
| `Geb/Mathlib/Computability/BellantoniCook/Basic.lean` | the class, moved from the file above, gaining `compChildren` |
| `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` | the expressions, the unfolding and environment lemmas, the characterizations |
| `GebTests/Mathlib/Computability/BellantoniCook.lean` | becomes the test directory index |
| `GebTests/Mathlib/Computability/BellantoniCook/Basic.lean` | the existing worked expressions, moved, losing their private `compChildren` |
| `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean` | the assertions of Task 6 |
| `docs/references.bib` | already carries `Hofmann2000` and `Marion2003` in this segment's spec commit |
| `docs/index.md` | one path correction and one new bullet |
| `TODO.md` | one `###` subsection, two stale-path corrections, one trigger |
| `docs/superpowers/specs/2026-08-06-bc-tree-recognizer-design.md` | exists; removed in Task 9 |
| `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md` | this plan; removed in Task 9 |
| `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-handoff.md` | the measured Lean the spec's § Verification evidence rests on; removed in Task 9 |

`Tree.lean` is one module, not a `Defs`/`Basic` split: the unfolding and
environment lemmas are few and are consumed only here. The spec's
§ Deferred item 3 records extraction once a second Bellantoni-Cook
function needs them.

The restructure is what `CONTRIBUTING.md` § Repo structure requires —
one indexing file per directory. Leaving the class in
`BellantoniCook.lean` would make `Computability.lean` index two levels
and leave `BellantoniCook/` without an index; moving the content into
`BellantoniCook/BellantoniCook.lean` instead would name the module
`Geb.Mathlib.Computability.BellantoniCook.BellantoniCook`.
Importers of `Geb.Mathlib.Computability.BellantoniCook` are unaffected,
since the index re-exports `Basic` with `public import`.

The repository is not uniform here, as the spec records:
`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` carries content at a
path where an index belongs, and so does its test-side counterpart. In
both trees the parent `CategoryTheory.lean` imports `FreeCoprodCompDisc`
and `FreeCoprodCompDisc.NatTrans` directly, so it indexes two levels and
`FreeCoprodCompDisc/` has no index of its own — the arrangement Task 2's
rationale rejects for `BellantoniCook`. This restructure follows the rule
rather than that precedent and leaves those two as the remaining cases;
Task 7 Step 6 records them as a trigger rather than fixing them here, one
concern per branch.

## Deltas from the spec

Three differences between the spec and what this plan builds — two
against § The theorems, one against § Verification evidence. Each was
forced by a measurement taken while writing the plan; none changes what
the segment proves.

1. **`noUnderflowSem_cons` is three theorems.** The spec's
   § Verification evidence already records this: the proof needs the
   nil, `false`-step and `true`-step lemmas separately. They are
   `noUnderflowSem_nil`, `noUnderflowSem_cons_false`,
   `noUnderflowSem_cons_true`.
2. **Four auxiliary theorems are added**: `countSem_apply` (the counter at
   an arbitrary environment), `noUnderflowSem_gen` (the `Fin.cons`-shaped
   generalization the `List.rec` runs at), `eqOneSem_env` (the
   environment-normalization lemma for `eqOne`) and `isTreeSem_apply` (the
   one-step unfolding of the recognizer). The spec's § Unfolding calls
   for one environment lemma per expression, so `eqOneSem_env` is implied
   rather than new.
3. **`tail_replicate` is not written.** Lean core already states it, as
   `@[simp] theorem List.tail_replicate {n : Nat} {a : α} :
   (replicate n a).tail = replicate (n - 1) a` in
   `Init/Data/List/Lemmas.lean`. This plan reuses it, per
   `CONTRIBUTING.md` § Code is cost. It is `@[simp]`, but the proofs
   below name it explicitly, in one `rw` list and one `simp only` list,
   so nothing depends on the default simp set.

### What this plan's measurements changed in the spec

Four amendments, applied in the spec's own commit rather than carried
here as deltas, so that the spec and the plan agree:

- § Per-definition classification now covers all twenty-four definitions
  this segment ships, and § Tests classifies the one it ships into
  `GebTests/Mathlib/`.
- § Placement and file manifest now lists the moved test module, the new
  test index and the measured-Lean companion.
- § Unfolding now introduces the four `Sem` ascriptions the statements
  are written over, and its device 3 was narrowed — see below.
- § The theorems had its theorems renamed and its statements rewritten
  over those ascriptions. It was written before the ascriptions existed, when the
  statements read `eval count ![w] ![]`; mathlib names a lemma after the
  head symbol of its statement, and `eval` occurs in none of them. Two
  names changed more than mechanically: `eval_isTree_eq_true_iff` became
  `isTreeSem_eq_singleton_iff_valid`, its right-hand side being the
  one-element list `[true]` and not the `Bool` `true`, and
  `eval_isTree_iff_exists_print` became
  `isTreeSem_eq_singleton_iff_exists_print` for the same reason and to
  put both in the infix `_iff_` form.

### Two measurements restated

The ascriptions are load-bearing in exactly two places:
`rw [countSem_apply]` inside `noUnderflowSem_gen`, and `rw [eqOneSem_env]`
inside `isTreeSem_eq_singleton_iff_valid`, both fail without them —
*Tactic `rewrite` failed … Note: The target expression is not
type-correct under the `implicit` transparency level*, the `Sigma`
projection in the type blocking the motive. Everything else in the
module, `countSem_apply` and `isTreeSem_apply` included, elaborates
stated through the projection.

The spec's § Unfolding read more strongly than the measurement supports
and has been corrected; this records what was measured. The rule
"write every child family as a constant function" cannot apply to a
`cond` node's four safe children, which are four distinct expressions;
`![…]` is the only spelling available there. What was measured is
narrower and is what binds: the spelling matters only where the family
is consumed at a bound index — that is, under `evalRec`'s stuck
recursion, which is the guard inside `noUnderflow`'s `true`-step. Both
`![…]` and `fun _ ↦ …` were measured to work in `isTree`, where `eqOne`
consumes its safe environment at the literal index `0`.

## The three unfolding devices

The segment's whole technical content, restated from the spec's
§ Unfolding because every task below depends on it.

1. **State each step lemma at an abstract `Fin.cons`-shaped
   environment**, per constructor, with the recursive value exposed on
   the right. `Sem (n, s)` is a function type, so `evalRec` recurses at a
   function motive and every eliminator in the chain sits at that motive;
   eliminators at function motives reduce only when their scrutinee is a
   constructor. A lemma with a symbolic bit and a lemma in fold shape are
   both non-definitional and fail with *Not a definitional equality*.
2. **One `funext`-based environment-normalization lemma for each
   expression whose meaning is named at an environment other than the
   canonical one**, proved by `funext` and `Subsingleton.elim`, rewriting
   an arbitrary environment to the canonical `![…]` form. `Sem` being a
   function type, no `rfl` lemma reaches this. Three expressions qualify;
   `isTreeSem` is only ever applied at `![w] ![]`, so it gets none.
3. **A `comp` node's child families are written `fun _ ↦ e` for the node
   whose environment a lemma names**, and specifically for the inner
   node inside `noUnderflow`'s guard. `![e]` is `Matrix.cons e ![]`,
   which does not reduce at a bound index. This constrains how the
   expression is built: retrofitting it means rebuilding the expression
   and every lemma above it, so it is settled in Task 3 and not
   revisited.

A failed `rfl` therefore signals one of three things — a rejected
statement shape, a non-canonical environment, or a child family whose
spelling does not reduce to the environment the lemma names — and the
third is a defect in the expression, not in the lemma.

---

## Task 1: Verify the stack and take the working copy to the segment head

**Files:**

- Modify: none (version-control inspection and repositioning only)

**Interfaces:**

- Consumes: `feat/binary-tree-preorder` complete through its own plan's
  Task 6
- Produces: evidence that this segment's commits sit above that
  bookmark, that nothing of this segment has leaked below it, and a
  working copy positioned at the segment head so that Task 2's `jj new`
  extends the stack rather than forking it

- [ ] **Step 1: Print the stack**

```bash
jj log -r 'main::feat/bc-tree-recognizer' --no-pager \
  -T 'change_id.short() ++ "  " ++ bookmarks ++ "  " ++ description.first_line() ++ "\n"'
```

Expected: `feat/binary-tree-preorder` on segment 1's removal commit, and
above it this segment's spec commit and plan commit, the latter carrying
`feat/bc-tree-recognizer`.

If the plan commit is absent, create it:

```bash
jj new --insert-after <spec-2 change id> --no-edit \
  -m "doc: add the tree-recognizer implementation plan"
jj squash --use-destination-message \
  --from <change holding the plan file> --into <the new change> \
  docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md
```

`--use-destination-message` matters: moving the plan file out empties the
source change, jj abandons it, and with two non-empty descriptions it
would otherwise prompt for a combined one and stall a non-interactive
run.

- [ ] **Step 2: Confirm the segment boundary**

```bash
jj diff --stat -r 'main..feat/binary-tree-preorder'
jj diff --stat -r 'feat/binary-tree-preorder..feat/bc-tree-recognizer'
```

Expected: the first names no path under `docs/superpowers/`. The second
names this segment's spec, this plan, the measured-Lean companion
`docs/superpowers/plans/2026-08-06-bc-tree-recognizer-handoff.md`, and
`docs/references.bib`.

`docs/references.bib` appears in both diffs, since segment 1's spec
commit adds `Knuth1997`, so `--stat` cannot say which entries each
carries. Check the content:

```bash
jj file show -r feat/binary-tree-preorder docs/references.bib \
  | grep -q 'Knuth1997' || echo "BIB UNREADABLE"
jj file show -r feat/binary-tree-preorder docs/references.bib \
  | grep -q 'Hofmann2000\|Marion2003' && echo LEAK || echo clean
```

Expected: `clean`, with nothing before it. `LEAK` means those two entries
have leaked down into segment 1; `BIB UNREADABLE` means the first command
failed and the second one's `clean` is meaningless. (`grep -c` is the
wrong instrument for the second check: it prints `0` and exits 1, so a
checker reading the exit status sees the pass as a failure.)

- [ ] **Step 3: Put the working copy on the segment head**

Every task below creates its commit with `jj new`, which makes a child of
`@`; run from anywhere but this segment's head it would fork the stack.
The preceding plan's last step already puts `@` here, so this is usually
a no-op: `jj edit` on the current commit is idempotent. It runs
unconditionally because a session may reach this plan another way.

```bash
jj edit feat/bc-tree-recognizer
jj log -r @ --no-pager -T 'change_id.short() ++ "  " ++ description.first_line() ++ "\n"'
```

Expected: `@` is the tree-recognizer plan commit.

- [ ] **Step 4: Confirm the branch builds**

Run: `lake build && lake test`
Expected: exit 0 from each.

---

## Task 2: The directory restructure

**Files:**

- Create: `Geb/Mathlib/Computability/BellantoniCook/Basic.lean` (moved
  content, plus `compChildren`)
- Modify: `Geb/Mathlib/Computability/BellantoniCook.lean` (becomes the
  index)
- Create: `GebTests/Mathlib/Computability/BellantoniCook/Basic.lean`
  (moved content, less its private `compChildren`)
- Modify: `GebTests/Mathlib/Computability/BellantoniCook.lean` (becomes
  the test index)

**Interfaces:**

- Consumes: the two existing modules
- Produces: `Geb.Mathlib.Computability.BellantoniCook.Basic`, re-exported
  by `Geb.Mathlib.Computability.BellantoniCook`, so that every existing
  importer is unaffected; and `BellantoniCook.compChildren` as the single
  copy of the `comp`-child ordering

Every step lemma of Task 4 closes by `rfl` across a module boundary into
`Basic.lean`. The module system does not unfold a non-exposed
definition, so an unexposed `sig`, `Direction`, `rc`, `q`, `BC`,
`BC.eval`, `evalRec` or `evalValue` would leave every such lemma stuck.
All of them are already `@[expose]` inside a `public section` in the file
as merged, and this move carries them across untouched, so the property
is preserved rather than newly established. Step 6 re-measures it anyway:
the failure is silent at the LSP and surfaces only at `lake build`.

- [ ] **Step 1: Create the change**

```bash
jj new -m "refactor(computability): index the class module and hoist compChildren"
```

- [ ] **Step 2: Move the library module**

```bash
mkdir -p Geb/Mathlib/Computability/BellantoniCook
mv Geb/Mathlib/Computability/BellantoniCook.lean \
   Geb/Mathlib/Computability/BellantoniCook/Basic.lean
```

Leave the moved file's contents untouched apart from Step 3, including
its module docstring, whose title still describes it.

- [ ] **Step 3: Add `compChildren` to the moved module**

The existing test module declares its own `compChildren` at the root
namespace, and `Tree.lean` needs the same function. Two copies of a
`comp` node's child ordering is duplication `CONTRIBUTING.md` § Code is
cost rules out, and a root-namespace copy alongside a
`BellantoniCook`-namespace one makes every unqualified use ambiguous
under `open BellantoniCook`. One copy, in the module that declares
`Direction`, resolves both.

Insert it inside `Basic.lean`'s `public section`, after the
`sigFinitary` instance, which keeps `sig` adjacent to its three
finiteness declarations. The spec's "belongs with `Direction`" is about
which module it belongs in, not where in the file:

```lean
/-- The children of a `comp` node, in the order `Direction` gives them:
the head, then the normal arguments, then the safe arguments. -/
@[expose] def compChildren {m k : ℕ} (h : sig.toPFunctor.W)
    (gN : Fin m → sig.toPFunctor.W) (gS : Fin k → sig.toPFunctor.W) :
    Unit ⊕ Fin m ⊕ Fin k → sig.toPFunctor.W :=
  Sum.elim (fun _ ↦ h) (Sum.elim gN gS)
```

Add to that module's `## Main definitions` list, after the `sig` entry,
so that the list keeps tracking declaration order:

```markdown
* `BellantoniCook.compChildren` — a `comp` node's children in the order
  `Direction` gives them.
```

- [ ] **Step 4: Write the library index**

Create `Geb/Mathlib/Computability/BellantoniCook.lean` with the `Basic`
line only. `Tree` does not exist until Task 3, which adds its import
line; keeping the index truthful at every commit is what makes each
commit build on its own.

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.BellantoniCook.Basic

/-!
# BellantoniCook — index
-/
```

- [ ] **Step 5: Move the test module and delete its private `compChildren`**

```bash
mkdir -p GebTests/Mathlib/Computability/BellantoniCook
mv GebTests/Mathlib/Computability/BellantoniCook.lean \
   GebTests/Mathlib/Computability/BellantoniCook/Basic.lean
```

Two changes to the moved file, and no others:

- Delete its `compChildren` docstring and `def` outright. The module
  already has `open BellantoniCook`, so its remaining uses resolve to
  `BellantoniCook.compChildren` unchanged. Measured: the module's `plus`,
  `mult` and their assertions elaborate with the private copy deleted and
  no other edit.
- Narrow its first import from
  `import Geb.Mathlib.Computability.BellantoniCook` to
  `import Geb.Mathlib.Computability.BellantoniCook.Basic`, which is what
  a test module for `Basic.lean` should name.

Then create `GebTests/Mathlib/Computability/BellantoniCook.lean` as the
test index:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Computability.BellantoniCook.Basic

/-!
# BellantoniCook tests — index
-/
```

- [ ] **Step 6: Build and re-measure exposure**

Run: `lake build && lake build GebTests && lake test`
Expected: exit 0 from each, with no diagnostics. A *definitions were not
unfolded because their definition is not exposed* error names the
declaration whose `@[expose]` did not survive the move. An
*Ambiguous term compChildren* error means the test module's private copy
was not deleted.

- [ ] **Step 7: Confirm the imports are still minimal**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: none of the four files appears in the reported list.

This is the step that first creates a module under a new
`GebTests/Mathlib/Computability/BellantoniCook/`, so `lake shake` may
print a `PANIC at Option.get!` trace from `Lake.Shake.visitModule`. It
exits 0 when that happens; a non-zero exit is a real failure.

- [ ] **Step 8: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: four paths — the two moved files, added at their new locations,
and the two vacated paths, which are not deleted but rewritten as index
files and so appear modified.

---

## Task 3: The four expressions

**Files:**

- Create: `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`
- Modify: `Geb/Mathlib/Computability/BellantoniCook.lean` (add the
  `Tree` import)

**Interfaces:**

- Consumes: `BellantoniCook.sig`, `sig.toPFunctor.W`, `BC`, `BCOf`,
  `BC.eval`, `compChildren` from `Basic`;
  `SlicePFunctor.decidableWValid` from
  `Geb.Mathlib.Data.PFunctor.Slice.Decidable`; `WType.mk` and mathlib's
  `![…]` vector notation, both reached transitively through `Basic`
- Produces, all in namespace `BellantoniCook`:
  - `zeroAt (n s : ℕ) : sig.toPFunctor.W`, `oneAt (n s : ℕ) : sig.toPFunctor.W`
  - `incRaw`, `decRaw`, `countRaw`, `guardRaw`, `nuTrueStepRaw`,
    `noUnderflowRaw`, `eqOneInnerRaw`, `eqOneRaw`, `isTreeRaw`, each
    `: sig.toPFunctor.W`
  - `count`, `noUnderflow`, `eqOne`, `isTree`, each `: BC`
  - `countOf : BCOf 1 0`, `noUnderflowOf : BCOf 1 0`,
    `eqOneOf : BCOf 0 1`, `isTreeOf : BCOf 1 0`
  - `countSem`, `noUnderflowSem`, `isTreeSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool`;
    `eqOneSem : (Fin 0 → List Bool) → (Fin 1 → List Bool) → List Bool`

Two properties of the `⟨_, by decide⟩` form, each of which cost an
iteration when the expressions were first built: `⟨WType.mk …, by decide⟩`
does not elaborate — instance search fails against an inline `WType.mk`
application, reporting *failed to synthesize Decidable (sig.WValid
(WType.mk …))* — so every raw tree is bound as its own `def` first; and
`cond`'s even branch is dead in `eqOneInnerRaw`, a non-empty unary
numeral always having head `true`, but must still be supplied.

- [ ] **Step 1: Create the change**

```bash
jj new -m "feat(computability): add the tree recognizer's expressions"
```

- [ ] **Step 2: Write the module header and the shared constructors**

Create `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`. The
`Geb.Mathlib.Data.Tree.Preorder` import is added in Task 4, where the
first use of `BinTree.depth` appears; nothing in this task needs it.

The module docstring written here omits `## Main statements`: no theorem
exists in this commit, and `docs/rules/lean-coding.md` § Documentation
requires each section to be present when it has content and omitted when
vacuous. Tasks 4 and 5 add that section as their theorems arrive.

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.BellantoniCook.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable

/-!
# A tree recognizer in the Bellantoni-Cook class

Four expressions of `B` deciding whether a bitstring is the preorder
spelling of a binary tree. `B` is a characterization of the
polynomial-time functions [BellantoniCook1992], which is used and not
proved here, so the membership test lies in that class without a separate
complexity argument.

The recognizer is a single right-to-left scan rather than a recursive
descent. A descent would parse the second subtree from a remainder the
first call computes, which sits in safe position, and recursion on a safe
argument is what the class forbids.

## Main definitions

* `BellantoniCook.zeroAt`, `BellantoniCook.oneAt` — the empty bitstring
  and the one-bit string `[true]` at an arbitrary arity.
* `BellantoniCook.count` — the stack depth in unary, of arity `(1, 0)`.
* `BellantoniCook.noUnderflow` — whether every node bit is read at depth
  at least two, of arity `(1, 0)`.
* `BellantoniCook.eqOne` — whether a unary numeral is one, of arity
  `(0, 1)`.
* `BellantoniCook.isTree` — the recognizer, of arity `(1, 0)`.

## Implementation notes

`noUnderflow` must track the counter and whether it underflowed, and
`safeRec` yields one recursive value, which cannot be a pair: two safe
bitstrings do not concatenate. Its step therefore recomputes `count` from
the normal tail at each level, so the recognizer runs in time quadratic
in the input length rather than linear. [HeraudNowak2011] § 7 proposes
the replacement for exactly this difficulty — define such a function in
Cobham's class and apply the translation of § 5, Theorem 2 — and the
authors report that "dealing with the carry bit does not fit immediately
in Bellantoni-Cook's recursion scheme".

The node inside `noUnderflowRaw`'s guard writes both its child families
as constant functions rather than with vector notation. `evalValue`'s
`comp` clause builds the environment it passes to the head out of those
families, and `![e]` is `Matrix.cons e ![]`, which does not reduce at the
bound index `evalRec`'s stuck recursion supplies. The requirement is
local to that node; the guard's own safe family is written the same way
for uniformity, and every other family in the module is consumed at a
literal index, where either spelling reduces.

`countSem`, `noUnderflowSem`, `eqOneSem` and `isTreeSem` name each
meaning at its arity, so that the arity pair is reduced and rewriting
under it type-checks. A meaning taken through the `Sigma` projection
instead has a type headed by that projection rather than by an arrow, and
`rw` under it fails as not type-correct at `implicit` transparency.

## References

* [HeraudNowak2011]
* [BellantoniCook1992]

## Tags

Bellantoni-Cook, polytime, implicit computational complexity, safe
recursion, binary tree, preorder, recognizer
-/

namespace BellantoniCook

public section

/-- The empty bitstring at an arbitrary arity. -/
@[expose] def zeroAt (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 0)
    (compChildren (WType.mk .zero Fin.elim0) Fin.elim0 Fin.elim0)

/-- The one-bit string `[true]` at an arbitrary arity. -/
@[expose] def oneAt (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0 ![zeroAt n s])
```

- [ ] **Step 3: Add the counter**

Append:

```lean
/-- The increment step of `count`: prepend `true` to the recursive
value. -/
@[expose] def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

/-- The decrement step of `count`: drop the low bit of the recursive
value. -/
@[expose] def decRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

/-- The raw tree of the counter. A leaf bit is `false` and increments; a
node bit is `true` and decrements. -/
@[expose] def countRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0) ![WType.mk .zero Fin.elim0, incRaw, decRaw]

/-- The stack depth of a bitstring read right to left, in unary. -/
@[expose] def count : BC := ⟨countRaw, by decide⟩
```

- [ ] **Step 4: Add the underflow test**

Append. Both child families of `guardRaw`'s inner node are written
`fun _ ↦ …`; that is device 3 of § The three unfolding devices and it is
what makes Task 4's `true`-step lemma definitional. `guardRaw`'s own safe
family is written the same way for uniformity — measured, `![…]` there
works equally, since that family is consumed at a literal index.

```lean
/-- The guard of `noUnderflow`'s `true`-step: `pred (count v)`, empty
exactly when the counter is below two.

`count` reaches this guard as the head of an inner `comp`, not as a safe
child of the step. A `safeRec 0 0` step has arity `(1, 1)`, and a
`comp n s m k` requires its safe children at `(n, s)`; placing `count`
there would require it at `(1, 1)`, which it does not meet at `(1, 0)`.
Written as `comp 1 1 1 0` the head requirement is `(1, 0)`, which `count`
does meet, and its one normal child is the projection onto the recursion
variable. -/
@[expose] def guardRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      (fun _ ↦ WType.mk (.comp 1 1 1 0)
          (compChildren countRaw (fun _ ↦ WType.mk (.proj 1 0 0) Fin.elim0)
            (fun _ ↦ zeroAt 1 1))))

/-- The `true`-step of `noUnderflow`: fail when the guard is empty,
otherwise pass the recursive value up. Failure propagates, `[]` being the
only value ever passed up in place of the recursive one. -/
@[expose] def nuTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![guardRaw, zeroAt 1 1, WType.mk (.proj 1 1 1) Fin.elim0,
        WType.mk (.proj 1 1 1) Fin.elim0])

/-- The raw tree of the underflow test. -/
@[expose] def noUnderflowRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0)
    ![oneAt 0 0, WType.mk (.proj 1 1 1) Fin.elim0, nuTrueStepRaw]

/-- Whether every node bit of a bitstring is read at depth at least two,
returning `[true]` when it is and `[]` when it is not. -/
@[expose] def noUnderflow : BC := ⟨noUnderflowRaw, by decide⟩
```

- [ ] **Step 5: Add the one-test and the recognizer**

Append:

```lean
/-- The inner conditional of `eqOne`: whether the predecessor of the
argument is empty. The even branch is dead, a non-empty unary numeral
always having head `true`, but the conditional takes four safe arguments
and it must be supplied. -/
@[expose] def eqOneInnerRaw : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.comp 0 1 0 1)
          (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
            ![WType.mk (.proj 0 1 0) Fin.elim0]),
        oneAt 0 1, zeroAt 0 1, zeroAt 0 1])

/-- The raw tree of the one-test: empty is not one, and otherwise the
argument is one exactly when its predecessor is empty. -/
@[expose] def eqOneRaw : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.proj 0 1 0) Fin.elim0, zeroAt 0 1, eqOneInnerRaw,
        eqOneInnerRaw])

/-- Whether a unary numeral has length one, returning `[true]` or `[]`. -/
@[expose] def eqOne : BC := ⟨eqOneRaw, by decide⟩

/-- The raw tree of the recognizer: `noUnderflow` of the word, and the
counter equal to one. -/
@[expose] def isTreeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 0 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![noUnderflowRaw, zeroAt 1 0,
        WType.mk (.comp 1 0 0 1) (compChildren eqOneRaw Fin.elim0 ![countRaw]),
        WType.mk (.comp 1 0 0 1) (compChildren eqOneRaw Fin.elim0 ![countRaw])])

/-- The recognizer: whether a bitstring is the preorder spelling of a
binary tree. The output is `[true]` or `[]`, so correctness is an
equation rather than a disequation. -/
@[expose] def isTree : BC := ⟨isTreeRaw, by decide⟩
```

- [ ] **Step 6: Add the arity witnesses and the meaning ascriptions**

Append:

```lean
/-- `count` at its declared arity. Elaborating this is the assertion that
`BC.arity count` is `(1, 0)`. -/
@[expose] def countOf : BCOf 1 0 := ⟨count, rfl⟩

/-- `noUnderflow` at its declared arity. -/
@[expose] def noUnderflowOf : BCOf 1 0 := ⟨noUnderflow, rfl⟩

/-- `eqOne` at its declared arity. -/
@[expose] def eqOneOf : BCOf 0 1 := ⟨eqOne, rfl⟩

/-- `isTree` at its declared arity. -/
@[expose] def isTreeOf : BCOf 1 0 := ⟨isTree, rfl⟩

/-- The counter's meaning at its arity, ascribed so that the arity pair
is reduced and rewriting under it type-checks. -/
@[expose] def countSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool := (BC.eval count).2

/-- The underflow test's meaning at its arity, ascribed likewise. -/
@[expose] def noUnderflowSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool :=
  (BC.eval noUnderflow).2

/-- The one-test's meaning at its arity, ascribed likewise. -/
@[expose] def eqOneSem :
    (Fin 0 → List Bool) → (Fin 1 → List Bool) → List Bool := (BC.eval eqOne).2

/-- The recognizer's meaning at its arity, ascribed likewise. -/
@[expose] def isTreeSem :
    (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool := (BC.eval isTree).2

end

end BellantoniCook
```

- [ ] **Step 7: Add the `Tree` line to the library index**

In `Geb/Mathlib/Computability/BellantoniCook.lean`, add below the
`Basic` line:

```lean
public import Geb.Mathlib.Computability.BellantoniCook.Tree
```

- [ ] **Step 8: Build and lint**

Run: `lake build && lake lint`
Expected: exit 0 from each. This step adds `Tree.lean` to `Geb`'s import
closure, so it is where `GebMeta.detectNonstandardAxiom` first sees the
four `by decide` proof terms and the four `Sem` ascriptions. Linting here
rather than at Task 5 attributes any axiom leak to the commit that
introduced it — Global constraint 16 notes that the dependence is silent
at elaboration and surfaces only at `lake lint`.

Each `by decide` is an admissibility
check: a failure means the raw tree violates `rc` at some node, and the
node is found by re-checking arities against `Basic.lean`'s `rc` and `q`.
Each `rfl` in a `BCOf` witness is an arity assertion; a failure there
means the expression has the wrong arity, not that the witness is
mis-stated.

`Geb.Mathlib.Data.PFunctor.Slice.Decidable` is a `public import` because
the `by decide` proof terms sit inside `@[expose]` bodies and reference
the `Decidable` instance. `lake shake` in Task 8 is the authority on
whether any import is redundant.

- [ ] **Step 9: Verify that the guard's safe-slot route is inadmissible**

`guardRaw`'s docstring justifies its shape by an arity argument: putting
`count` in a safe-child slot of the step's `comp` would require it at
`(1, 1)`, which it does not meet at `(1, 0)`. The control below is that
exact shape — `pred` applied to `countRawProbe` as its one safe child.

The measured-Lean companion's `guardSafeRaw` is a different shape: it
makes `count` the head of an inner `comp 1 1 0 1`, whose head requirement
is `(m, k) = (0, 1)`. That is also inadmissible, but by a different
obstruction, so it does not test the docstring's claim. Use the control
below instead.

Neither control ships — each exists only to justify the shape of
`guardRaw` — so run it once through the `lean-lsp` MCP's `lean_run_code`
rather than committing it. The snippet must be self-contained;
`lean_run_code` also needs the project path initialised, so call
`lean_diagnostic_messages` on an existing `.lean` file once beforehand.

```lean
import Geb.Mathlib.Computability.BellantoniCook.Basic
import Geb.Mathlib.Data.PFunctor.Slice.Decidable

open BellantoniCook

def countRawProbe : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0)
    ![WType.mk .zero Fin.elim0,
      WType.mk (.comp 1 1 0 1)
        (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
          ![WType.mk (.proj 1 1 1) Fin.elim0]),
      WType.mk (.comp 1 1 0 1)
        (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
          ![WType.mk (.proj 1 1 1) Fin.elim0])]

-- `count` as a safe child, which is the route the docstring rules out
def guardCountAsSafeChild : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0 ![countRawProbe])

theorem safeChild_invalid : sig.wValidBool guardCountAsSafeChild = false :=
  rfl
```

Expected: elaborates with no diagnostics. If it does not, `guardRaw`'s
justification is wrong and its docstring must be corrected before
proceeding.

The control is left out of `Tree.lean` and out of Task 6's test module on
cost grounds — it records why one expression is shaped as it is, and the
spec's § Verification evidence records both obstructions. Nothing
prevents shipping it: `SlicePFunctor.wValidBool` is `@[expose]`, and
`GebTests/Mathlib/Computability/BellantoniCook/Basic.lean` already
carries the analogous `wValid_badRaw_eq_false`.

- [ ] **Step 10: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: two paths — `Tree.lean` added, the index modified.

---

## Task 4: The counter and the underflow test

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` (add the
  `Geb.Mathlib.Data.Tree.Preorder` import and the twelve theorems)

**Interfaces:**

- Consumes: everything Task 3 produced; `BinTree.depth`,
  `BinTree.depth_cons_false`, `BinTree.depth_cons_true`, `BinTree.ok`,
  `BinTree.ok_cons_false`, `BinTree.ok_cons_true` from
  `Geb.Mathlib.Data.Tree.Preorder`; `List.tail_replicate`,
  `List.replicate_succ`, `List.replicate_zero`, `funext`,
  `Subsingleton.elim` and `Nat.eq_zero_or_pos`, all from Lean core
- Produces:
  - `countSem_nil`, `countSem_cons_false`, `countSem_cons_true`
  - `countSem_env`, `countSem_eq`, `countSem_apply`
  - `noUnderflowSem_nil`, `noUnderflowSem_cons_false`, `noUnderflowSem_cons_true`
  - `noUnderflowSem_env`, `noUnderflowSem_gen`, `noUnderflowSem_eq`

Every theorem below was measured to elaborate as written, at
v4.33.0-rc2, while this plan was being written — not transcribed from the
measured-Lean companion, which predates the `Sem` ascriptions and the
substitution of Lean core's `List.tail_replicate`.

- [ ] **Step 1: Create the change**

```bash
jj new -m "feat(computability): characterize the counter and underflow test"
```

- [ ] **Step 2: Add the encoding import**

In `Tree.lean`, add below the `Slice.Decidable` line:

```lean
public import Geb.Mathlib.Data.Tree.Preorder
```

Add a `## Main statements` section to the module docstring, between
`## Main definitions` and `## Implementation notes`, naming the two
characterizations this task proves:

```markdown
## Main statements

* `BellantoniCook.countSem_eq` — `count` computes `BinTree.depth` in
  unary.
* `BellantoniCook.noUnderflowSem_eq` — `noUnderflow` computes
  `BinTree.ok`.
```

Add to `## Implementation notes`, before the paragraph on the guard's
child families:

```markdown
Each unfolding lemma is stated per constructor with the recursive value
exposed on the right. `Sem` is a function type, so `evalRec` recurses at
a function motive and every eliminator in the chain sits there;
eliminators at function motives reduce only when their scrutinee is a
constructor, so a symbolic-bit or fold-shaped statement is not
definitional.
```

- [ ] **Step 3: Add the counter's unfolding lemmas and characterization**

Append inside the `public section`, before its `end`:

```lean
/-- The counter of the empty bitstring is empty. -/
theorem countSem_nil : countSem ![[]] ![] = [] := rfl

/-- A leaf bit increments the counter. -/
theorem countSem_cons_false (v : List Bool) :
    countSem ![false :: v] ![] = true :: countSem ![v] ![] := rfl

/-- A node bit decrements the counter, truncated at zero. -/
theorem countSem_cons_true (v : List Bool) :
    countSem ![true :: v] ![] = (countSem ![v] ![]).tail := rfl

/-- The counter at an arbitrary environment is the counter at the
canonical one. -/
theorem countSem_env (f : Fin 1 → List Bool) (g : Fin 0 → List Bool) :
    countSem f g = countSem ![f 0] ![] := by
  have hf : f = ![f 0] := funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  have hg : g = ![] := Subsingleton.elim _ _
  conv_lhs => rw [hf, hg]

/-- The counter computes the stack depth, in unary. -/
theorem countSem_eq (w : List Bool) :
    countSem ![w] ![] = List.replicate (BinTree.depth w) true := by
  refine List.rec (motive := fun u ↦
    countSem ![u] ![] = List.replicate (BinTree.depth u) true) rfl ?_ w
  intro b v ih
  cases b
  · rw [countSem_cons_false, ih, BinTree.depth_cons_false, List.replicate_succ]
  · rw [countSem_cons_true, ih, BinTree.depth_cons_true, List.tail_replicate]

/-- The counter's characterization at an arbitrary environment, which is
the form the underflow test's step lemma needs. -/
theorem countSem_apply (f : Fin 1 → List Bool) (g : Fin 0 → List Bool) :
    countSem f g = List.replicate (BinTree.depth (f 0)) true := by
  rw [countSem_env]; exact countSem_eq _
```

- [ ] **Step 4: Build and check the three `rfl` lemmas in isolation**

Run: `lake build Geb.Mathlib.Computability.BellantoniCook.Tree`
Expected: exit 0. A *Not a definitional equality* on any of the three
`rfl` lemmas is a statement-shape failure, not a proof failure: re-read
§ The three unfolding devices before changing anything.

- [ ] **Step 5: Add the underflow test's step lemmas**

Append:

```lean
/-- The underflow test succeeds vacuously on the empty bitstring. -/
theorem noUnderflowSem_nil (x y : Fin 0 → List Bool) :
    noUnderflowSem (Fin.cons [] x) y = [true] := rfl

/-- A leaf bit leaves the underflow test's verdict unchanged. -/
theorem noUnderflowSem_cons_false (v : List Bool) (x y : Fin 0 → List Bool) :
    noUnderflowSem (Fin.cons (false :: v) x) y =
      noUnderflowSem (Fin.cons v x) y := rfl

/-- A node bit fails when the counter over the remaining bitstring is
below two, and otherwise passes the verdict up. The counter is recomputed
from the normal tail, which is what makes the recognizer quadratic; the
step has one recursive value and it cannot carry both the counter and the
verdict. -/
theorem noUnderflowSem_cons_true (v : List Bool) (x y : Fin 0 → List Bool) :
    noUnderflowSem (Fin.cons (true :: v) x) y =
      (match (countSem (fun _ ↦ v) (fun _ ↦ [])).tail with
       | [] => []
       | true :: _ => noUnderflowSem (Fin.cons v x) y
       | false :: _ => noUnderflowSem (Fin.cons v x) y) := rfl

/-- The underflow test at an arbitrary environment is the test at the
canonical one. -/
theorem noUnderflowSem_env (f : Fin 1 → List Bool) (g : Fin 0 → List Bool) :
    noUnderflowSem f g = noUnderflowSem ![f 0] ![] := by
  have hf : f = ![f 0] := funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  have hg : g = ![] := Subsingleton.elim _ _
  conv_lhs => rw [hf, hg]
```

`noUnderflowSem_env` has no consumer inside this segment: `noUnderflowSem_gen`
runs at `Fin.cons`-shaped environments and `noUnderflowSem_eq`
specialises it directly. It ships because the spec's § The theorems names
it, and because it is the companion any consumer of `noUnderflowSem` at a
non-canonical environment needs — the role `countSem_env` plays for
`countSem_apply` here.

- [ ] **Step 6: Add the characterization**

Append. The `List.rec` runs at the `Fin.cons`-shaped environment, since
that is the shape the step lemmas are stated at; the case split inside
the `true` case is on whether `depth v - 1` is zero, which is what
decides the conditional's branch.

```lean
/-- The underflow test computes `BinTree.ok`, at any environment whose
first normal argument is the word. -/
theorem noUnderflowSem_gen : ∀ (w : List Bool) (x y : Fin 0 → List Bool),
    noUnderflowSem (Fin.cons w x) y = if BinTree.ok w then [true] else [] := by
  refine List.rec (motive := fun u ↦ ∀ (x y : Fin 0 → List Bool),
    noUnderflowSem (Fin.cons u x) y = if BinTree.ok u then [true] else [])
    (fun x y ↦ by rw [noUnderflowSem_nil]; simp) ?_
  intro b v ih x y
  cases b
  · rw [noUnderflowSem_cons_false, ih, BinTree.ok_cons_false]
  · rw [noUnderflowSem_cons_true, countSem_apply, BinTree.ok_cons_true]
    simp only [List.tail_replicate]
    obtain (h1 | ⟨m, hm⟩) :
        BinTree.depth v - 1 = 0 ∨ ∃ m, BinTree.depth v - 1 = m + 1 := by
      rcases Nat.eq_zero_or_pos (BinTree.depth v - 1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨BinTree.depth v - 2, by omega⟩
    · simp only [h1, List.replicate_zero]
      change ([] : List Bool) = _
      simp [show ¬ (2 ≤ BinTree.depth v) by omega]
    · simp only [hm, List.replicate_succ]
      change noUnderflowSem (Fin.cons v x) y = _
      rw [ih]
      simp [show 2 ≤ BinTree.depth v by omega]

/-- The underflow test computes `BinTree.ok`. -/
theorem noUnderflowSem_eq (w : List Bool) :
    noUnderflowSem ![w] ![] = if BinTree.ok w then [true] else [] :=
  noUnderflowSem_gen w _ _
```

Three bare `simp` calls appear above: one in the nil branch, and two in
the `true` case, each of the latter given an `omega`-established
hypothesis. All three were measured inside a theorem whose axioms are
`[propext, Quot.sound]`; Global constraint 16 is about a `simp` left to
decide an arithmetic `if` on its own, which is not what happens here.

- [ ] **Step 7: Build**

Run: `lake build`
Expected: exit 0, no diagnostics, no linter warnings. `unusedSimpArgs`
fires as an error on an over-specified `simp only` list; every list above
was measured as written.

- [ ] **Step 8: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: one path, `Tree.lean` modified.

---

## Task 5: The one-test and the recognizer

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`

**Interfaces:**

- Consumes: `countSem`, `noUnderflowSem`, `eqOneSem` and `isTreeSem` from
  Task 3; `countSem_eq` and `noUnderflowSem_eq` from Task 4;
  `BinTree.Valid` and `BinTree.valid_iff_exists_print` from
  `Geb.Mathlib.Data.Tree.Preorder`; `List.length_replicate`,
  `List.length_cons`, `if_pos`, `if_neg`, `absurd`, `funext`,
  `Subsingleton.elim` and `nofun`, all from Lean core
- Produces: `eqOneSem_env`, `eqOneSem_eq`, `isTreeSem_apply`,
  `isTreeSem_eq_singleton_iff_valid`, `isTreeSem_eq_singleton_iff_exists_print`

`isTreeSem_eq_singleton_iff_exists_print` is the segment's stated goal.

Every theorem below was measured to elaborate as written, at v4.33.0-rc2,
while this plan was being written, as Task 4's were. The spec's
§ Verification evidence records `isTree`'s two correctness theorems as
not yet measured; that was the state when the spec was written, and the
spec has since been amended to say so.

- [ ] **Step 1: Create the change**

```bash
jj new -m "feat(computability): characterize the recognizer against Valid"
```

- [ ] **Step 2: Add the one-test's lemmas**

Append inside the `public section`:

```lean
/-- The one-test at an arbitrary environment is the test at the canonical
one. -/
theorem eqOneSem_env (f : Fin 0 → List Bool) (g : Fin 1 → List Bool) :
    eqOneSem f g = eqOneSem ![] ![g 0] := by
  have hf : f = ![] := Subsingleton.elim _ _
  have hg : g = ![g 0] := funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  conv_lhs => rw [hf, hg]

/-- The one-test accepts exactly the unary numerals of length one. It is
not a recursion, so its three cases are decided by matching. -/
theorem eqOneSem_eq (u : List Bool) :
    eqOneSem ![] ![u] = if u.length = 1 then [true] else [] := by
  match u with
  | [] => rfl
  | [b] => cases b <;> rfl
  | b :: c :: v =>
    cases b <;> cases c <;>
      (change ([] : List Bool) = _
       rw [if_neg (by simp only [List.length_cons]; omega)])
```

The last case discharges its side condition by `omega` rather than by a
bare `simp`, which was measured to add `Classical.choice` — Global
constraint 16.

- [ ] **Step 3: Add the recognizer's unfolding lemma**

Append. Unlike `noUnderflow`'s guard, the families here may be written
with vector notation: `eqOne` consumes its safe environment at the
literal index `0`, so `Matrix.cons` reduces.

```lean
/-- One step of the recognizer: the underflow test decides whether the
counter is consulted at all. -/
theorem isTreeSem_apply (w : List Bool) :
    isTreeSem ![w] ![] =
      (match noUnderflowSem ![w] ![] with
       | [] => []
       | true :: _ => eqOneSem (fun _ ↦ []) (fun _ ↦ countSem ![w] ![])
       | false :: _ => eqOneSem (fun _ ↦ []) (fun _ ↦ countSem ![w] ![])) := rfl
```

- [ ] **Step 4: Add the two correctness theorems**

Append:

```lean
/-- The recognizer accepts exactly the words satisfying `BinTree.Valid`. -/
theorem isTreeSem_eq_singleton_iff_valid (w : List Bool) :
    isTreeSem ![w] ![] = [true] ↔ BinTree.Valid w := by
  by_cases h : BinTree.ok w = true
  · rw [isTreeSem_apply, noUnderflowSem_eq, if_pos h]
    change eqOneSem (fun _ ↦ []) (fun _ ↦ countSem ![w] ![]) = [true] ↔ _
    rw [eqOneSem_env]
    simp only [eqOneSem_eq, countSem_eq, List.length_replicate]
    by_cases hd : BinTree.depth w = 1
    · rw [if_pos hd]
      exact ⟨fun _ ↦ ⟨h, hd⟩, fun _ ↦ rfl⟩
    · rw [if_neg hd]
      refine ⟨fun hw ↦ absurd hw (by nofun), ?_⟩
      rintro ⟨-, hd'⟩
      exact absurd hd' hd
  · rw [isTreeSem_apply, noUnderflowSem_eq, if_neg h]
    refine ⟨fun hw ↦ absurd hw (by nofun), ?_⟩
    rintro ⟨h', -⟩
    exact absurd h' h

/-- The recognizer accepts exactly the preorder spellings of binary
trees. -/
theorem isTreeSem_eq_singleton_iff_exists_print (w : List Bool) :
    isTreeSem ![w] ![] = [true] ↔ ∃ t, BinTree.print t = w :=
  (isTreeSem_eq_singleton_iff_valid w).trans (BinTree.valid_iff_exists_print w)
```

Both splits are on decidable propositions, which is what keeps them
choice-free — `BinTree.ok w = true` and `BinTree.depth w = 1` are `Bool`
and `Nat` equations. The tactic is not what decides this: measured,
`by_contra` on a decidable proposition is also axiom-free, and `by_cases`
on a proposition with no `Decidable` instance pulls in
`Classical.choice`. The anonymous constructor `⟨h, hd⟩` and the `rintro`
patterns build and destructure `BinTree.Valid w` through its definitional
unfolding to a conjunction.

- [ ] **Step 5: Extend the module docstring**

The summary paragraph and `## Main statements` now have their remaining
content. Replace the first paragraph of the module docstring — do not
append, or its `[BellantoniCook1992]` sentence appears twice — with:

```markdown
Four expressions of `B` deciding whether a bitstring is the preorder
spelling of a binary tree, and their correctness against the `Valid`
predicate of the encoding. Composed with `BinTree.valid_iff_exists_print`,
`isTreeSem_eq_singleton_iff_exists_print` states that an expression of `B` accepts
exactly the spellings of trees. `B` is a characterization of the
polynomial-time functions [BellantoniCook1992], which is used and not
proved here, so the membership test lies in that class without a separate
complexity argument.
```

and append to `## Main statements`:

```markdown
* `BellantoniCook.eqOneSem_eq` — `eqOne` accepts exactly the unary
  numerals of length one.
* `BellantoniCook.isTreeSem_eq_singleton_iff_valid` — `isTree` accepts exactly the
  words satisfying `BinTree.Valid`.
* `BellantoniCook.isTreeSem_eq_singleton_iff_exists_print` — equivalently, exactly
  the spellings of trees.
```

`isTree` gets no environment-normalization lemma. The spec's § Unfolding
asks for one per expression whose meaning is named at a non-canonical
environment; `isTreeSem` is only ever applied at `![w] ![]`, so an
`isTreeSem_env` would have no consumer and no caller.

- [ ] **Step 6: Build and lint**

Run: `lake build && lake lint`
Expected: exit 0 from each. `lake lint` runs
`GebMeta.detectNonstandardAxiom` over the module, which is now in `Geb`'s
import closure through `Computability.lean`; a failure names any
declaration reaching outside `{propext, Quot.sound}`.

- [ ] **Step 7: Re-measure the axiom groups**

Run `#print axioms` on each of the 40 declarations of `Tree.lean` — the
23 definitions of Task 3 and the 17 theorems of Tasks 4 and 5 —
through the `lean-lsp` MCP's `lean_run_code`. (A file written outside the
lake package cannot resolve `Geb.*` imports, so a throwaway module under
a temporary directory is not an alternative.)

Expected, from the measurement taken while writing this plan — treat a
disagreement as a finding, not as a reason to adjust the expectation:

- no axiom: `zeroAt` — one.
- `[propext]`: `oneAt`, `incRaw`, `decRaw`, `countRaw`, `guardRaw`,
  `nuTrueStepRaw`, `noUnderflowRaw`, `eqOneInnerRaw`, `eqOneRaw`,
  `isTreeRaw` — ten, every raw `sig`-tree other than `zeroAt`.
- `[propext, Quot.sound]`: everything else — the four expressions, the
  four `BCOf` witnesses, the four `Sem` ascriptions and all seventeen
  theorems, twenty-nine in all.

`compChildren` depends on no axiom, but it lives in `Basic.lean` after
Task 2 and is not one of these 40. Nothing lies outside
`{propext, Quot.sound}`. If `Classical.choice` appears, the culprit is an
arithmetic side goal closed by a bare `simp`; see Global constraint 16.

- [ ] **Step 8: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: one path, `Tree.lean` modified.

---

## Task 6: The test module

**Files:**

- Create: `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`
- Modify: `GebTests/Mathlib/Computability/BellantoniCook.lean`

**Interfaces:**

- Consumes: `BellantoniCook.isTreeSem`, `BellantoniCook.countSem` and
  `BellantoniCook.isTreeOf` from
  `Geb.Mathlib.Computability.BellantoniCook.Tree`, and
  `BellantoniCook.BCOf` from `…BellantoniCook.Basic`, which that module
  publicly imports
- Produces: `isTreeArity : BCOf 1 0`, the named `def` the spec's § Tests
  calls for, and eight assertions

Every assertion below was measured by `rfl`. The spec's § Tests asks for
four rejections: the empty word, a word failing `ok` alone, a word
failing the depth conjunct alone, and a word with an accepted spelling's
bit counts in the wrong order. Those four are not a partition of the
failure modes — `[]` and `[false, false]` both fail the depth conjunct
alone, and `[false, false, true]` fails both conjuncts — and the two that
separate the conjuncts are the non-vacuity control for the conjunction in
`isTree`: without them no assertion would distinguish `noUnderflow` from
the counter test.

- [ ] **Step 1: Create the change**

```bash
jj new -m "test(computability): assert the recognizer and its rejections"
```

- [ ] **Step 2: Write the test module**

Create `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.BellantoniCook.Tree

/-!
# The tree recognizer on worked bitstrings

The recognizer accepting three spellings and rejecting four words — the
empty word, a word failing the underflow test alone, a word failing the
counter test alone, and a permutation of an accepted spelling — together
with the counter on a word whose depth exceeds one.

## Main statements

The eight assertions below.

## Tags

Bellantoni-Cook, polytime, binary tree, preorder, recognizer
-/

set_option linter.privateModule false

open BellantoniCook

/-- The recognizer at its declared arity, named so that this module
references a constant of the module under test. -/
def isTreeArity : BCOf 1 0 := isTreeOf

/-- The spelling of the leaf is accepted. -/
theorem isTreeSem_print_leaf : isTreeSem ![[false]] ![] = [true] := rfl

/-- The spelling of the two-leaf node is accepted. -/
theorem isTreeSem_print_node : isTreeSem ![[true, false, false]] ![] = [true] :=
  rfl

/-- The spelling of an asymmetric tree of two nodes and three leaves is
accepted. -/
theorem isTreeSem_print_asymmetric :
    isTreeSem ![[true, true, false, false, false]] ![] = [true] := rfl

/-- The empty word is rejected: it leaves no tree on the stack. -/
theorem isTreeSem_nil : isTreeSem ![([] : List Bool)] ![] = [] := rfl

/-- A word failing the underflow test alone is rejected. Its depth is
one, so the counter half of the conjunction accepts it. -/
theorem isTreeSem_underflow : isTreeSem ![[false, true, false]] ![] = [] := rfl

/-- A word failing the counter test alone is rejected. It satisfies the
underflow test, so the underflow half of the conjunction accepts it. -/
theorem isTreeSem_depth : isTreeSem ![[false, false]] ![] = [] := rfl

/-- A word with the bit counts of an accepted spelling, in the wrong
order, is rejected. It fails both conjuncts. -/
theorem isTreeSem_permuted : isTreeSem ![[false, false, true]] ![] = [] := rfl

/-- The counter on a word whose depth exceeds one, separating the counter
from the recognizer. -/
theorem countSem_two_leaves : countSem ![[false, false]] ![] = [true, true] :=
  rfl
```

- [ ] **Step 3: Add the import to the test index**

In `GebTests/Mathlib/Computability/BellantoniCook.lean`, add below the
`Basic` line:

```lean
import GebTests.Mathlib.Computability.BellantoniCook.Tree
```

- [ ] **Step 4: Build the tests and run them**

Run: `lake build GebTests && lake test && lake lint -- GebTests`
Expected: exit 0 from each. A failing `rfl` here, with `Tree.lean`
building, is an exposure failure across the module boundary: check that
the declaration named is `@[expose]` inside `Tree.lean`'s
`public section`.

- [ ] **Step 5: Confirm `lake shake` does not report the module**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: the new test module is absent from the reported list. Its eight
theorem statements reference `isTreeSem` and `countSem`, and
`isTreeArity` names `isTreeOf` and `BCOf`, so the import leaves constants
in the olean for `shake` to see; `shake`'s known blind spot is an
anonymous `example`, which this module does not use. A
`PANIC at Option.get!` trace from `Lake.Shake.visitModule` may appear
again here; it exits 0, and only a non-zero exit is a real failure.

- [ ] **Step 6: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: two paths — the new test module added, the test index modified.

---

## Task 7: Documentation

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`
- Modify, under one branch of Step 4 only:
  `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` (confirmed) or
  `docs/references.bib` (refuted)

**Interfaces:**

- Consumes: the axiom measurement from Task 5 Step 7
- Produces: the persistent record of the module, the follow-on work, and
  the only persistent citers of `[Hofmann2000]` and `[Marion2003]`

The spec's § Deferred items are genuine follow-on work and `TODO.md` is
where they persist once the spec is removed. Two of them cite
`[Hofmann2000]` and `[Marion2003]`, which is what keeps those two
bibliography entries from citing nothing: `Tree.lean`'s own
`## References` names only `[HeraudNowak2011]` and `[BellantoniCook1992]`.

- [ ] **Step 1: Create the change**

```bash
jj new -m "doc: record the tree recognizer and its follow-on work"
```

- [ ] **Step 2: Correct the three stale paths left by the restructure**

Task 2 renamed `Geb/Mathlib/Computability/BellantoniCook.lean` to
`.../BellantoniCook/Basic.lean`. After the restructure that path is a
bare directory index, and three places in the two persistent documents
still name it.

```bash
grep -rn "Computability/BellantoniCook" --include=*.md .
```

returns far more than three, because this plan and this segment's spec
both discuss the path at length; those two are removed by Task 9 and are
not to be edited. The three to correct, each to
`Geb/Mathlib/Computability/BellantoniCook/Basic.lean`, are:

- `docs/index.md`, the bullet beginning "the function class `B`". Change
  its path, and extend it for `compChildren`, which Task 2 Step 3 added
  to that module: append to its content summary
  "`compChildren` orders a `comp` node's children as `Direction` gives
  them." and, to its axiom sentence, that `compChildren` depends on no
  axiom.
- `TODO.md` § Bellantoni-Cook, the sentence "Three items, in dependency
  order, over …".
- `TODO.md` § Triggers, the bullet on `finEnumFin` and
  `finEnumCompDirection`, whose closing sentence says where they are
  `scoped`.

- [ ] **Step 3: Add the new `docs/index.md` bullet**

Add immediately after the corrected `Basic.lean` bullet:

```markdown
- `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — a recognizer
  for the preorder spellings of binary trees, as four expressions of `B`.
  `count` is a `safeRec` returning the stack depth in unary;
  `noUnderflow` is a `safeRec` whose node-bit step guards on the counter
  recomputed from the normal tail; `eqOne` tests a unary numeral for
  one; `isTree` is their conjunction. `countSem_eq` and
  `noUnderflowSem_eq` identify the first two with `BinTree.depth` and
  `BinTree.ok`; `eqOneSem_eq` identifies the third with a length test;
  `isTreeSem_eq_singleton_iff_valid` identifies the recognizer with
  `BinTree.Valid`, and `isTreeSem_eq_singleton_iff_exists_print`
  composes that with `BinTree.valid_iff_exists_print` to give acceptance
  of exactly the spellings of trees. The recognizer is a single scan rather than a
  recursive descent, a descent needing recursion on a safe argument,
  which the class forbids; the counter is recomputed at each level, so
  the scan is quadratic rather than linear, and [HeraudNowak2011] § 7's
  translation from Cobham's class is the recorded replacement. Depends
  on `Geb.Mathlib.Computability.BellantoniCook.Basic`,
  `Geb.Mathlib.Data.PFunctor.Slice.Decidable` and
  `Geb.Mathlib.Data.Tree.Preorder`. `zeroAt` depends on no axiom; the ten
  other raw `sig`-trees, `oneAt` among them, on `propext`; the four
  expressions, their arity witnesses, the ascriptions of their meanings
  and every theorem on `propext` and `Quot.sound`.
```

Correct any axiom claim above that Task 5 Step 7 measured differently.

- [ ] **Step 4: Attempt the Marion attribution check**

The spec's § Deferred item 5 asks that the Marion attribution be verified
against `[Marion2003]` directly or dropped. Spend one bounded attempt:
search for *Marion, Analysing the implicit complexity of programs*,
Information and Computation 183(1):2-18, through `theorem_search` and
`search_papers`, and if a copy is reachable, check whether it states that
polynomiality extends to constructors `s₁ × ⋯ × sₙ → s` under the
constraint that `s` occurs at most once among the `sᵢ`.

Three outcomes, and each keeps `docs/references.bib` internally
consistent:

- **No copy reachable.** Keep item 5 of Step 5 as written. It cites
  `[Marion2003]`, which is what keeps the bibliography entry from citing
  nothing.
- **Confirmed.** The attribution is then established mathematics about a
  neighbouring system, not follow-on work, so it does not belong in
  `## Next up`. Delete item 5, renumber the item after it, change Step 5's
  opening line to "Five items over …", and instead add the citation to
  `Tree.lean`'s module docstring — one sentence in
  `## Implementation notes` recording the neighbouring constraint, and
  `[Marion2003]` added to its `## References`. That makes `Tree.lean` the
  persistent citer.
- **Refuted.** Delete item 5, renumber the item after it, change Step 5's
  opening line to "Five items over …", and remove the `Marion2003` entry
  from `docs/references.bib` in this same commit. Nothing in the design
  depends on it.

- [ ] **Step 5: Add the `TODO.md` subsection**

Add as the last `###` subsection of `## Next up` in `TODO.md`:

```markdown
### The Bellantoni-Cook tree recognizer

Six items over `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`.

1. The tree recursor — the analogue of `safeRec` on the encoded tree,
   whose step receives the two subtree spellings in normal position and
   the two recursive values in safe position. Its soundness is a new
   theorem, not a corollary: [HeraudNowak2011] Proposition 2 is proved by
   induction over the constructors of `B`, and a tree recursor is a
   further constructor. The expected argument is that the step inherits
   the maximum bound, giving
   `|f(node l r)| ≤ p(|l| + |r|) + max(|f l|, |f r|, |ā|)`, and induction
   on height gives a polynomial. Depends on this recognizer's scan for
   the split point.
2. Apply the `C → B` translation of [HeraudNowak2011] § 5, Theorem 2 to
   the recognizer, removing the quadratic recomputation
   `noUnderflow`'s step performs. Depends on § Bellantoni-Cook item 3,
   which is where Cobham's class and the translation itself are built;
   this item is only their consumer.
3. Extract the unfolding and environment lemmas into their own module
   once a second Bellantoni-Cook function needs them.
4. The labelled variant, tracking the corresponding item in
   § Binary trees and their preorder encoding.
5. Verify against [Marion2003] directly, rather than through
   [DalLagoMartiniZorzi2010]'s report of it, that polynomiality extends
   to constructors `s₁ × ⋯ × sₙ → s` under the constraint that `s`
   occurs at most once among the `sᵢ` — or drop the attribution together
   with the bibliography entry. The paper was not reachable when the
   recognizer was written; nothing in the design depends on it.
6. A linear-logic strand. [Hofmann2000]'s abstract states soundness for
   recursion over trees in a system it describes as modally and linearly
   typed, and the light and soft linear logics tune one family of
   systems to several complexity classes. The motivation to record is
   that tunability. Against it: those systems are reported to need more
   elaborate syntax or encodings than the function algebras, and a
   well-typed term there does not carry its own bound — the type
   derivation is needed to extract it, which tells against the
   representation strategy used here, in which the program is the term.
   Any pursuit of this item begins by verifying both claims against
   primary sources.
```

- [ ] **Step 6: Add the remaining-non-uniformity trigger**

This restructure leaves two directories without an index of their own:
`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/` and its test-side
counterpart, each indexed two levels up by `CategoryTheory.lean` while a
content-bearing `FreeCoprodCompDisc.lean` occupies the path where the
index belongs. Fixing them is a separate concern and a separate branch.
Add as a bullet of `## Triggers (do when condition fires)` in `TODO.md`:

```markdown
- **`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/` gains a second
  module, or either `FreeCoprodCompDisc.lean` is edited for another
  reason**: split `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  and `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` into
  directory indexes over `Basic.lean` files, as
  `Geb/Mathlib/Computability/BellantoniCook.lean` was split. Both
  `FreeCoprodCompDisc/` directories currently have no index of their own:
  `CategoryTheory.lean` imports the module and its `NatTrans` sibling
  directly, indexing two levels, which is what CONTRIBUTING.md § Repo
  structure's "one indexing file per directory" rules out.
```

- [ ] **Step 7: Regenerate the tables of contents and lint the Markdown**

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` and `Summary: 0 issues`.

- [ ] **Step 8: Confirm the commit's contents**

Run: `jj diff --stat -r @`
Expected: `docs/index.md` and `TODO.md`, plus `docs/references.bib` and
`Tree.lean` only under the corresponding branches of Step 4.

---

## Task 8: The pre-push gate

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
introduced it rather than adding a commit here.

- [ ] **Step 1: Run the full checklist**

Run: `scripts/pre-push.sh`
Expected: every step passes and the script exits 0.

The checklist covers, among other steps, `lake exe cache get`,
`lake build`, `lake test`, `lake lint`, `lake build GebTests`,
`lake lint -- GebTests`, `lake shake`, `scripts/lint-imports.sh`, the
repository's script smoke tests, the commit-message check over this
branch's commits, and the `doctoc` and `markdownlint-cli2` checks. It
also emits non-fatal reminders, which do not affect its exit status.
Nothing further need be run separately.

`scripts/lint-imports.sh` is the floodgate test: it rejects a forbidden
import in `Geb/Mathlib/` or `GebTests/Mathlib/`, and any occurrence of
the `Geb.Mathlib.` or `GebTests.Mathlib.` prefix outside an `^import`
line — including in the new module docstrings.

`lake shake` may print a `PANIC at Option.get!` trace from
`Lake.Shake.visitModule` when the first module under a new
`GebTests/Mathlib/<Dir>/` appears. It exits 0 when that happens; a
non-zero exit is a real failure.

- [ ] **Step 2: Confirm the commit-message check saw both segments**

At this point `@` is above `feat/binary-tree-preorder`, so
`jj log -r 'fork_point(main | @)..@ ~ merges()'` covers both segments'
commits — fifteen of them: segment 1's seven, and this segment's spec,
plan and Tasks 2 through 7. Read the printed list and confirm every
subject is imperative,
uncapitalised, unpunctuated, at most 72 characters, and carries one of
the nine allowed types.

- [ ] **Step 3: Confirm the gate left nothing behind**

Run: `jj diff --stat -r @`
Expected: the same paths Task 7 Step 8 reported. `Geb/Cslib.lean`
appearing here means `scripts/tests/test-lake-shake.sh` did not restore
it; restore it before continuing.

---

## Task 9: Remove the spec, the plan and the measured Lean

**Files:**

- Delete: `docs/superpowers/specs/2026-08-06-bc-tree-recognizer-design.md`
- Delete: `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md`
- Delete: `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-handoff.md`

**Interfaces:**

- Consumes: nothing
- Produces: a branch whose working tree carries only persistent content,
  and a bookmark on its head

`CONTRIBUTING.md` § Concern shape: specs and plans record how the current
state was reached, not what it is. The third file is the measured Lean
the expressions were rebuilt from; its own § Purpose and lifespan says it
is removed in the same commit, and everything in it that persists is now
in `Tree.lean`. All three remain reachable in this segment's spec and
plan commits.

- [ ] **Step 1: Create the removal change**

```bash
jj new -m "doc: remove the tree-recognizer spec, plan and measured Lean"
```

- [ ] **Step 2: Delete the three files**

```bash
rm docs/superpowers/specs/2026-08-06-bc-tree-recognizer-design.md
rm docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md
rm docs/superpowers/plans/2026-08-06-bc-tree-recognizer-handoff.md
```

- [ ] **Step 3: Confirm nothing else changed and nothing is left behind**

```bash
jj status
ls docs/superpowers/specs docs/superpowers/plans
```

Expected: under `Working copy changes:`, three `D` lines and nothing
else; and two empty directories.

- [ ] **Step 4: Re-check the Markdown**

```bash
doctoc --dryrun --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` and `Summary: 0 issues`.

- [ ] **Step 5: Move the bookmark to this commit**

```bash
jj bookmark set feat/bc-tree-recognizer -r @
```

- [ ] **Step 6: Confirm the two segments**

```bash
jj log -r 'main::feat/bc-tree-recognizer' --no-pager \
  -T 'change_id.short() ++ "  " ++ bookmarks ++ "  " ++ description.first_line() ++ "\n"'
jj diff --stat -r 'main..feat/binary-tree-preorder'
jj diff --stat -r 'feat/binary-tree-preorder..feat/bc-tree-recognizer'
```

Expected: two bookmarks on two removal commits; the first diff names no
path under `docs/superpowers/` and no Bellantoni-Cook path; the second
names the six `.lean` paths of § File structure plus `docs/references.bib`,
`docs/index.md` and `TODO.md`, and no path under `docs/superpowers/`.

- [ ] **Step 7: Confirm segment 1 builds on its own, and return**

```bash
jj new feat/binary-tree-preorder
lake build && lake test
```

Expected: exit 0. This is the floodgate check that segment 1 is an
independently shippable PR candidate: if it fails, something of segment 2
has leaked below the bookmark. It rebuilds the oleans on both sides of
the boundary, so allow for two full builds.

```bash
jj edit feat/bc-tree-recognizer
```

That is enough on its own: `jj edit` moves `@` away from the throwaway
change, and jj discards an empty, undescribed working-copy commit when
the working copy leaves it. `jj abandon @` beforehand would be a no-op —
it replaces the working-copy commit with a fresh empty one on the same
parent.

- [ ] **Step 8: Confirm the stack has one head per segment**

`jj log -r 'main::feat/bc-tree-recognizer'` cannot answer this: `x::y`
intersects descendants of `x` with ancestors of `y`, so a sibling head
off `feat/binary-tree-preorder` is excluded by construction. Ask for the
heads instead:

```bash
jj log -r 'heads(feat/binary-tree-preorder::)' --no-pager \
  -T 'change_id.short() ++ "  " ++ bookmarks ++ "  " ++ description.first_line() ++ "\n"'
```

Expected: exactly one commit, the one carrying `feat/bc-tree-recognizer`.

- [ ] **Step 9: Check this commit's own message**

Task 8's gate ran before this commit existed, so the checklist never saw
its subject. Run the check again over both completed segments:

```bash
jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
  -T 'description.first_line() ++ "\n"' | bash scripts/check-commit-msg.sh
```

Expected: exit 0 over sixteen subjects — segment 1's seven and this
segment's nine.

No push. AGENTS.md § No `jj git push` without user line-by-line review:
every push, including a first creation, waits on the user reading the
diff.
