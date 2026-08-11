# Absorbing `BinTree` into the two-symbol ranked term algebra — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [What is already in the working tree](#what-is-already-in-the-working-tree)
- [File map](#file-map)
- [Task 1: Commit the counter form](#task-1-commit-the-counter-form)
- [Task 2: Commit the residue-lemma correction](#task-2-commit-the-residue-lemma-correction)
- [Task 3: Commit the Cobham restatement](#task-3-commit-the-cobham-restatement)
- [Task 4: Restate the Bellantoni-Cook recognizer](#task-4-restate-the-bellantoni-cook-recognizer)
- [Task 5: Restate the two test mirrors](#task-5-restate-the-two-test-mirrors)
- [Task 6: Delete the absorbed modules](#task-6-delete-the-absorbed-modules)
- [Task 7: Restate the catalogue and the roadmap](#task-7-restate-the-catalogue-and-the-roadmap)
- [Task 8: Dispose of the two plan documents](#task-8-dispose-of-the-two-plan-documents)
- [Task 9: Remove this plan and the spec, and gate the branch](#task-9-remove-this-plan-and-the-spec-and-gate-the-branch)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Leave one unlabelled binary-tree encoding under `Geb/Mathlib/` —
`RankedAlphabet.Binary.binRanked.Term` with `spell`, `parse` and `Valid` —
by deleting `BinTree`, its preorder encoding and the equivalence bridging
them, and restating every consumer over the ranked development.

**Architecture:** `Ranked/Binary.lean` gains the validity scan's counter form
at width one (`depth` and `ok` as projections of `scanFinal`, plus the
`cons`-lemmas that give them content). The two recognizers, which were stated
over `BinTree.ok`/`BinTree.depth`/`BinTree.Valid`, are restated over that
counter form and over `binRanked.Valid`. `Cobham/RankedTree.lean`'s bridge
theorem then relates two statements about one predicate and collapses. The
deletions follow last, by which point nothing names what they remove.

**Tech Stack:** Lean 4 (toolchain pinned by `lean-toolchain`), `lake`,
mathlib, `doctoc`, `markdownlint-cli2`.

**Governing spec:**
[docs/superpowers/specs/2026-08-11-tree-absorb-bintree-design.md](../specs/2026-08-11-tree-absorb-bintree-design.md).
Where this plan and the spec disagree, the spec is wrong and both are fixed.

## Global constraints

- **Build discipline.** `lake build` and `lake test` only. Never
  `lake env lean`; avoid `lake clean`. Run Lean alone: a second concurrent
  Lean process, the `lean-lsp` tools included, corrupts package `.trace`
  files and fails unrelated mathlib targets.
- **Line length** 100 characters in `.lean`; in `.md`, whatever
  `markdownlint-cli2` enforces — 80 in prose, with tables and fenced code
  exempt by `.markdownlint-cli2.jsonc`. Indentation two spaces, no tabs.
- **No `sorry`, no `admit`, no `noncomputable`, no `native_decide`.**
  `Classical` is minimised; every declaration this branch adds or edits must
  measure within `{propext, Quot.sound}`, which `lake lint` checks.
- **Bound `Nat` and `Fin` arithmetic by `omega` over named hypotheses, or by
  case analysis** — never by the single lemma that states the bound.
- **A docstring is mandatory** on every `def`, `structure`, `class`,
  `instance`, every field, and every theorem of public interest; module
  docstrings carry their sections in the order
  `# Title`, summary, `## Main definitions`, `## Main statements`,
  `## Notation`, `## Implementation notes`, `## References`, `## Tags`, each
  present when it has content and omitted when vacuous.
- **No counts of a population the project keeps adding to** in committed
  text; name the members or state the property they share.
- **Commit messages**: `type(scope): imperative subject`, lower-case, no
  trailing period, under 72 characters where possible, type drawn from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- **VCS**: `jj` for every state-mutating operation. Never a mutating `git`
  subcommand. Commit freely; **do not push** — pushing requires the user's
  line-by-line review.
- **Markdown**: every committed `.md` passes `markdownlint-cli2` and carries
  a `doctoc` table of contents when it has more than one `##` heading.

Lean has no failing-test-first cycle in the `pytest` sense. The equivalent
discipline, which every task below follows, is: state the target, make the
edit, build and read the *specific* expected failure or success, then lint,
then commit. Where a step expects a failure, the expected message is given;
an implementer who sees a different failure has diverged and should stop.

## What is already in the working tree

Four files carry verified, uncommitted work. Tasks 1 to 3 commit it; they are
separate tasks because they are separate concerns and each must be a
separately reviewable commit.

```text
Geb/Mathlib/Data/Tree/Ranked/Binary.lean        +140   Task 1
Geb/Mathlib/Data/Tree/Ranked/Preorder.lean      +2 -1  Task 2
Geb/Mathlib/Computability/Cobham/Tree.lean      ~112   Task 3
Geb/Mathlib/Computability/Cobham/RankedTree.lean  ~9   Task 3
```

`lake build` passes and `lake lint` passes over `Geb` and over `GebTests`
with all four in place. Confirm that before starting, and do not re-derive
the content: read it, check it against the spec's § What `Ranked/Binary.lean`
gains, and commit it.

## File map

| File | Task | Responsibility after the branch |
| --- | --- | --- |
| `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` | 1, 6 | the two-symbol alphabet, its constructors, and the counter form of its scan |
| `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` | 2, 6 | the generic encoding, descent and scan; gains the `DyckWord` comparison and the fuel argument |
| `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` | 6 | ranked alphabets and their terms; docstring loses its `BinTree` comparisons |
| `Geb/Mathlib/Computability/Cobham/Tree.lean` | 3 | the two-symbol recognizer, stated over the counter form and `binRanked.Valid` |
| `Geb/Mathlib/Computability/Cobham/RankedTree.lean` | 3 | the generic recognizer; its bridge theorem collapses |
| `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` | 4 | the same, in `B` |
| `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` | 5 | worked words for the alphabet, its spelling, its descent and its counter form |
| `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` | 5 | the shared fixtures; its sweep inventory loses the retired mirror |
| `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean` | 5 | worked words for the `B` recognizer; three names lose `print` |
| `Geb/Mathlib/Data/Tree/Binary.lean` | 6 | **deleted** |
| `Geb/Mathlib/Data/Tree/Preorder.lean` | 6 | **deleted** |
| `GebTests/Mathlib/Data/Tree/Preorder.lean` | 6 | **deleted** |
| `Geb/Mathlib/Data/Tree.lean`, `GebTests/Mathlib/Data/Tree.lean` | 6 | directory indices, each losing imports |
| `docs/index.md`, `TODO.md` | 7 | the catalogue and the roadmap |
| `docs/superpowers/plans/2026-08-10-*.md` | 8 | the session handoff and the workstream record |

---

## Task 1: Commit the counter form

**Files:**

- Modify (already edited): `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.scanFinal`, `scanStep`, `scanFinal_cons`,
  `length_buf_scanFinal_lt`, `depth_scanFinal_le_length`,
  `valid_iff_scanFinal`, `arOf`, `decodeBits` — all from
  `Ranked/{Preorder,Code}.lean`, unchanged by this branch.
- Produces, in `namespace RankedAlphabet.Binary`, the names Tasks 3 and 4
  consume:
  - `depth : List Bool → ℕ`, `ok : List Bool → Bool`
  - `depth_le_length (w) : depth w ≤ w.length`
  - `valid_iff_ok_and_depth_eq_one (w) :`
    `binRanked.Valid w ↔ ok w = true ∧ depth w = 1`
  - `@[simp] ok_cons_false (w) : ok (false :: w) = ok w`
  - `@[simp] ok_cons_true (w) :`
    `ok (true :: w) = (ok w && decide (2 ≤ depth w))`
  - `depth_cons_false_of_ok (w) (h : ok w = true) :`
    `depth (false :: w) = depth w + 1`
  - `depth_cons_true_of_ok_of_two_le_depth (w) (h : ok w = true)`
    `(h2 : 2 ≤ depth w) : depth (true :: w) = depth w - 1`
  - and, used only within this module: `buf_scanFinal_eq_nil`,
    `decide_length_eq_width`, `arOf_decodeBits_false`, `arOf_decodeBits_true`,
    `scanStep_false_of_live_of_buf_nil`,
    `scanStep_true_of_live_of_buf_nil_of_two_le_depth`,
    `scanStep_true_of_live_of_buf_nil_of_depth_lt_two`, `scanStep_of_not_live`.

- [ ] **Step 1: Confirm the working tree is in the expected state**

```bash
jj diff --stat
```

Expected: four modified files, as § What is already in the working tree
lists. If `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` is not among them, this
plan's premise is broken — stop and re-read the spec's § Appendix.

- [ ] **Step 2: Read the added declarations against the spec**

Read `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` between `spell_node` and
`ofBinTree`. Check each declaration against the spec's § What
`Ranked/Binary.lean` gains table: sixteen declarations, in that order, with
those statements. Check the module docstring carries them under
`## Main definitions` and `## Main statements`, and that Implementation notes
carry the `@[expose]`, `@[simp]`, `cases b` and `scanStep_of_not_live`
placement reasons.

- [ ] **Step 3: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Binary
```

Expected: `Built Geb.Mathlib.Data.Tree.Ranked.Binary`, no errors.

Note what this build covers. `jj commit <paths>` commits the named paths and
leaves the rest in the new working copy, so this build sees Tasks 2 and 3's
edits as well: it verifies more than the commit, not the commit alone.
That is sound here, and the check is worth stating so a reviewer can re-run
it: the commit leaves the previous `Cobham/*.lean`, which still resolve
`BinTree.ok`, `BinTree.depth` and `RankedAlphabet.Binary.valid_iff` from the
modules this branch has not yet deleted; the previous `Cobham/Tree.lean` does
not import `Ranked/Binary.lean` at all; and the previous
`Cobham/RankedTree.lean`, which does, contains no occurrence of
`RankedAlphabet.Binary.ok` or `.depth`, so the two new `@[simp]` lemmas have
no head symbol to fire on. The same holds of Task 2, whose change is
proof-internal. From Task 4 on, the working copy and the commit coincide.

- [ ] **Step 4: Check the axioms**

```bash
lake lint
```

Expected: `-- Linting passed for Geb.` A failure here names a declaration
depending on an axiom outside `{propext, Quot.sound}`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Binary.lean \
  -m "feat(tree): give the two-symbol scan's counter form"
```

---

## Task 2: Commit the residue-lemma correction

**Files:**

- Modify (already edited): `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`

This is a one-line rule-compliance fix that the branch makes in passing,
because it edits this module anyway in Task 6. It is unrelated to absorbing
`BinTree` and so takes its own commit.

**Interfaces:** none; the statement proved is unchanged.

- [ ] **Step 1: Read the change**

```bash
jj diff Geb/Mathlib/Data/Tree/Ranked/Preorder.lean
```

Expected, inside `exists_spell_append_of_live_of_buf_nil_of_one_le_depth`'s
`Nat.rec` base case:

```lean
-      have hnil : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
+      have hzero : w.length ≤ 0 := hw
+      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
```

`Nat.le_zero.mp` is the single lemma stating its bound, which
`docs/rules/lean-coding.md` § Constructive-only Lean code's fourth rule bars.
`by omega` alone does not work: the `Nat.rec` base case presents the bound as
`w.length ≤ Nat.zero`, and `omega` treats the unreduced `Nat.zero` as an
atom. Naming the bound at a literal first is the rule's own form.

- [ ] **Step 2: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: built, and `-- Linting passed for Geb.` The lint matters here
specifically: `omega` proving a non-`False` goal can pull in
`Classical.choice`.

- [ ] **Step 3: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "style(tree): bound the descent's base case by omega"
```

---

## Task 3: Commit the Cobham restatement

**Files:**

- Modify (already edited): `Geb/Mathlib/Computability/Cobham/Tree.lean`
- Modify (already edited): `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes Task 1's counter form.
- Produces `Cobham.isTreeSem_eq_singleton_iff_exists_spell`, replacing
  `isTreeSem_eq_singleton_iff_exists_print`; and
  `Cobham.isTreeSem_eq_singleton_iff_valid` now stated over
  `binRanked.Valid`. Task 4 mirrors both in `BellantoniCook`.

- [ ] **Step 1: Read the change against the spec's § The consumers**

```bash
jj diff Geb/Mathlib/Computability/Cobham/Tree.lean
```

Check: the import swap to `public import Geb.Mathlib.Data.Tree.Ranked.Binary`;
`open RankedAlphabet.Binary` after `namespace Cobham`; `combSem_eq`,
`length_combSem_le`, `isTreeSem_eq_ite`,
`isTreeSem_eq_singleton_iff_valid` and the renamed
`isTreeSem_eq_singleton_iff_exists_spell`; and that no `BinTree` or
`exists_print` remains anywhere in the file, module docstring included.

```bash
grep -c "BinTree\|exists_print" Geb/Mathlib/Computability/Cobham/Tree.lean
awk 'length>90 {print FILENAME":"NR": "length}' \
  Geb/Mathlib/Computability/Cobham/Tree.lean
```

Expected: `0` from the grep, and no output from the `awk`. The second check is
for paragraphs edited without re-wrapping: a name substitution inside a
docstring leaves a long line or an orphan stub that no linter catches, the
limit being 100. Every paragraph the diff touches must read as one wrapped
block.

- [ ] **Step 2: Read the collapsed bridge**

```bash
jj diff Geb/Mathlib/Computability/Cobham/RankedTree.lean
```

Expected: `isRankedSem_binRanked_eq_singleton_iff_isTreeSem`'s proof loses its
middle link, both outer links now speaking of `binRanked.Valid`:

```lean
  (isRankedSem_eq_singleton_iff_valid _ w).trans
    (isTreeSem_eq_singleton_iff_valid w).symm
```

and its docstring no longer speaks of two scans' differing failure
conventions.

- [ ] **Step 3: Build and lint**

```bash
lake build && lake build GebTests && lake lint && lake lint -- GebTests
```

Expected: no errors; `-- Linting passed for Geb.` and
`-- Linting passed for GebTests.`

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Tree.lean \
          Geb/Mathlib/Computability/Cobham/RankedTree.lean \
  -m "refactor(cobham): state the recognizer over the ranked scan"
```

---

## Task 4: Restate the Bellantoni-Cook recognizer

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`

**Interfaces:**

- Consumes Task 1's counter form and `RankedAlphabet.valid_iff_exists_spell`.
- Produces `BellantoniCook.isTreeSem_eq_singleton_iff_exists_spell`,
  replacing `…_exists_print`. Task 5's mirror renames three theorems that
  refer to this module's subject but not to these names.

This module has no `length_combSem_le`: its `combRaw` is a `safeRec` node and
carries no recursion bound. It reads the deleted predicate's conjuncts at six
sites, twice as many as Cobham, which is this task's bulk.

- [ ] **Step 1: Swap the import**

In `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`, replace

```lean
public import Geb.Mathlib.Data.Tree.Preorder
```

with

```lean
public import Geb.Mathlib.Data.Tree.Ranked.Binary
```

- [ ] **Step 2: Open the namespace**

After `namespace BellantoniCook`, insert a blank line and

```lean
open RankedAlphabet.Binary
```

Write `depth`, `ok` and `binRanked` bare thereafter. `Binary.ok` will not
resolve under this `open`, and the wider `open RankedAlphabet` is rejected —
it would bring `mod_two_mul` and `add_one_mod` bare beside `Nat`'s own
residue API.

- [ ] **Step 3: Restate `combSem_eq`**

Replace the whole theorem with:

```lean
/-- The scan computes the stack depth in unary, offset by one, while the scan
is live, and the absorbing value `[false]` once it has failed. -/
theorem combSem_eq (w : List Bool) :
    combSem ![w] ![] =
      if ok w then List.replicate (depth w + 1) true
      else [false] := by
  refine List.rec (motive := fun u ↦ combSem ![u] ![] =
    if ok u then List.replicate (depth u + 1) true else [false])
    rfl ?_ w
  intro b v ih
  cases hok : ok v
  · have hv : combSem ![v] ![] = [false] := by rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, ok_cons_false, hok]; rfl
    · rw [combSem_cons_true, hv, ok_cons_true, hok]; rfl
  · have hv : combSem ![v] ![] = List.replicate (depth v + 1) true := by
      rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, ok_cons_false, hok,
        depth_cons_false_of_ok v hok]
      rfl
    · rw [combSem_cons_true, hv, ok_cons_true, hok]
      -- the guard's two predecessors reduce only on a numeral of at least
      -- that size, so the depth is split into constructor forms; the
      -- conditional depth lemma applies only in the third case, the first
      -- two closing on the failed branch
      have hsplit : ∀ d : ℕ, d = 0 ∨ d = 1 ∨ ∃ m, d = m + 2 := fun d ↦
        match d with
        | 0 => Or.inl rfl
        | 1 => Or.inr (Or.inl rfl)
        | (m + 2) => Or.inr (Or.inr ⟨m, rfl⟩)
      obtain (h0 | h1 | ⟨m, hm⟩) := hsplit (depth v)
      · rw [h0]; rfl
      · rw [h1]; rfl
      · rw [depth_cons_true_of_ok_of_two_le_depth v hok (by omega), hm]; rfl
```

The two changes from the deleted form are the substitution of the counter
form's names, and the move of the depth rewrite from before the three-way
split to inside its third case, where `hm : depth v = m + 2` supplies
`2 ≤ depth v` by `omega`. `Geb/Mathlib/Computability/Cobham/Tree.lean`'s
`combSem_eq`, committed in Task 3, is the same shape and compiles.

- [ ] **Step 4: Restate `isTreeSem_eq_singleton_iff_valid`**

```lean
/-- The recognizer accepts exactly the words `binRanked`'s scan accepts. -/
theorem isTreeSem_eq_singleton_iff_valid (w : List Bool) :
    isTreeSem ![w] ![] = [true] ↔ binRanked.Valid w := by
  rw [isTreeSem_apply, eqOneSem_env]
  simp only [eqOneSem_eq, combSem_eq]
  by_cases h : ok w = true
  · rw [if_pos h]
    simp only [List.tail_replicate, List.length_replicate, Nat.add_sub_cancel]
    by_cases hd : depth w = 1
    · rw [if_pos hd]
      exact ⟨fun _ ↦ (valid_iff_ok_and_depth_eq_one w).mpr ⟨h, hd⟩, fun _ ↦ rfl⟩
    · rw [if_neg hd]
      refine ⟨fun hw ↦ absurd hw (by nofun), ?_⟩
      rintro hv
      exact absurd ((valid_iff_ok_and_depth_eq_one w).mp hv).2 hd
  · rw [if_neg h, if_neg (by decide : ¬ ([false] : List Bool).tail.length = 1)]
    refine ⟨fun hw ↦ absurd hw (by nofun), ?_⟩
    rintro hv
    exact absurd ((valid_iff_ok_and_depth_eq_one w).mp hv).1 h
```

- [ ] **Step 5: Restate and rename `isTreeSem_eq_singleton_iff_exists_print`**

```lean
/-- The recognizer accepts exactly the preorder spellings of `binRanked`'s
terms. -/
theorem isTreeSem_eq_singleton_iff_exists_spell (w : List Bool) :
    isTreeSem ![w] ![] = [true] ↔ ∃ t, binRanked.spell t = w :=
  (isTreeSem_eq_singleton_iff_valid w).trans (binRanked.valid_iff_exists_spell w)
```

- [ ] **Step 6: Restate `isTreeSem_eq_ite`**

```lean
/-- The recognizer is the indicator of `binRanked`'s scan: `[true]` on a
spelling and `[]` on anything else. `isTreeSem_eq_singleton_iff_valid` pins
the value only where it accepts. -/
theorem isTreeSem_eq_ite (w : List Bool) :
    isTreeSem ![w] ![] = if binRanked.Valid w then [true] else [] := by
  rw [isTreeSem_apply, eqOneSem_env, eqOneSem_eq, combSem_eq]
  by_cases h : ok w = true
  · rw [if_pos h]
    simp only [List.tail_replicate, List.length_replicate, Nat.add_sub_cancel]
    by_cases hd : depth w = 1
    · rw [if_pos hd, if_pos ((valid_iff_ok_and_depth_eq_one w).mpr ⟨h, hd⟩)]
    · rw [if_neg hd,
        if_neg fun hv ↦ hd ((valid_iff_ok_and_depth_eq_one w).mp hv).2]
  · rw [if_neg h, if_neg (by decide : ¬ ([false] : List Bool).tail.length = 1),
      if_neg fun hv ↦ h ((valid_iff_ok_and_depth_eq_one w).mp hv).1]
```

- [ ] **Step 7: Restate the module docstring**

Five occurrences across five bullets name `BinTree` or the renamed theorem.
Replace as follows, keeping every line under 100
characters and re-wrapping the paragraphs you touch:

- the summary's "Composed with `BinTree.valid_iff_exists_print`,
  `isTreeSem_eq_singleton_iff_exists_print` states that an expression of `B`
  accepts exactly the spellings of trees" becomes the same sentence over
  `RankedAlphabet.valid_iff_exists_spell`,
  `isTreeSem_eq_singleton_iff_exists_spell`, and "the spellings of
  `binRanked`'s terms";
- `## Main statements`' `combSem_eq` bullet: "the scan computes
  `RankedAlphabet.Binary.depth` in unary, offset by one, while
  `RankedAlphabet.Binary.ok` holds, and `[false]` once it has failed";
- its `isTreeSem_eq_singleton_iff_valid` bullet: "`isTree` accepts exactly
  the words `binRanked`'s scan accepts";
- its `isTreeSem_eq_singleton_iff_exists_print` bullet: renamed, and
  "equivalently, exactly the spellings of `binRanked`'s terms";
- its `isTreeSem_eq_ite` bullet: "the recognizer as the indicator of
  `binRanked`'s scan".

- [ ] **Step 8: Build**

```bash
lake build Geb.Mathlib.Computability.BellantoniCook.Tree
```

Expected: built, no errors. A `rewrite failed` at `combSem_eq` means the
depth rewrite was left before the split; a `Unknown identifier Binary.ok`
means the qualified form was used under the narrow `open`.

- [ ] **Step 9: Check the whole build, the axioms and the residual names**

```bash
lake build && lake build GebTests && lake lint && lake lint -- GebTests
grep -c "BinTree\|exists_print" Geb/Mathlib/Computability/BellantoniCook/Tree.lean
```

Expected: no build errors, both lints pass, and `0` from the grep.

- [ ] **Step 10: Commit**

```bash
jj commit Geb/Mathlib/Computability/BellantoniCook/Tree.lean \
  -m "refactor(bc): state the recognizer over the ranked scan"
```

---

## Task 5: Restate the two test mirrors

**Files:**

- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`
- Modify: `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`

**Interfaces:**

- Consumes Tasks 1 and 4.
- Produces the worked words the deleted mirror carried, at `binRanked`.
  Task 6 deletes `GebTests/Mathlib/Data/Tree/Preorder.lean` once they are
  here.

The words `[false]`, `[false, true, false]` and `[false, false]` must stay
pinned on the scan side, because `GebTests/…/Cobham/Tree.lean` pins
`isTreeSem` at the same three, and the two sets meeting at an accepting word
and a rejecting one is what checks that `decide` reduces each route to what
its proofs are about.

- [ ] **Step 1: Redefine the worked term and its spelling**

In `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`, replace `binarySample`'s
definition and the two agreement theorems:

```lean
/-- The asymmetric term the assertions below are stated at: a node whose left
child is a two-leaf node and whose right child is a leaf. Its `size` is five,
counting leaves alongside internal nodes. -/
def binarySample : binRanked.Term := node (node leaf leaf) leaf

/-- The asymmetric term's spelling, which no symmetric term has. -/
theorem spell_binarySample :
    binRanked.spell binarySample = [true, true, false, false, false] := by
  decide

/-- A node over two leaves is spelled by a `true` bit and two `false` bits. -/
theorem spell_node_leaf_leaf :
    binRanked.spell (node leaf leaf) = [true, false, false] := by decide
```

`spell_termEquiv_binarySample` and `print_binarySample` go: the first names
`termEquiv`, and the second is the other half of an agreement whose first
half is now `spell_binarySample`. No theorem restates
`binRanked.spell leaf = [false]`: that is `spell_leaf`, which the library
already carries as `@[simp]`.

These are `decide`, not `rfl`: `Nat.land`, which `Nat.testBit` runs through,
is not exposed, so a block does not reduce during elaboration while the
kernel evaluates it.

- [ ] **Step 2: Add the descent's values and its three rejections**

```lean
/-- The descent inverts the spelling on a leaf. -/
theorem parse_spell_leaf :
    (binRanked.parse [false]).map binRanked.spell = some [false] := by decide

/-- And on the asymmetric term. -/
theorem parse_spell_binarySample :
    (binRanked.parse [true, true, false, false, false]).map binRanked.spell =
      some [true, true, false, false, false] := by decide

/-- And on a node over two leaves. -/
theorem parse_spell_node_leaf_leaf :
    (binRanked.parse [true, false, false]).map binRanked.spell =
      some [true, false, false] := by decide

/-- The descent rejects the empty word: it has nothing to read. -/
theorem parse_nil : (binRanked.parse ([] : List Bool)).map binRanked.spell = none := by
  decide

/-- The descent rejects a truncated word: the second child runs out of
input. -/
theorem parse_truncated :
    (binRanked.parse [true, false]).map binRanked.spell = none := by decide

/-- The descent rejects trailing input: it succeeds and leaves a non-empty
remainder. -/
theorem parse_trailing :
    (binRanked.parse [false, false]).map binRanked.spell = none := by decide
```

The `Option.map binRanked.spell` form is deliberate: `binRanked.parse w = t`
is an equation in `Option binRanked.Term` and would need a `DecidableEq` on
the W-type, which the sibling mirror's Implementation notes record avoiding.

- [ ] **Step 3: Add the counter form's worked words**

```lean
/-- Validity itself on the asymmetric term's spelling. -/
theorem valid_spell_binarySample :
    binRanked.Valid [true, true, false, false, false] := by decide

/-- A word failing liveness alone: its pending count is one, yet it reads a
node bit with one subterm pending. -/
theorem depth_node_at_depth_one : depth [false, true, false] = 1 := by decide

/-- The liveness half of that word. -/
theorem ok_node_at_depth_one : ok [false, true, false] = false := by decide

/-- That word is not valid, by reduction rather than through the counter
form's characterisation. -/
theorem not_valid_node_at_depth_one : ¬ binRanked.Valid [false, true, false] := by
  decide

/-- A word failing the count alone: two leaves and no node leave two
subterms pending. -/
theorem depth_two_leaves : depth [false, false] = 2 := by decide

/-- The liveness half of that word. Together with the pair at
`[false, true, false]`, validity's conjuncts are separated in both
directions. -/
theorem ok_two_leaves : ok [false, false] = true := by decide

/-- And it is not valid. -/
theorem not_valid_two_leaves : ¬ binRanked.Valid [false, false] := by decide

/-- `depth_le_length` at the empty word. -/
theorem depth_le_length_nil : depth ([] : List Bool) ≤ ([] : List Bool).length := by
  decide

/-- `depth_le_length` at a word of leaf bits only. -/
theorem depth_le_length_leaves : depth [false, false, false] ≤ 3 := by decide

/-- `depth_le_length` at a word mixing a node bit with leaf bits. -/
theorem depth_le_length_mixed : depth [true, false, false] ≤ 3 := by decide

/-- The `DecidablePred binRanked.Valid` instance accepts a valid word. -/
theorem decide_valid_leaf : decide (binRanked.Valid [false]) = true := by decide

/-- And rejects an invalid one. Its word is a node bit and a leaf bit. -/
theorem decide_not_valid_node_leaf :
    decide (binRanked.Valid [true, false]) = false := by decide
```

- [ ] **Step 4: Remove the vacuous sweep and its import**

Delete `validBool_eq_decide_binTree_valid`. Both its sides become one
function once `BinTree.Valid` is gone, so the assertion loses its subject.
Then delete the now-unused import line

```lean
public import GebTests.Mathlib.Data.Tree.Ranked.Basic
```

together with the blank line that separated the `public` group from the plain
import. `wordsUpTo` was its only use. Leaving it fails
`lake shake --add-public --keep-implied`, which the pre-push checklist runs.

- [ ] **Step 5: Restate the sweep inventory in the fixture module**

`GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` carries

```lean
/-- The enumeration the `Preorder` and `Binary` mirrors sweep holds every word
of length at most eight. -/
theorem length_wordsUpTo_eight : (wordsUpTo 8).length = 511 := by
```

Those are the two siblings in `GebTests/…/Ranked/`, and Step 4 retires the
`Binary` one's sweep. Restate the docstring over the mirror that still sweeps
there:

```lean
/-- The enumeration the `Preorder` mirror sweeps holds every word of length at
most eight. -/
```

`length_wordsUpTo_six`'s docstring needs no change: it names the
`Cobham/RankedTree` mirror's sweeps, which this branch does not touch.

- [ ] **Step 6: Restate that mirror's module docstring**

Its title, summary, `## Main definitions`, `## Main statements` and `## Tags`
all describe the equivalence with `BinTree`. Replace them with:

```lean
/-!
# The two-symbol alphabet on worked words

The spelling of a worked term, the descent's value on two spellings and its
three rejections, and the counter form of the validity scan at the words that
separate validity's two conjuncts.

## Main definitions

* `binarySample` — the term the assertions are stated at.

## Main statements

The assertions below give the worked term's spelling, the descent's value on
two spellings and its rejection of the empty, the truncated and the trailing
word, the pending count and the liveness verdict at a word failing each
conjunct of validity, and the decision of validity at an accepting and a
rejecting word.

## Tags

binary tree, ranked alphabet, preorder, descent, scan
-/
```

- [ ] **Step 7: Build the mirror**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Binary
```

Expected: built. A `decide` that fails to reduce means a `@[expose]`
regression upstream; a `maxRecDepth` error means a `set_option maxRecDepth
100000 in` is needed on that assertion, though none of the above should need
one.

- [ ] **Step 8: Rename the three Bellantoni-Cook mirror theorems**

In `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`, rename

```text
isTreeSem_print_leaf        →  isTreeSem_spell_leaf
isTreeSem_print_node        →  isTreeSem_spell_node
isTreeSem_print_asymmetric  →  isTreeSem_spell_asymmetric
```

Their statements, values and tactics are unchanged: the words are the same
bitstrings either way. That module's docstring names none of the three — it
says only that each names the recognizer's or the scan's value on a specific
bitstring — so it needs no change.

- [ ] **Step 9: Build and lint everything**

```bash
lake build && lake build GebTests && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
```

Expected: no errors, both lints pass, and no output from `lake shake`. The
shake run belongs here rather than in Task 6: Step 4 removes an import, and
this is the commit that would carry a stale one.

- [ ] **Step 10: Commit**

```bash
jj commit GebTests/Mathlib/Data/Tree/Ranked/Binary.lean \
          GebTests/Mathlib/Data/Tree/Ranked/Basic.lean \
          GebTests/Mathlib/Computability/BellantoniCook/Tree.lean \
  -m "test(tree): mirror the two-symbol encoding and its counter form"
```

---

## Task 6: Delete the absorbed modules

**Files:**

- Delete: `Geb/Mathlib/Data/Tree/Binary.lean`
- Delete: `Geb/Mathlib/Data/Tree/Preorder.lean`
- Delete: `GebTests/Mathlib/Data/Tree/Preorder.lean`
- Modify: `Geb/Mathlib/Data/Tree.lean`, `GebTests/Mathlib/Data/Tree.lean`
- Modify: `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`,
  `Ranked/Basic.lean`, `Ranked/Preorder.lean`

**Interfaces:** consumes every earlier task; produces nothing new. After this
task no committed file names `BinTree`.

- [ ] **Step 1: Delete the equivalence from `Ranked/Binary.lean`**

Remove `ofBinTree`, `toBinTree`, `toBinTree_ofBinTree`, `ofBinTree_toBinTree`,
`termEquiv`, `spell_termEquiv` and `valid_iff`, and the import

```lean
public import Geb.Mathlib.Data.Tree.Preorder
```

- [ ] **Step 2: Restate that module's docstring in full**

Its title and summary say the term algebra is equivalent to `BinTree` and
that the equivalence carries `spell` to `BinTree.print`; `## Main
definitions` lists `termEquiv`; `## Main statements` lists `spell_termEquiv`
and `valid_iff`; `## Tags` ends with the word "equivalence." Replace the
title, the summary, those bullets and the tag list with the following,
keeping the counter-form entries Task 1 added and the whole of Implementation
notes:

```lean
/-!
# The two-symbol ranked alphabet

The alphabet of one nullary and one binary symbol, spelled by one bit each.
Its terms are the unlabelled binary trees, the initial algebra of
`F X = 1 + X × X`, and its preorder encoding is `RankedAlphabet.spell` at
this alphabet.

At width one every block is a single bit, so the validity scan carries no
incomplete block and its state reduces to a pending count and a liveness
verdict. This module names that counter form and gives it one bit at a time,
which is the shape a recognizer over the encoding is stated against.

## Main definitions

* `RankedAlphabet.Binary.binRanked` — the alphabet.
* `RankedAlphabet.Binary.leaf`, `RankedAlphabet.Binary.node` — the two forms
  of its terms.
* `RankedAlphabet.Binary.depth`, `RankedAlphabet.Binary.ok` — the validity
  scan's pending count and its liveness verdict, read off a whole word.
```

`## Main statements` keeps the counter-form bullets Task 1 added and loses the
`spell_termEquiv` and `valid_iff` ones. `## Tags` becomes

```lean
binary tree, ranked alphabet, term algebra, preorder, scan
```

- [ ] **Step 3: Delete the three modules and edit the two indices**

```bash
rm Geb/Mathlib/Data/Tree/Binary.lean \
   Geb/Mathlib/Data/Tree/Preorder.lean \
   GebTests/Mathlib/Data/Tree/Preorder.lean
```

From `Geb/Mathlib/Data/Tree.lean` remove both

```lean
public import Geb.Mathlib.Data.Tree.Binary
public import Geb.Mathlib.Data.Tree.Preorder
```

and from `GebTests/Mathlib/Data/Tree.lean` remove

```lean
import GebTests.Mathlib.Data.Tree.Preorder
```

Both indices survive with one import each: the narrow-and-deep convention
gives each directory one indexing file, and `Geb/Mathlib/Data/Tree/` may grow
again.

- [ ] **Step 4: Move the three pieces of persistent documentation**

Into `Ranked/Preorder.lean`'s module docstring, each into the section its
source occupied:

- **Into the summary**, beside the existing prefix-notation paragraph, where
  it sat in the deleted module: the `DyckWord` comparison — that validity is
  stated as conditions in the manner of mathlib's `DyckWord`, whose
  `count_U_eq_count_D` and
  `count_D_le_count_U` play the roles the pending count and the liveness flag
  play here, and in the direction a single right-to-left pass carrying a
  counter can scan. Generalise the count: `valid_iff_scanFinal` gives three
  conditions, the third being the empty buffer that width one makes vacuous.
  Transcribed unaltered the clause would be false here.
- **Into Implementation notes**, beside the existing paragraph on `parseAux`
  recursing over an explicit bound, where it sat in the deleted module: the
  fuel argument — that fuel exhaustion is not a rejection mechanism of its
  own, each layer consuming a whole block, which `width_pos` makes at
  least one bit, so the invariant that the fuel is at least the remaining
  length holds from the initial length down. The generic descent's rejections
  are `decodeBlock`'s two, input short of a block and a block spelling no
  symbol, together with a child's failure and the trailing input `parse`
  rejects.

`Ranked/Binary.lean`'s docstring needs nothing further here: Step 2's
replacement summary already carries the initial-algebra characterisation,
that these terms are the initial algebra of `F X = 1 + X × X`. Three
neighbouring notes in the deleted module die with their subject: `Direction`'s fibre-naming
convention, its sending `leaf` to `Fin 0` rather than `Empty`, and why it is
`@[expose]` — the ranked family is `fun i ↦ Fin (R.arity i)` by construction,
and `Ranked/Basic.lean` already records its own `@[expose]` reason.

`size`'s upstream-adjacency note dies with its subject; Task 7 records the
`TODO.md` consequence.

- [ ] **Step 5: Restate the two remaining orphaned docstrings**

In `Ranked/Basic.lean`, two sentences. Replace

```lean
The unlabelled binary trees of `Data/Tree/Binary.lean` are the terms of the
alphabet of one symbol of arity zero and one of arity two.
```

with

```lean
The unlabelled binary trees are the terms of `RankedAlphabet.Binary`'s
alphabet, of one symbol of arity zero and one of arity two.
```

and in its Implementation notes replace "`Term` is `@[expose]`, as `BinTree`
is: without it …" with "`Term` is `@[expose]`: without it …", keeping the
rest of that sentence unchanged.

In `Ranked/Preorder.lean`, the sentence sits mid-paragraph and spans an
existing line break. Replace

```lean
The idea is that of prefix notation, in which a symbol is followed by exactly
as many operands as its arity. `Data/Tree/Preorder.lean` is the case of one
symbol of arity zero and one of arity two.
```

with

```lean
The idea is that of prefix notation, in which a symbol is followed by exactly
as many operands as its arity. `RankedAlphabet.Binary` is the case of one
symbol of arity zero and one of arity two.
```

The names differ in length, so re-wrap the paragraph after the substitution.

- [ ] **Step 6: Build, lint, and check for residue**

```bash
lake build && lake build GebTests && lake lint && lake lint -- GebTests
grep -rn "BinTree" --include=*.lean Geb GebTests
```

Expected: no build errors, both lints pass, and the grep returns nothing.

- [ ] **Step 7: Check the imports are minimal**

`lake shake` reads built oleans for every library it scans, and
`lakefile.toml`'s `defaultTargets` is `Geb` alone, so `GebTests` is built
explicitly first — the order `scripts/pre-push.sh` itself uses.

```bash
lake build GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
```

Expected: no output. A report against
`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` means Task 5 Step 4 was
skipped.

- [ ] **Step 8: Commit**

```bash
jj commit -m "refactor(tree): delete the absorbed binary-tree encoding"
```

---

## Task 7: Restate the catalogue and the roadmap

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

- [ ] **Step 1: Edit `docs/index.md`**

- Delete the entries for `Geb/Mathlib/Data/Tree/Binary.lean` and
  `Geb/Mathlib/Data/Tree/Preorder.lean`.
- Restate the entries for `Ranked/Binary.lean` (which gains the counter form:
  `depth`, `ok`, `valid_iff_ok_and_depth_eq_one`, `depth_le_length` and the
  four `cons`-lemmas), `Cobham/Tree.lean` and `BellantoniCook/Tree.lean`.
- In the `Ranked/Preorder.lean` entry, remove the reference to the deleted
  module and add the `DyckWord` comparison, whose only other home was the
  entry being deleted.
- The `Cobham/RankedTree.lean` entry needs no change: this branch alters how
  its bridge theorem is proved, not what it states.

- [ ] **Step 2: Edit `TODO.md` § Extensions of the tree recognizers**

- Record B4 as done, leaving B5. Rewrite B4's own entry as a done-entry; it
  names `BinTree` twice and counts its consumers in this repository, and the
  count goes.
- Restate B1's done-entry, which credits `termEquiv`, `spell_termEquiv` and
  `valid_iff` as exhibiting `BinTree` as the two-symbol instance.
- Add the deferral: whether `Cobham/Tree.lean`'s recognizer is redundant
  beside `Cobham/RankedTree.lean`'s, with `isTree_smashFree` and the
  [Strahm2003] Theorem 1(2) corollary as the residue that is not.
- Add the deferral: a sweep-scale cross-check of `Cobham.isTreeSem` against
  `binRanked.validBool`, noting that at length six it follows from
  `isRankedSem_eq_validBool_binRanked` and the bridge theorem, so the
  deferral is worth taking only above that, and that a lighter computation was measured
  reaching the 200000-heartbeat `isDefEq` limit at 511 words, so a sweep above
  length seven may not elaborate at all.

- [ ] **Step 3: Edit `TODO.md` § The Bellantoni-Cook tree recognizer**

Item 6 says "any statement relating `BinTree.Valid` to that predicate";
name `binRanked.Valid`.

- [ ] **Step 4: Edit `TODO.md` § Binary trees and their preorder encoding**

- Delete item 3 outright. Every part of it — the overlap with
  `Mathlib/Data/Tree/Basic.lean`, `Binary.lean` being a free filename, the
  `numNodes` transfer, whether the name `size` survives — rests on `BinTree`
  existing. Recording that the overlap dissolved would be a note about how
  the code used to be, which `CONTRIBUTING.md` § Document only the persistent
  bars.
- The section opens by counting its items; that line goes with item 3, and
  the remaining items are named rather than counted.
- Restate item 2 (`ConcreteSyntax.Ast` from `BinTree`) over the labelled
  ranked alphabet item 1 describes, and item 4 (`print` to
  `DyckWord.equivTree`) over `binRanked.spell`.

- [ ] **Step 5: Edit `TODO.md` § The namespace prefix in a declaration body**

It cites four `BinTree.induction` sites in the deleted
`Geb/Mathlib/Data/Tree/Preorder.lean` and one `Term.mk` site in
`Ranked/Basic.lean`. Restate over the surviving site alone, and record that
whether one site still warrants a branch of its own is open.

- [ ] **Step 6: Add the tooling deferral**

`TODO.md` has no section about repository tooling; add one. Its heading is

```markdown
### Vale configuration
```

and it goes immediately before `### The namespace prefix in a declaration
body`, which is the first of the file's process-and-tooling entries rather
than a mathematical workstream. Its content: the tree carries a Vale
configuration that neither `scripts/pre-push.sh` nor any workflow runs, whose
default package set flags the spaced em-dash every committed document using
one writes, and the filename `TODO.md`; adopting it with those rules
downgraded, or removing it, is its own branch.

- [ ] **Step 7: Lint the Markdown**

```bash
doctoc --update-only . && markdownlint-cli2 '**/*.md' && scripts/check-md-links.sh
```

Expected: `Everything is OK.`, `Summary: 0 issues in 0 files`, and
`check-md-links: all Markdown link targets resolve`.

- [ ] **Step 8: Commit**

```bash
jj commit docs/index.md TODO.md \
  -m "doc(tree): catalogue the absorbed encoding"
```

---

## Task 8: Dispose of the two plan documents

**Files:**

- Modify: `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md`
- Replace: `docs/superpowers/plans/2026-08-10-tree-recognizer-session-handoff.md`

Both name deleted declarations and both assert a state this branch changes,
and B5's session is instructed to read them first.

- [ ] **Step 1: Rewrite the session handoff**

It says of itself that it owns the state of the line and is replaced when
that state changes. Keep its § Read these first list of binding documents,
dropping its final paragraph (which asserts B4 has no specification and that
its first phase is brainstorming), and keep § Which document owns what
unchanged. Replace the rest as follows.

Status table:

```markdown
| Item | What it is | Status |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — ranked alphabets, the preorder encoding, the validity scan | Done, unpushed |
| B2 | `Cobham/Scan.lean` — the scan combinator, and `Cobham/Tree.lean` rebuilt on it | Done, unpushed |
| — | `Cobham/Cases.lean` — definition by cases, with its combinators in `Cobham/Basic.lean` | Done, unpushed |
| B6 | `Cobham/RankedTree.lean` — the generic ranked recognizer | Done, unpushed |
| B3 | `Cobham/Fold.lean` — the catamorphism at a carrier with a bit encoding | Done, unpushed |
| B4 | `BinTree` absorbed into `RankedAlphabet.Term`, the duplication removed | Done, unpushed |
| B5 | `Geb/Internal/` — linear time and space against Cslib's `MultiTapeTM` | Not started |
```

The B1 row loses the clause crediting `BinTree` as the two-symbol instance.
The line diagram gains a segment:

```text
main                                   312c5adf
  └─ feat/ranked-tree-recognizers      2f50f879
       └─ feat/cobham-scanner          8cbff06f
            └─ feat/cobham-cases       5ea87784
                 └─ feat/cobham-ranked-tree  79aaea40
                      └─ feat/cobham-fold    c368339d
                           └─ refactor/tree-absorb-bintree
```

The ids above are the current bookmark targets; confirm them with
`jj bookmark list`. The last line carries no id because this segment's final
commit does not exist until Task 9, and its bookmark is set after that commit
rather than before, so that it does not omit the commit removing this
segment's own transient documents.

§ What this session delivered becomes the absorption: the counter form of the
validity scan at width one in `Ranked/Binary.lean`; the two recognizers and
the bridge theorem restated over it and over `binRanked.Valid`; the deletion
of `Data/Tree/{Binary,Preorder}.lean` and their mirror; and the catalogue and
roadmap entries.

§ What to pick up next becomes B5, whose description the workstream record's
§ B5 carries, with the note that it depends on B2, that it is confined to
`Geb/Internal/` by the subtree import rules, and that it differs in kind from
the others, its difficulty unbounded by anything done so far.

§ Context the next session will want keeps its existing entries — they remain
true — and § Loose ends keeps both of its entries: the `docs/references.bib`
keys are still uncited, and the `oneAtOf`/`falseAtOf` duplication is still
open, `TODO.md` § Extensions of the tree recognizers carrying it as well.

- [ ] **Step 2: Amend the workstream record**

It outlives this branch, B5 still needing it, so amend rather than replace:

- § Read these first says B4 and B5 each get their own brainstorming phase,
  spec, plan and segment. It becomes true of B5 alone.
- § Where the workstream stands says B4 and B5 are not started. It becomes:
  B1, B2, the case combinator, B6, B3 and B4 are done and unpushed on one
  line off `main`; B5 is not started.
- Its inventory of `Ranked/Binary.lean` lists `termEquiv`, `spell_termEquiv`
  and `valid_iff`. Those three are deleted; the inventory becomes the
  alphabet, its two constructors, the block and spelling lemmas, and the
  counter form of the validity scan.
- Its sentence "the mirrors … sweep `validBool` against the descent and
  against `BinTree.Valid` over every word of length at most eight" loses its
  second conjunct: the mirrors sweep `validBool` against the descent.
- § B4's heading gains the `(done)` suffix, matching its
  siblings `## B2: the scan combinator (done)`, `## B6: the generic ranked
  recognizer (done)` and `## B3: the fold (done)`. Its body, which prescribes
  a bridge-corollary design the spec supersedes and says the duplication is
  on `main` until B4 lands, becomes a done-entry naming what landed:
  `Ranked/Binary.lean`'s counter form, the two recognizers and the bridge
  theorem restated over it, and the deletion of `Data/Tree/{Binary,Preorder}`
  and their mirror.
- § What completion means says two items remain in the order B4 then B5, and
  that the workstream is complete when B4 has landed. It becomes: one item
  remains, B5; the workstream's completion condition is met, no tree encoding
  now being defined twice, and B5 is a separate undertaking whose failure
  costs nothing already built.
- § Facts established by building gains what this branch established, its
  opening paragraph attributing the new items to this segment as it
  attributes the existing ones. The facts worth recording: that
  `decide (([b] : List Bool).length = binRanked.width)` does not iota-reduce
  inside `scanStep`'s `match` though `binRanked.width` does reduce to `1`;
  that `depth` unfolds under `simp only [depth]` at a hypothesis and the goal
  together; and that `omega` treats an unreduced `Nat.zero` as an atom, so a
  `Nat.rec` base case's bound is named at a literal first.

- [ ] **Step 3: Regenerate the tables of contents**

Restating § B4's heading changes that document's TOC.

```bash
doctoc --update-only . && markdownlint-cli2 '**/*.md' && scripts/check-md-links.sh
```

Expected: all three clean.

- [ ] **Step 4: Commit**

```bash
jj commit docs/superpowers/plans/ \
  -m "doc(tree): hand off the workstream after the absorption"
```

---

## Task 9: Remove this plan and the spec, and gate the branch

Specs and plans are transient: they record how the current state was reached,
not what it is, so they belong in history rather than on an active branch.

- [ ] **Step 1: Remove both transient documents**

```bash
rm docs/superpowers/specs/2026-08-11-tree-absorb-bintree-design.md \
   docs/superpowers/plans/2026-08-11-tree-absorb-bintree.md
```

- [ ] **Step 2: Check no committed document links to them**

```bash
scripts/check-md-links.sh
```

Expected: `check-md-links: all Markdown link targets resolve`. A failure
names a document still linking to a removed file; fix that document rather
than restoring the file.

- [ ] **Step 3: Commit**

```bash
jj commit -m "doc(tree): remove the transient spec and plan"
```

- [ ] **Step 4: Set the segment's bookmark**

Set it after the final commit, so that it does not omit the commit removing
this segment's own transient documents.

```bash
jj bookmark set refactor/tree-absorb-bintree -r @-
```

- [ ] **Step 5: Run the pre-push checklist**

```bash
scripts/pre-push.sh
```

Expected: every step passes. A non-blocking WARN about commit `5cfd5ef1`'s
73-character subject is pre-existing and belongs to the case-combinator
segment; leave it.

- [ ] **Step 6: Run the Lean review skill**

Run `lean4:review` over the branch's `.lean` changes, and
`pr-review-toolkit:review-pr` over the segment as a whole. A task-scoped
review does not see a module-scoped defect: budget a review that reads
`Cobham/Tree.lean` and `BellantoniCook/Tree.lean` whole.

- [ ] **Step 7: Stop**

Do not push. `AGENTS.md` § No `jj git push` without user line-by-line review
binds every segment, first creation included. Report the branch as ready for
the user's review.
