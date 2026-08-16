# The ranked term algebra's destructor in the fold's language — plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [The constant this branch computes with](#the-constant-this-branch-computes-with)
- [Task 1: Create the branch and commit the spec and this plan](#task-1-create-the-branch-and-commit-the-spec-and-this-plan)
- [Task 2: Move the weighted-length bound into `SelfDelim.lean`](#task-2-move-the-weighted-length-bound-into-selfdelimlean)
- [Task 3: The block reader](#task-3-the-block-reader)
- [Task 4: The paramorphism and its growth constant](#task-4-the-paramorphism-and-its-growth-constant)
- [Task 5: The delimited-children algebra and its invariant](#task-5-the-delimited-children-algebra-and-its-invariant)
- [Task 6: The linearity hypothesis](#task-6-the-linearity-hypothesis)
- [Task 7: The delimited-children algebra as an expression](#task-7-the-delimited-children-algebra-as-an-expression)
- [Task 8: The child reader](#task-8-the-child-reader)
- [Task 9: The inverse laws](#task-9-the-inverse-laws)
- [Task 10: The test module, and the end of `Boundary.lean`](#task-10-the-test-module-and-the-end-of-boundarylean)
- [Task 11: Documentation and the amended obligations](#task-11-documentation-and-the-amended-obligations)
- [Task 12: Verify the branch and remove the spec and plan](#task-12-verify-the-branch-and-remove-the-spec-and-plan)
- [Risks this plan carries](#risks-this-plan-carries)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver the inverse of the initial algebra's structure map as
expressions of Cobham's class, and the paramorphism at the same
representation, in
`Geb/Internal/Computability/CobhamFoldProto/Destruct.lean` with one lemma
into `SelfDelim.lean` and a test module carrying the samples.

**Architecture:** `algPara` is the paramorphism as a fold at the carrier
`List Bool`, pairing a subterm's spelling with the step's value, the value
delimited by `entryWord` so the two are separable. The delimiting does not
nest — each level reads only the spelling half of a child's value — so the
value stays linear in the subterm. `algCh` is the instance whose step returns
the children's spellings, each delimited; `childOf j` reads the `j`-th entry
of that fold's payload, and `codeOf` reads the leading block through a
constant unary prefix that needs no dispatch. `algCh` fails the per-symbol
growth condition, so the linearity hypothesis `foldOutOfV` takes is proved
through an invariant of `algCh`'s own outputs and a potential argument over
it.

**Tech Stack:** Lean 4 (toolchain from `lean-toolchain`), mathlib, `lake`,
`jj` in colocated mode.

**Spec:**
[docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md](../specs/2026-08-15-ranked-term-destructor-design.md)

Each task's **Interfaces** block names the declarations that task's own
statements mention. It is not an exhaustive import list: the proofs also
reach ordinary `List` and `Nat` lemmas and the neighbouring `…_nil` /
`…_cons` equations of the primitives they use, all of which resolve through
the imports Task 3 Step 1 declares.

## Global Constraints

- Branch: `feat/cobham-term-dest`, stacked on `feat/cobham-term-mk`, which
  stacks on the unmerged `feat/cobham-fold-proto`. `main` has advanced past
  that branch's base, so none of the three is an ancestor of `main`; if
  `feat/cobham-fold-proto` is rebased onto `main` first, re-read
  `scripts/pre-push.sh` before Task 12, since its contents differ between the
  two bases. It
  depends on that branch's `algMk`, `flattenOf`, `semAt_flattenOf`,
  `semAt_compOf`, `smashFreeBool_flattenOf`, `mkOf` and `semAt_mkOf`; it must
  not be rebased off it.
- All state-mutating version control goes through `jj`. Raw mutating `git`
  subcommands are blocked by `scripts/hooks/block-mutating-git.sh`. After
  every `jj commit` on the branch, run
  `jj bookmark set feat/cobham-term-dest -r @-`: jj bookmarks do not
  auto-advance.
- No `noncomputable`. No `Classical` beyond what the imported modules already
  carry; every declaration this branch adds is `Classical.choice`-free, which
  `GebMeta.detectNonstandardAxiom` enforces through `lake lint` and
  `lake lint -- GebTests`. In particular, do not reach for `List.take_add` or
  the `Vector.ofFn` family: `SelfDelim.lean` records that the first was
  measured choice-dependent, and this plan supplies its own truncation lemma
  for that reason.
- No `sorry` and no `admit` in any committed state. Between edits within a
  task, use `_` to expose a hole.
- No `induction` / `induction'` tactics and no self-calling `def`. All
  recursion goes through a recursor: `Nat.rec`, `List.rec`,
  `RankedAlphabet.Term.induction`.
- Lean style: 2-space indent, 100-character lines, one declaration per line,
  Unicode notation, module docstring with `# Title`, summary,
  `## Main definitions`, `## Main statements`, `## Implementation notes`
  where it has content, `## References`, `## Tags`, and a `/-- ... -/`
  docstring on every `def` and every theorem.
- Markdown: 80-character lines outside code blocks and tables, doctoc TOC
  markers on any file with more than one `##`, repo-relative internal links.
- Commit messages: `<type>(<scope>): <subject>`, imperative present tense, no
  capital, no trailing period, type drawn from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- No literature citation is added to `docs/references.bib`: `[Cobham1965]`,
  `[Meertens1992]` and `[Strahm2003]` are all already recorded there.
- No expression is evaluated. Acceptance is symbolic throughout for anything
  reaching the expression layer: the readout's dispatch has
  `2 ^ readoutWidthV R` branches and an evaluation of it at a one-entry state
  was measured not to return. The `#guard`s the test module carries evaluate
  the semantic fold and the semantic child reader only, as
  `Boundary.lean`'s do now.
- `Destruct.lean` is the only new library module. Four existing modules are
  edited, each authorised by the spec's § What exists and each a
  generalisation or an addition rather than a copy: the one lemma Task 2 moves into
  `SelfDelim.lean`; `mem_stack_foldScanFinal` into `Fold.lean` and the
  potential chain generalised in `Variable.lean`, both in Task 6;
  `semAt_comp1Of` into `Bound.lean` in Task 7; and in Task 8 the two
  remainder-bearing stack-reading lemmas into `Variable.lean` together with
  the `private` drop on `SelfDelim.lean`'s `take_succ_append_take_one`, so
  that `SelfDelim.lean` is edited three times and four library modules in
  all, beside the two indexing files and `GebTests`' own.
  Every existing name keeps its statement, so no consumer of the fold
  changes. Nothing is restated in `Destruct.lean` that an existing module
  already proves.

## The constant this branch computes with

One constant recurs, with a multiplier derived from it. Fix them here so no
task re-derives either.

| Name | Value | Where it comes from |
| --- | --- | --- |
| `chGrowth R` | `4 * R.maxArity * R.width + R.maxArity + R.width + 1` | the per-symbol growth `algCh` meets under its own invariant, attained at a symbol of maximum arity whose children are all nullary |

The multiplier is `2 * chGrowth R + 2`, written inline in `chFoldOf`:
`foldOutOfV`'s `hmult` at `c = chGrowth R`, taken with equality so no
hypothesis is carried and `Nat.le_refl` discharges it.

The arithmetic behind `chGrowth`, for a symbol of arity `n` with arguments
`f`, writing `u d = dropEntrySem ![f d]`, `F = Σ_d |u d|`:

- `|algCh R i f| = 5 * F + 2 * n + 1 + R.width`, since the take-half is
  `entryWord` of a flattening of `n` entries whose payloads total `F`, and
  the drop-half is `R.code i` followed by those payloads.
- The invariant `5 * |u d| + 1 ≤ |f d| + 4 * R.width` at each child sums to
  `5 * F + n ≤ Σ_d |f d| + 4 * n * R.width`.
- Hence `|algCh R i f| ≤ Σ_d |f d| + 4 * n * R.width + n + R.width + 1`, and
  `n ≤ R.maxArity` gives `chGrowth R`.

The general paramorphism's constant is `2 * cphi + R.width + 1`, from
`2 * |takeEntrySem ![w]| + |dropEntrySem ![w]| ≤ |w|` — the lemma Task 2
moves into `SelfDelim.lean` — applied at each child.

---

## Task 1: Create the branch and commit the spec and this plan

**Files:**

- Restore, edit and commit:
  `docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md`
- Restore and commit:
  `docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md`

**Interfaces:**

- Consumes: the tip of `feat/cobham-term-mk`.
- Produces: the branch `feat/cobham-term-dest` with its spec and plan as its
  first commit.

- [ ] **Step 1: Start from the constructor branch's tip**

```bash
jj new feat/cobham-term-mk
jj log -r 'ancestors(@, 3)' --no-graph \
  -T 'change_id.short() ++ " " ++ bookmarks ++ " " ++ description.first_line() ++ "\n"'
```

Expected: a new empty working copy whose parent carries the bookmark
`feat/cobham-term-mk`, whose own tip commit removed that branch's spec and
plan.

- [ ] **Step 2: Restore the spec and this plan**

The constructor branch's Task 1 parked both under
`.superpowers/cobham-term-handoff/`, which is in `.gitignore` and in
`.markdownlint-cli2.jsonc`'s `ignores` list, so it is neither committed nor
linted. If that directory is gone, they are
recoverable from the operation log: `jj op log` names the operation that
`jj restore` performed on the constructor branch, and `jj op restore <id>`
rolls the working copy back to the state before it, from which the two files
can be copied out before rolling forward again.

```bash
cp .superpowers/cobham-term-handoff/2026-08-15-ranked-term-destructor-design.md \
  docs/superpowers/specs/
cp .superpowers/cobham-term-handoff/2026-08-15-ranked-term-destructor-plan.md \
  docs/superpowers/plans/
doctoc --update-only docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md
markdownlint-cli2 'docs/superpowers/plans/*.md' 'docs/superpowers/specs/*.md'
bash scripts/check-md-links.sh
```

Expected: the three checks exit zero, after one repair. The spec's § Scope
carries a Markdown link whose target is the constructor spec's filename,
`2026-08-15-ranked-term-constructor-design.md`, which this branch's working
tree no longer holds, so `scripts/check-md-links.sh` reports it as missing.
Replace that whole link — the bracketed text and the parenthesised target
together — with the module the constructor branch delivered, written as
inline code rather than as a link:
`Geb/Internal/Computability/CobhamFoldProto/Initial.lean`, so the sentence
reads:

```text
Together with `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`, on
which it depends, it lets a term of `RankedAlphabet.Term` be constructed,
destructed and recursed over inside the class, with the representation fixed
by `RankedAlphabet.spell`.
```

That § Scope link is the only one to change: the spec's `## References` names
`docs/index.md` and `TODO.md` but not the constructor spec.

- [ ] **Step 3: Commit and set the bookmark**

```bash
jj commit -m 'doc(cobham-term): add the ranked-term destructor spec and plan'
jj bookmark set feat/cobham-term-dest -r @-
```

Expected: the commit carries the bookmark and its parent is
`feat/cobham-term-mk`.

---

## Task 2: Move the weighted-length bound into `SelfDelim.lean`

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/SelfDelim.lean`
- Modify: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (remove the moved theorem and its docstring line)
- Modify: `docs/index.md` (the `SelfDelim.lean` entry)

**Interfaces:**

- Consumes: `Geb.CobhamFold.takeEntrySem_cons`,
  `Geb.CobhamFold.dropEntrySem_cons`, `Geb.CobhamFold.firstBitSem_eq`.
- Produces, in namespace `Geb.CobhamFold`:

```text
two_mul_length_takeEntrySem_add_length_dropEntrySem_le : ∀ w : List Bool, 2 * (takeEntrySem ![w]).length + (dropEntrySem ![w]).length ≤ w.length
```

This is the bound the general paramorphism's constant rests on, and the
first of this branch's edits to an existing library module; § Global
Constraints lists them all. `SelfDelim.lean` has
its two halves separately (`length_takeEntrySem_le`,
`length_dropEntrySem_le`); the combination is what makes the constant
unconditional.

- [ ] **Step 1: Add the theorem to `SelfDelim.lean`**

Place it after `length_takeEntrySem_le` and before `takeEntryOf`, beside the
last of the primitives' own length bounds. The proof is the one
`Boundary.lean` already carries, unchanged:

```lean
/-- The payload and the remainder together fit inside the word, the payload
counted twice: a `true` lengthens the payload by at most one bit while the
remainder loses one, so the weighted total does not grow. This is what bounds
a general paramorphism step's contribution. -/
theorem two_mul_length_takeEntrySem_add_length_dropEntrySem_le :
    ∀ w : List Bool,
      2 * (takeEntrySem ![w]).length + (dropEntrySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [takeEntrySem_cons, dropEntrySem_cons, List.length_cons]
    cases b
    · rw [ite_eq_right (by simp), ite_eq_right (by simp), List.length_nil]
      omega
    · rw [ite_eq_left rfl, ite_eq_left rfl, List.length_append, List.length_tail,
        firstBitSem_eq]
      match hd : dropEntrySem ![v] with
      | [] =>
        rw [hd] at ih
        simp only [List.length_nil]
        omega
      | c :: t =>
        rw [hd, List.length_cons] at ih
        simp only [List.length_cons, List.length_nil]
        omega
```

Add to `SelfDelim.lean`'s `## Main statements`:

```text
* `Geb.CobhamFold.two_mul_length_takeEntrySem_add_length_dropEntrySem_le` —
  the payload counted twice and the remainder fit inside the word.
```

- [ ] **Step 2: Remove it from `Boundary.lean`**

Delete the theorem, its docstring, and the `## Main statements` bullet naming
`GebTests.CobhamFold.two_mul_length_takeEntrySem_add_length_dropEntrySem_le`.

- [ ] **Step 3: Build both libraries**

```bash
lake build
lake build GebTests
```

Expected: no errors and no warnings. `Boundary.lean` `open`s
`Geb.CobhamFold`, so the moved name resolves there unqualified; nothing in
the remaining half uses it, so no reference breaks.

- [ ] **Step 4: Update the `SelfDelim.lean` entry in `docs/index.md`**

Append to that entry, before its `Depends on` sentence, indented two spaces
to match its continuation lines:

```text
`two_mul_length_takeEntrySem_add_length_dropEntrySem_le` combines the two
length bounds into the weighted one — a `true` lengthens the payload by at
most one bit while the remainder loses one — which is what bounds a
paramorphism step's contribution at an arbitrary argument rather than only at
a fold's value.
```

- [ ] **Step 5: Lint and commit**

```bash
markdownlint-cli2 'docs/index.md'
jj commit -m 'feat(cobham-term): bound a self-delimiting word'\''s halves'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 3: The block reader

**Files:**

- Create: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`
- Modify: `Geb/Internal/Computability/CobhamFoldProto.lean` (one import line)

**Interfaces:**

- Consumes: `Geb.CobhamFold.takeEntryOf`, `Geb.CobhamFold.dropEntryOf`,
  `Geb.CobhamFold.idOf`, `Geb.CobhamFold.comp1Of`,
  `Geb.CobhamFold.stepWord_comp1Of`, `Geb.CobhamFold.takeEntrySem_replicate`,
  `Geb.CobhamFold.dropEntrySem_replicate`, `Cobham.prependOf`,
  `Cobham.stepWord_prependOf`; `RankedAlphabet.spell_mk`,
  `RankedAlphabet.length_code`.
- Produces, in namespace `Geb.CobhamFold`:

```text
codeOf (R : RankedAlphabet) : COf 1
dropCodeOf (R : RankedAlphabet) : COf 1
stepWord_codeOf (R) (w : List Bool) : stepWord (codeOf R) w = w.take R.width
stepWord_dropCodeOf (R) (w : List Bool) : stepWord (dropCodeOf R) w = w.drop R.width
stepWord_codeOf_spell_mk (R) (i) (ch) : stepWord (codeOf R) (R.spell (Term.mk R i ch)) = R.code i
stepWord_dropCodeOf_spell_mk (R) (i) (ch) : stepWord (dropCodeOf R) (R.spell (Term.mk R i ch)) = (List.ofFn fun d ↦ R.spell (ch d)).flatten
```

The block reader needs no dispatch: a constant unary prefix turns the word
into a self-delimiting entry whose payload is the leading block.

- [ ] **Step 1: Create the module**

Write `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.Initial
public import Geb.Mathlib.Data.W.Basic

/-!
# The term algebra's destructor in the fold's language

The inverse of the initial algebra's structure map, as expressions of
Cobham's class, at the representation `RankedAlphabet.spell` fixes.

`codeOf` and `dropCodeOf` read a word's leading block and what follows it,
through a constant unary prefix that makes the word a self-delimiting entry
whose payload is that block, so no dispatch over the block is needed.

## Main definitions

* `Geb.CobhamFold.codeOf`, `Geb.CobhamFold.dropCodeOf` — the block reader and
  its complement.

## Main statements

* `Geb.CobhamFold.stepWord_codeOf`, `Geb.CobhamFold.stepWord_dropCodeOf` —
  what those two compute at an arbitrary word.
* `Geb.CobhamFold.stepWord_codeOf_spell_mk`,
  `Geb.CobhamFold.stepWord_dropCodeOf_spell_mk` — what they recover from a
  spelling.

## References

* [Cobham1965]
* [Strahm2003]

## Tags

Cobham, ranked tree, destructor, self-delimiting, subterm
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

/-- The leading block of a word, as an expression of arity one: a constant
unary prefix of the alphabet's width makes the word a self-delimiting entry
whose payload is that block. -/
def codeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of takeEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The word past its leading block, by the same prefix. -/
def dropCodeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of dropEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The prefixed word, in the shape the payload primitives read. -/
private theorem stepWord_prefix (R : RankedAlphabet) (w : List Bool) :
    stepWord (prependOf (List.replicate R.width true ++ [false]) idOf) w =
      List.replicate R.width true ++ false :: w := by
  rw [stepWord_prependOf, stepWord_idOf, List.append_assoc]
  rfl

/-- The block reader truncates to the alphabet's width. -/
theorem stepWord_codeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (codeOf R) w = w.take R.width := by
  rw [codeOf, stepWord_comp1Of, stepWord_prefix, stepWord_takeEntryOf,
    takeEntrySem_replicate]

/-- Its complement drops the alphabet's width. -/
theorem stepWord_dropCodeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (dropCodeOf R) w = w.drop R.width := by
  rw [dropCodeOf, stepWord_comp1Of, stepWord_prefix, stepWord_dropEntryOf,
    dropEntrySem_replicate]

/-- At a spelling the block reader recovers the head symbol's block. -/
theorem stepWord_codeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (codeOf R) (R.spell (Term.mk R i ch)) = R.code i := by
  rw [stepWord_codeOf, spell_mk, List.take_left' (R.length_code i)]

/-- And its complement recovers the children's spellings. -/
theorem stepWord_dropCodeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (dropCodeOf R) (R.spell (Term.mk R i ch)) =
      (List.ofFn fun d ↦ R.spell (ch d)).flatten := by
  rw [stepWord_dropCodeOf, spell_mk, List.drop_left' (R.length_code i)]

end Geb.CobhamFold

end
```

`Geb.Mathlib.Data.W.Basic` is imported directly rather than reached through
the chain. `Fold.lean` imports it with a plain, non-public `import` — it needs
`WType.elim_unique` only inside a proof — so `WType.para` and `WType.para_mk`,
which Task 4 uses, are not re-exported to this module.
`GebTests/…/Boundary.lean` carries the same import beside its index import for
the same reason. `WType.toSigma` and `WType.ofSigma_toSigma`, which Task 9
uses, need no import of their own: `Geb/Mathlib/Data/Tree/Ranked/Basic.lean`
publicly imports `Mathlib.Data.W.Basic`.

- [ ] **Step 2: Add the index line**

In `Geb/Internal/Computability/CobhamFoldProto.lean`, after the `Initial`
import:

```lean
public import Geb.Internal.Computability.CobhamFoldProto.Initial
public import Geb.Internal.Computability.CobhamFoldProto.Destruct
```

- [ ] **Step 3: Build and repair**

```bash
lake build
```

Expected: no errors. `lake shake` is not run here and would report
`Destruct.lean`'s `public import …Initial` as removable until Task 7 uses
`flattenOf`; the import is correct and the final state is clean, which
Task 12's gate checks. Two shapes to expect if the build fails:

- `stepWord_prefix`'s `rfl` closes
  `(List.replicate R.width true ++ [false]) ++ w`
  against `List.replicate R.width true ++ false :: w` only after
  `List.append_assoc`; if the rewrite leaves `[false] ++ w`, add
  `List.singleton_append` to the rewrite list.
- `List.take_left'` and `List.drop_left'` take the length equation
  `(R.code i).length = R.width`, which `R.length_code i` supplies in that
  direction. If the elaborator wants the reverse, use
  `(R.length_code i).symm`.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'feat(cobham-term): read a spelling'\''s leading block'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 4: The paramorphism and its growth constant

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`
- Modify: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (remove the moved declarations)

**Interfaces:**

- Consumes: `Geb.CobhamFold.entryWord`, `Geb.CobhamFold.takeEntrySem`,
  `Geb.CobhamFold.dropEntrySem`, `Geb.CobhamFold.takeEntrySem_entryWord`,
  `Geb.CobhamFold.dropEntrySem_entryWord`,
  `Geb.CobhamFold.length_entryWord`,
  `Geb.CobhamFold.two_mul_length_takeEntrySem_add_length_dropEntrySem_le`
  (Task 2); `Geb.CobhamFold.Term.fold`, `Geb.CobhamFold.Term.fold_mk`;
  `RankedAlphabet.Term.induction`, `RankedAlphabet.spell_mk`;
  `WType.para`, `WType.para_mk`.
- Produces, in namespace `Geb.CobhamFold` (`ParaStep` as an `abbrev`):

```text
ParaStep (R : RankedAlphabet) : Type
algPara (R) (phi : ParaStep R) (i : Fin R.card) (f : Fin (R.arity i) → List Bool) : List Bool
dropEntry_algPara (R) (phi) (t : R.Term) : dropEntrySem ![Term.fold R (algPara R phi) t] = R.spell t
takeEntry_algPara (R) (phi) (i) (ch) : takeEntrySem ![Term.fold R (algPara R phi) (Term.mk R i ch)] = phi i fun d ↦ (R.spell (ch d), takeEntrySem ![Term.fold R (algPara R phi) (ch d)])
algPara_eq_para (R) (phi) (t) : takeEntrySem ![Term.fold R (algPara R phi) t] = WType.para (List Bool) (fun x ↦ phi x.1 fun d ↦ (R.spell (x.2 d).1, (x.2 d).2)) t
sum_ofFn_length_eq_length_flatten {n : ℕ} (g : Fin n → List Bool) : (List.ofFn fun d ↦ (g d).length).sum = ((List.ofFn g).flatten).length
growth_algPara (R) (phi) (cphi : ℕ) (hphi) (i) (f) : (algPara R phi i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + (2 * cphi + R.width + 1)
```

- [ ] **Step 1: Move the paramorphism in**

Append to `Destruct.lean`, before `end Geb.CobhamFold`, the five declarations
`Boundary.lean` carries, unchanged but for the namespace they now sit in:
`ParaStep`, `algPara`, `dropEntry_algPara`, `takeEntry_algPara` and
`algPara_eq_para`. Their statements and proofs are in
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`; copy them
verbatim, including their docstrings.

While copying, add `[Meertens1992]` to `algPara_eq_para`'s docstring, which
names `WType.para` as the existing recursion scheme without naming its
source; `Destruct.lean`'s `## References` lists the key from Task 4 Step 5,
and this is the declaration that cites it.

`algPara_eq_para`'s statement names `WType.para`'s implicit family arguments
`(α := Fin R.card) (β := fun i ↦ Fin (R.arity i))` and gives its carrier
`(List Bool)` explicitly; keep all three, since the families are not
inferable from the term.

- [ ] **Step 2: Remove them from `Boundary.lean`**

Delete `ParaStep`, `algPara`, `dropEntry_algPara`, `takeEntry_algPara` and
`algPara_eq_para` with their docstrings, and the four `## Main definitions` /
`## Main statements` bullets naming them (`ParaStep` and `algPara` share
one). Amend the module docstring in the same edit, so the commit leaves no
docstring describing declarations the module no longer holds: drop the
summary paragraph beginning "`algPara` carries a subterm's spelling", and
remove the `## References` section entirely, heading included.
`[Meertens1992]` was its only remaining entry — the constructor branch
already took `[GambinoHyland2004]` — and `docs/rules/lean-coding.md`
§ Documentation requires a vacuous section to be omitted, never left as a
bare heading. Replace the title block, which the constructor branch left
naming a paramorphism this step removes, with:

```text
# The delimited-children algebra, at the semantic layer

The algebra from which a subterm's spelling is recovered.

`algCh` delimits each child's spelling, and the delimiting does not nest:
each level reads only the spelling half of a child's value, so a subterm's
boundary is reached by a fold.
```

drop `paramorphism` from `## Tags`, leaving
`Cobham, ranked tree, subterm, self-delimiting`. Two surviving bullets take
their antecedents from text this step removes — `algCh`'s reads "one of its
instances", and the shared `dropEntry_algCh` / `takeEntry_algCh` bullet reads
"those two at the delimited-children instance" — so reword them to stand
alone:

```text
* `GebTests.CobhamFold.algCh` — the delimited-children algebra.
* `GebTests.CobhamFold.dropEntry_algCh`,
  `GebTests.CobhamFold.takeEntry_algCh` — its value's two halves.
```

Then drop the
`public import Geb.Mathlib.Data.W.Basic` line: `algPara_eq_para` was its only
user, so from this commit it is an import `lake shake` would reject.

`algCh` in `Boundary.lean` is defined as `algPara R fun _ g ↦ ...` and now
resolves to the moved `Geb.CobhamFold.algPara` through the module's
`open Geb.CobhamFold`, so it and its two corollaries keep building. That is
what Step 4 checks.

- [ ] **Step 3: Add the length lemma and the general growth constant**

```lean
/-- A family's lengths sum to the length of its flattening. -/
theorem sum_ofFn_length_eq_length_flatten {n : ℕ} (g : Fin n → List Bool) :
    (List.ofFn fun d ↦ (g d).length).sum = ((List.ofFn g).flatten).length := by
  rw [List.length_flatten, List.map_ofFn]
  rfl

/-- The weighted length bound, over a list rather than a family: the payloads
counted twice and the remainders together fit inside the words. -/
private theorem two_mul_length_flatten_take_add_drop_le : ∀ l : List (List Bool),
    2 * ((l.map fun x ↦ takeEntrySem ![x]).flatten).length +
        ((l.map fun x ↦ dropEntrySem ![x]).flatten).length ≤ l.flatten.length :=
  List.rec (Nat.le_refl 0) fun a t ih ↦ by
    have h := two_mul_length_takeEntrySem_add_length_dropEntrySem_le a
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    omega

/-- A paramorphism whose step is bounded by its children's values, plus a
constant, meets the per-symbol growth condition at `2 * cphi + R.width + 1`,
attained at a nullary symbol. The constant is unconditional because the
weighted bound holds at an arbitrary word rather than only at a fold's
value. -/
theorem growth_algPara (R : RankedAlphabet) (phi : ParaStep R) (cphi : ℕ)
    (hphi : ∀ (i : Fin R.card) (g : Fin (R.arity i) → List Bool × List Bool),
      (phi i g).length ≤ (List.ofFn fun d ↦ (g d).2.length).sum + cphi)
    (i : Fin R.card) (f : Fin (R.arity i) → List Bool) :
    (algPara R phi i f).length ≤
      (List.ofFn fun d ↦ (f d).length).sum + (2 * cphi + R.width + 1) := by
  have hstep := hphi i fun d ↦ (dropEntrySem ![f d], takeEntrySem ![f d])
  have hw := two_mul_length_flatten_take_add_drop_le (List.ofFn f)
  rw [algPara, List.length_append, length_entryWord, List.length_append,
    R.length_code, sum_ofFn_length_eq_length_flatten]
  simp only [List.map_ofFn, Function.comp_def, sum_ofFn_length_eq_length_flatten] at hstep hw ⊢
  omega
```

- [ ] **Step 4: Build both libraries and repair**

```bash
lake build
lake build GebTests
```

Expected: no errors and no warnings. Repairs to expect:

- `Function.comp_def` in the `simp only` is what makes `omega` see one atom
  rather than two. `List.map_ofFn` rewrites to `List.ofFn (f ∘ g)`, where the
  goal has `List.ofFn fun d ↦ f (g d)`; the two are defeq but not
  syntactically equal, so without it `omega` reports the flattened lengths as
  unrelated atoms. `Function.comp` is the wrong name here — it is rejected as
  an unused `simp` argument, which `weak.warningAsError` turns into an error.
- `sum_ofFn_length_eq_length_flatten` appears once in the `rw` list, not
  twice: after the first rewrite no `(List.ofFn fun d ↦ (? d).length).sum`
  remains, and a second would fail with "Did not find an occurrence of the
  pattern".

- [ ] **Step 5: Extend the module docstring**

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.ParaStep`, `Geb.CobhamFold.algPara` — the paramorphism's
  step, and the paramorphism as a fold.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.dropEntry_algPara` — the value's second half is the
  spelling, whatever the step.
* `Geb.CobhamFold.takeEntry_algPara` — the paramorphism's defining equation.
* `Geb.CobhamFold.algPara_eq_para` — it is `WType.para` at the step that sees
  each child's spelling in place of the subtree.
* `Geb.CobhamFold.sum_ofFn_length_eq_length_flatten`,
  `Geb.CobhamFold.growth_algPara` — a family's total length, and the
  per-symbol growth a bounded step gives.
```

Add to the summary, after the paragraph on `codeOf`:

```text
`algPara` is the paramorphism as a fold, at a carrier pairing a subterm's
spelling with the step's value, the value delimited so the two are separable.
The delimiting does not nest: each level reads only the spelling half of a
child's value, so a subterm's boundary is reached by a fold rather than at
the cost a nested encoding would carry. `WType.para` already exists, so no
recursion scheme is introduced here; `algPara` is the encoding at which it is
computed, and `algPara_eq_para` identifies the two.
```

Add `* [Meertens1992]` to `## References`, between `[Cobham1965]` and
`[Strahm2003]` so the keys stay alphabetical, and `paramorphism` to
`## Tags`.

- [ ] **Step 6: Commit**

```bash
jj commit -m 'feat(cobham-term): add the paramorphism at the bitstring representation'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 5: The delimited-children algebra and its invariant

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`
- Modify: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (remove `algCh`, `dropEntry_algCh`, `takeEntry_algCh`)

**Interfaces:**

- Consumes: everything Task 4 produced; `Geb.CobhamFold.stackWordV`.
- Produces, in namespace `Geb.CobhamFold`:

```text
algCh (R : RankedAlphabet) : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool
dropEntry_algCh (R) (t : R.Term) : dropEntrySem ![Term.fold R (algCh R) t] = R.spell t
takeEntry_algCh (R) (i) (ch) : takeEntrySem ![Term.fold R (algCh R) (Term.mk R i ch)] = (List.ofFn fun d ↦ entryWord (R.spell (ch d))).flatten
stackWordV_ofFn {n : ℕ} (g : Fin n → List Bool) : stackWordV (List.ofFn g) = (List.ofFn fun d ↦ entryWord (g d)).flatten
dropEntrySem_algCh (R) (i) (f) : dropEntrySem ![algCh R i f] = R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten
length_algCh (R) (i) (f) : (algCh R i f).length = 5 * ((List.ofFn fun d ↦ dropEntrySem ![f d]).flatten).length + 2 * R.arity i + 1 + R.width
five_mul_length_dropEntrySem_algCh_le (R) (i) (f) : 5 * (dropEntrySem ![algCh R i f]).length + 1 ≤ (algCh R i f).length + 4 * R.width
```

`five_mul_length_dropEntrySem_algCh_le` needs no induction hypothesis: it
holds at arbitrary arguments, with equality at a nullary symbol.

- [ ] **Step 1: Move `algCh` and its two laws in**

Copy `algCh`, `dropEntry_algCh` and `takeEntry_algCh` from `Boundary.lean`
into `Destruct.lean`, verbatim with their docstrings, and delete them from
`Boundary.lean` together with the two bullets naming them (`dropEntry_algCh`
and `takeEntry_algCh` share one). Replace the title block again, since the
module now holds only the child reader and the samples:

```text
# A subterm's spelling, on samples

`GebTests.CobhamFold.childSem` at the two-symbol alphabet, and the fold's
value read against the term's node count.
```

`childSem` is still `GebTests.CobhamFold.childSem` here; Task 8 Step 8 moves
it and switches the namespace in this same sentence.

and delete the `## Main statements` heading with its last bullet: the module
holds no theorem from this commit until Task 10 deletes it, and
`docs/rules/lean-coding.md` § Documentation has a vacuous section omitted
rather than left as a bare heading. Drop `self-delimiting` from `## Tags`,
which named `algCh`'s delimiting and goes with it, leaving
`Cobham, ranked tree, subterm`; Task 10 replaces the module outright.

`algCh R = algPara R fun _ g ↦ (List.ofFn fun d ↦ entryWord (g d).1).flatten`
holds by definition, so the two laws stay one-line corollaries of
`dropEntry_algPara` and `takeEntry_algPara`.

- [ ] **Step 2: Add the flattening bridge and the two length computations**

```lean
/-- A family's delimited spelling is the stack layout at the list it names. -/
theorem stackWordV_ofFn {n : ℕ} (g : Fin n → List Bool) :
    stackWordV (List.ofFn g) = (List.ofFn fun d ↦ entryWord (g d)).flatten := by
  rw [stackWordV, List.flatMap_def, List.map_ofFn]
  rfl

/-- The value's second half is the symbol's block followed by the children's
own second halves, whatever the arguments. -/
theorem dropEntrySem_algCh (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    dropEntrySem ![algCh R i f] =
      R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten := by
  rw [algCh, algPara, dropEntrySem_entryWord]

/-- Its length, at arbitrary arguments: five times the children's second
halves, two bits per child, the sentinel and the block. -/
theorem length_algCh (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algCh R i f).length =
      5 * ((List.ofFn fun d ↦ dropEntrySem ![f d]).flatten).length +
        2 * R.arity i + 1 + R.width := by
  have hlen := length_stackWordV (List.ofFn fun d ↦ dropEntrySem ![f d])
  rw [stackWordV_ofFn, stackSize] at hlen
  rw [algCh, algPara, List.length_append, length_entryWord, List.length_append,
    R.length_code]
  simp only [List.length_ofFn] at hlen ⊢
  omega
```

- [ ] **Step 3: Add the invariant**

```lean
/-- Every value the delimited-children algebra produces carries its second
half within a fixed multiple of its own length. It needs no induction
hypothesis, holding at arbitrary arguments, and holds with equality at a
nullary symbol. This is what a potential argument runs over where the
per-symbol growth condition fails: `algCh` duplicates its children's
payloads, delimited and plain, so `|algCh R i f|` is bounded by a multiple of
the children's total rather than by that total plus a constant. -/
theorem five_mul_length_dropEntrySem_algCh_le (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    5 * (dropEntrySem ![algCh R i f]).length + 1 ≤
      (algCh R i f).length + 4 * R.width := by
  rw [dropEntrySem_algCh, List.length_append, R.length_code, length_algCh]
  omega
```

Reading the arithmetic: with `F` the flattened second halves' length, the
left side is `5 * (R.width + F) + 1` and the right is
`5 * F + 2 * R.arity i + 1 + R.width + 4 * R.width`, so the claim is
`0 ≤ 2 * R.arity i`.

- [ ] **Step 4: Build and repair**

```bash
lake build
lake build GebTests
```

Expected: no errors and no warnings. Repairs to expect:

- `List.flatMap_def` states `l.flatMap f = flatten (map f l)` and is `rfl`,
  so if the rewrite does not fire the whole lemma closes by
  `by rw [stackWordV, List.map_ofFn]; rfl`.
- `length_algCh` reuses `Geb.CobhamFold.length_stackWordV` rather than
  restating it: `stackWordV st` is `st.flatMap entryWord` and `stackSize st`
  is `st.flatten.length`, so that lemma already says an entry costs twice its
  payload plus one bit over a whole list. `stackWordV_ofFn` bridges the
  `List.ofFn` form. Its `simp only` takes `List.length_ofFn` alone: the
  `stackWordV_ofFn` rewrite has already put `hlen` in `List.ofFn`-of-lambda
  form, so `List.map_ofFn` and `Function.comp_def` have nothing to normalise
  and `linter.unusedSimpArgs` rejects them — the opposite of the three sites
  that do need `Function.comp_def`.

- [ ] **Step 5: Extend the module docstring**

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.algCh` — the delimited-children algebra, one instance of
  the paramorphism.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.dropEntry_algCh`, `Geb.CobhamFold.takeEntry_algCh` — the
  paramorphism's two laws at `Geb.CobhamFold.algCh`.
* `Geb.CobhamFold.length_algCh`,
  `Geb.CobhamFold.five_mul_length_dropEntrySem_algCh_le` — its length at
  arbitrary arguments, and the bound its outputs satisfy.
```

- [ ] **Step 6: Commit**

```bash
jj commit -m 'feat(cobham-term): bound the delimited-children algebra'\''s outputs'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 6: The linearity hypothesis

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Fold.lean`
  (`mem_stack_foldScanFinal`, after `foldScanFrom_cons`)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Variable.lean`
  (generalise the potential chain in place, re-deriving the existing forms)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`

**Interfaces:**

- Consumes: `Geb.CobhamFold.FoldScan`, `Geb.CobhamFold.foldScanStep`,
  `Geb.CobhamFold.foldScanFinal`, `Geb.CobhamFold.stackSize`,
  `Geb.CobhamFold.stackSize_cons`, `Geb.CobhamFold.stackSize_take_add_drop`,
  `Geb.CobhamFold.symOf`, `RankedAlphabet.decodeBits`;
  `RankedAlphabet.arity_le_maxArity`, `RankedAlphabet.width_pos`.
- Produces, in namespace `Geb.CobhamFold`:

```text
mem_stack_foldScanFinal (R) (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (P : α → Prop) (hpush) : ∀ (w : List Bool), ∀ v ∈ (foldScanFinal R alg w).stack, P v
potential_foldScanStep_le_of_invariant (R) (alg) (P) (c) (hgrow) (b) (s) (hs) : R.width * stackSize (foldScanStep R alg b s).stack + c * (foldScanStep R alg b s).buf.length ≤ R.width * stackSize s.stack + c * s.buf.length + c
potential_foldScanFinal_le_of_invariant (R) (alg) (P) (c) (hpush) (hgrow) : ∀ w, R.width * stackSize (foldScanFinal R alg w).stack + c * (foldScanFinal R alg w).buf.length ≤ c * w.length
stackSize_le_of_growth_of_invariant (R) (alg) (P) (c) (hpush) (hgrow) (w) : stackSize (foldScanFinal R alg w).stack ≤ c * w.length
chGrowth (R : RankedAlphabet) : ℕ
growth_algCh_of_dropEntrySem_le (R) (i) (f) (hf) : (algCh R i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + chGrowth R
stackSize_algCh_le (R) (w : List Bool) : stackSize (foldScanFinal R (algCh R) w).stack ≤ chGrowth R * w.length
```

This is the branch's one genuinely unproved piece. It is a proof argument of
`foldOutOfV`, so `childOf` cannot be defined until it is done, and
restricting to `RankedAlphabet.Binary.binRanked` does not avoid it: the
statement still quantifies over every word, with only the width and the
maximum arity becoming literals.

The potential chain is generalised in `Variable.lean` rather than restated
here. `Variable.lean`'s three lemmas take the growth condition at arbitrary
arguments, which `algCh` does not meet; each gains a predicate the scan's
stack values satisfy, and each existing form is re-derived from its
generalisation at the trivial predicate, so no consumer changes and nothing
is stated twice. `sum_ofFn_getElem` is already `private` in that module and
is used directly rather than restated. `Destruct.lean` is left with the three
declarations that are about `algCh`: `chGrowth`,
`growth_algCh_of_dropEntrySem_le` and `stackSize_algCh_le`.

- [ ] **Step 1: Carry the invariant along the scan**

This goes in `Fold.lean`, whose subject is the scan and its stack, after
`foldScanFrom_cons`. State it at that module's `variable {α : Type u}`, as
every other statement there is: the proof uses nothing carrier-specific, and
the `List Bool` specialisation is `Variable.lean`'s business. Add to that
module's `## Main statements`:

```text
* `Geb.CobhamFold.mem_stack_foldScanFinal` — every value on the scan's stack
  is one the algebra produced.
```

```lean
/-- Every value on the fold scan's stack is one the algebra produced: the
stack starts empty, and the completing pop is the only clause that pushes. -/
theorem mem_stack_foldScanFinal (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (P : α → Prop)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → α), P (alg i f)) :
    ∀ (w : List Bool), ∀ v ∈ (foldScanFinal R alg w).stack, P v :=
  List.rec (fun v hv ↦ absurd hv (by simp [foldScanFinal, foldScanFrom]))
    fun b u ih v hv ↦ by
    have hcons : foldScanFinal R alg (b :: u) =
        foldScanStep R alg b (foldScanFinal R alg u) := rfl
    rw [hcons, foldScanStep] at hv
    -- `foldScanFinal R alg u` is a term, not a local variable, so `obtain` on
    -- it would introduce fresh locals and rewrite neither `hv` nor `ih`. The
    -- named equation is what carries the split into both.
    rcases hfs : foldScanFinal R alg u with ⟨buf, stack, live⟩
    rw [hfs] at hv ih
    dsimp only at hv ih ⊢
    cases live
    · exact ih v hv
    · dsimp only at hv
      by_cases hlen : (b :: buf).length = R.width
      · rw [ite_eq_left hlen] at hv
        match hsym : symOf R (decodeBits (b :: buf)) with
        | none =>
          rw [hsym] at hv
          exact ih v hv
        | some i =>
          rw [hsym] at hv
          dsimp only at hv
          by_cases hst : R.arity i ≤ stack.length
          · rw [dite_eq_left hst] at hv
            rcases List.mem_cons.mp hv with h | h
            · exact h ▸ hpush i _
            · exact ih v (List.mem_of_mem_drop h)
          · rw [dite_eq_right hst] at hv
            exact ih v hv
      · rw [ite_eq_right hlen] at hv
        exact ih v hv
```

- [ ] **Step 2: Build and repair Step 1**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- The base case's `simp` needs `[foldScanFinal, foldScanFrom]`: the goal is
  `v ∉ (foldScanFinal R alg []).stack` and a bare `simp` will not unfold
  `foldScanFinal`, failing with "simp made no progress".
- The `rw [hsym] at hv` steps depend on `foldScanStep`'s `match` reducing
  once the symbol is named. If the rewrite does not fire, replace the
  `match hsym : ... with` by `cases hsym : symOf R (decodeBits (b :: buf))`
  and `simp only [hsym] at hv`.

- [ ] **Step 3: The potential step, with the growth condition restricted**

In `Variable.lean`, rename the existing `potential_foldScanStep_le` to
`potential_foldScanStep_le_of_invariant`, give it the two extra arguments,
and add the membership argument to its one `hgrow` application — the delta
line is marked below. Its proof is otherwise unchanged, so this is a
generalisation in place, not a second copy. Step 4 then re-derives the
original name from it.

```lean
/-- One step raises the potential `R.width * stackSize + c * |buf|` by at
most `c`, the growth condition assumed only of arguments the stack holds.
`Geb.CobhamFold.potential_foldScanStep_le` is this where the condition holds
at arbitrary arguments. -/
theorem potential_foldScanStep_le_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (b : Bool) (s : FoldScan (List Bool)) (hs : ∀ v ∈ s.stack, P v) :
    R.width * stackSize (foldScanStep R alg b s).stack +
        c * (foldScanStep R alg b s).buf.length ≤
      R.width * stackSize s.stack + c * s.buf.length + c := by
  obtain ⟨buf, stack, live⟩ := s
  dsimp only at hs
  rw [foldScanStep]
  dsimp only
  cases live
  · dsimp only
    omega
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [ite_eq_left hlen]
      have hbw : buf.length + 1 = R.width := by
        rw [List.length_cons] at hlen
        omega
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none =>
        dsimp only
        simp only [List.length_nil, Nat.mul_zero]
        omega
      | some i =>
        dsimp only
        by_cases hst : R.arity i ≤ stack.length
        · rw [dite_eq_left hst]
          dsimp only
          have hsum := sum_ofFn_getElem (R.arity i) stack hst
          -- the popped arguments are members of the stack, so `hs` supplies
          -- `P` at each
          have halg := hgrow i
            (fun d ↦ stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst))
            fun d ↦ hs _ (List.getElem_mem _)
          rw [hsum] at halg
          have hsplit := stackSize_take_add_drop stack (R.arity i)
          have hnew : stackSize ((alg i fun d ↦
              stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst)) ::
                stack.drop (R.arity i)) ≤ stackSize stack + c := by
            rw [stackSize_cons]
            omega
          have hmul : R.width * stackSize ((alg i fun d ↦
              stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst)) ::
                stack.drop (R.arity i)) ≤ R.width * (stackSize stack + c) :=
            Nat.mul_le_mul_left _ hnew
          rw [Nat.mul_add] at hmul
          have hcw : R.width * c = c * R.width := Nat.mul_comm _ _
          have hcb : c * buf.length + c = c * R.width := by
            rw [← hbw, Nat.mul_add, Nat.mul_one]
          simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
          omega
        · rw [dite_eq_right hst]
          dsimp only
          simp only [List.length_nil, Nat.mul_zero]
          omega
    · rw [ite_eq_right hlen]
      dsimp only
      have hcb : c * (buf.length + 1) = c * buf.length + c := by
        rw [Nat.mul_add, Nat.mul_one]
      simp only [List.length_cons]
      omega
```

If `obtain ⟨buf, stack, live⟩ := s` leaves `hs` stated about `s.stack`
rather than `stack`, replace the `obtain` by
`cases s with | mk buf stack live => ?_` so the substitution reaches the
hypothesis, or generalize `hs` first with `revert hs`.

- [ ] **Step 4: Re-derive the existing potential-step lemma**

Immediately after it, so `Variable.lean` still exports the name its own
consumers use, at the statement they use:

```lean
/-- One step raises the potential `R.width * stackSize + c * |buf|` by at most
`c`. Every clause but the completing pop leaves the stack alone, and the pop
adds at most `c` to it while clearing a block worth `R.width` bits. -/
theorem potential_foldScanStep_le (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (b : Bool) (s : FoldScan (List Bool)) :
    R.width * stackSize (foldScanStep R alg b s).stack +
        c * (foldScanStep R alg b s).buf.length ≤
      R.width * stackSize s.stack + c * s.buf.length + c :=
  potential_foldScanStep_le_of_invariant R alg (fun _ ↦ True) c
    (fun i f _ ↦ hgrow i f) b s fun _ _ ↦ trivial
```

- [ ] **Step 5: The potential over the whole input, and the bridge**

```lean
/-- The potential never exceeds `c` per input bit, the growth condition
assumed only of values satisfying `P`, which
`Geb.CobhamFold.mem_stack_foldScanFinal` carries along the scan.
`Geb.CobhamFold.potential_foldScanFinal_le` is this at the trivial
predicate. -/
theorem potential_foldScanFinal_le_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool), P (alg i f))
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c) :
    ∀ w : List Bool,
      R.width * stackSize (foldScanFinal R alg w).stack +
        c * (foldScanFinal R alg w).buf.length ≤ c * w.length :=
  List.rec (by
      rw [List.length_nil, Nat.mul_zero]
      exact Nat.le_of_eq rfl)
    fun b v ih ↦ by
      have hstep := potential_foldScanStep_le_of_invariant R alg P c hgrow b
        (foldScanFinal R alg v) (mem_stack_foldScanFinal R alg P hpush v)
      have hcons : foldScanFinal R alg (b :: v) =
          foldScanStep R alg b (foldScanFinal R alg v) := rfl
      have hc : c * (v.length + 1) = c * v.length + c := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hcons, List.length_cons]
      omega

/-- An algebra whose values satisfy an invariant under which it lengthens by
at most a constant per symbol keeps the pending values linear in the input.
`Geb.CobhamFold.stackSize_le_of_growth` is this at the trivial invariant. -/
theorem stackSize_le_of_growth_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool), P (alg i f))
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (w : List Bool) :
    stackSize (foldScanFinal R alg w).stack ≤ c * w.length := by
  have h := potential_foldScanFinal_le_of_invariant R alg P c hpush hgrow w
  have hm : stackSize (foldScanFinal R alg w).stack ≤
      R.width * stackSize (foldScanFinal R alg w).stack :=
    Nat.le_mul_of_pos_left _ R.width_pos
  omega
```

Then re-derive the two existing names from them, keeping their signatures
byte-identical to what `Variable.lean` has today and their docstrings' words
unchanged, so that
`GebTests`' `leafCountExpr` and `smashFree_leafCountExpr` — which pass
`stackSize_le_of_growth binRanked leafCountAlg 1 growth_leafCountAlg` — go on
elaborating unchanged:

```lean
/-- The potential never exceeds `c` per input bit. -/
theorem potential_foldScanFinal_le (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c) :
    ∀ w : List Bool,
      R.width * stackSize (foldScanFinal R alg w).stack +
        c * (foldScanFinal R alg w).buf.length ≤ c * w.length :=
  potential_foldScanFinal_le_of_invariant R alg (fun _ ↦ True) c
    (fun _ _ ↦ trivial) fun i f _ ↦ hgrow i f

/-- An algebra that lengthens by at most a constant per symbol keeps the
pending values linear in the input, which is the hypothesis
`Geb.CobhamFold.length_foldSemV_le` takes. This is the bridge from a condition
on the algebra alone to the condition the recursion bound consumes. -/
theorem stackSize_le_of_growth (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (w : List Bool) :
    stackSize (foldScanFinal R alg w).stack ≤ c * w.length :=
  stackSize_le_of_growth_of_invariant R alg (fun _ ↦ True) c
    (fun _ _ ↦ trivial) (fun i f _ ↦ hgrow i f) w
```

`stackSize_le_of_growth` has consumers in `GebTests`;
`potential_foldScanStep_le` and `potential_foldScanFinal_le` have none once
it routes through the generalisation, and are kept as the module's documented
API, each a one-line instance rather than a second proof.

Add these to `Variable.lean`'s `## Main statements`, beside the three
unrestricted names it already lists; no entry is removed, since no existing
name changes:

```text
* `Geb.CobhamFold.potential_foldScanStep_le_of_invariant`,
  `Geb.CobhamFold.potential_foldScanFinal_le_of_invariant`,
  `Geb.CobhamFold.stackSize_le_of_growth_of_invariant` — the same three with
  the growth condition assumed only of values satisfying a predicate the
  scan's stack carries, which an algebra duplicating its children's payloads
  needs; the unrestricted forms are these at the trivial predicate.
```

- [ ] **Step 6: The constant and the instance**

These three are about `algCh`, so they go in `Destruct.lean`.

```lean
/-- The per-symbol growth the delimited-children algebra meets under its own
invariant, attained at a symbol of maximum arity whose children are all
nullary. -/
def chGrowth (R : RankedAlphabet) : ℕ :=
  4 * R.maxArity * R.width + R.maxArity + R.width + 1

/-- The children's second halves, bounded by their own lengths under the
invariant, over a list rather than a family. -/
private theorem five_mul_length_flatten_dropEntrySem_le (R : RankedAlphabet) :
    ∀ l : List (List Bool),
      (∀ x ∈ l, 5 * (dropEntrySem ![x]).length + 1 ≤ x.length + 4 * R.width) →
      5 * ((l.map fun x ↦ dropEntrySem ![x]).flatten).length + l.length ≤
        l.flatten.length + 4 * R.width * l.length :=
  List.rec (fun _ ↦ Nat.le_refl 0) fun a t ih h ↦ by
    have ha := h a List.mem_cons_self
    have ht := ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)
    -- `omega` atomises `4 * R.width * (t.length + 1)` and
    -- `4 * R.width * t.length` separately, so the step is supplied by hand.
    have hd : 4 * R.width * (t.length + 1) = 4 * R.width * t.length + 4 * R.width := by
      rw [Nat.mul_add, Nat.mul_one]
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons]
    omega

/-- The delimited-children algebra lengthens by at most `chGrowth R` per
symbol, at arguments satisfying the invariant its own outputs satisfy. It
does not meet the condition at arbitrary arguments: it duplicates its
children's payloads, delimited and plain. -/
theorem growth_algCh_of_dropEntrySem_le (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool)
    (hf : ∀ d, 5 * (dropEntrySem ![f d]).length + 1 ≤
      (f d).length + 4 * R.width) :
    (algCh R i f).length ≤
      (List.ofFn fun d ↦ (f d).length).sum + chGrowth R := by
  have hlist := five_mul_length_flatten_dropEntrySem_le R (List.ofFn f)
    (fun x hx ↦ by
      obtain ⟨d, hd⟩ := List.mem_ofFn.mp hx
      exact hd ▸ hf d)
  have harity : R.arity i ≤ R.maxArity := R.arity_le_maxArity i
  -- `omega` is linear: it atomises `4 * R.width * R.arity i` and
  -- `4 * R.maxArity * R.width` separately and has no rule taking
  -- `R.arity i ≤ R.maxArity` from one to the other, so the monotonicity and
  -- the commutation are supplied by hand.
  have hmono : 4 * R.width * R.arity i ≤ 4 * R.width * R.maxArity :=
    Nat.mul_le_mul_left _ harity
  have hcomm : 4 * R.width * R.maxArity = 4 * R.maxArity * R.width := by
    rw [Nat.mul_assoc, Nat.mul_comm R.width, ← Nat.mul_assoc]
  rw [length_algCh, chGrowth, sum_ofFn_length_eq_length_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn] at hlist ⊢
  omega

/-- The pending values stay linear in the input at the delimited-children
algebra, which is the hypothesis `Geb.CobhamFold.foldOutOfV` takes. The
per-symbol growth condition does not apply, so the bound runs through the
invariant `five_mul_length_dropEntrySem_algCh_le` and a potential argument
over it, which charges each input bit at most `chGrowth R` and so needs no
assumption about how the pending subterms are laid out. -/
theorem stackSize_algCh_le (R : RankedAlphabet) (w : List Bool) :
    stackSize (foldScanFinal R (algCh R) w).stack ≤ chGrowth R * w.length :=
  stackSize_le_of_growth_of_invariant R (algCh R)
    (fun v ↦ 5 * (dropEntrySem ![v]).length + 1 ≤ v.length + 4 * R.width)
    (chGrowth R) (five_mul_length_dropEntrySem_algCh_le R) (growth_algCh_of_dropEntrySem_le R) w
```

- [ ] **Step 7: Build and repair**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- `List.mem_ofFn` states `a ∈ List.ofFn f ↔ ∃ i, f i = a`; if the direction
  or the equation's orientation differs, adjust the `hd ▸ hf d` accordingly.
- `growth_algCh_of_dropEntrySem_le`'s `omega` needs three things and has
  them: the two monotonicity `have`s above, and `Function.comp_def` in the
  `simp only`. Without the last, `hlist` and the goal name the flattened
  second halves as `List.ofFn ((fun x ↦ dropEntrySem ![x]) ∘ f)` and
  `List.ofFn fun d ↦ dropEntrySem ![f d]`, two distinct atoms.

- [ ] **Step 8: Confirm the axiom discipline early**

```bash
lake lint
```

Expected: exit zero. This task is where a choice-dependent lemma is most
likely to slip in, through a `simp` or `omega` call reaching a `Nat` order
lemma outside the choice-free set. Run the linter here rather than only at
the end, so a taint is attributed to the lemma that introduced it.

- [ ] **Step 9: Extend the module docstring and commit**

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.chGrowth` — the per-symbol growth the delimited-children
  algebra meets under its own invariant.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.growth_algCh_of_dropEntrySem_le`,
  `Geb.CobhamFold.stackSize_algCh_le` — the per-symbol growth condition at
  `Geb.CobhamFold.algCh`, and the linearity hypothesis it discharges.
```

Add an `## Implementation notes` section, after `## Main statements`:

```text
## Implementation notes

`algCh` does not meet the per-symbol growth condition
`Geb.CobhamFold.stackSize_le_of_growth` consumes, and not because
`dropEntrySem` fails to shrink — `length_dropEntrySem_le` bounds its result
by its argument. It duplicates its children's payloads, delimited and plain,
so its length is bounded by a multiple of the children's total rather than by
that total plus a constant. A multiplicative condition alone would not give
the linearity hypothesis either, a fold whose values multiply at every level
being exponential in depth. The route taken instead is
`five_mul_length_dropEntrySem_algCh_le`, a property of the algebra's own
outputs that needs no induction hypothesis,
carried along the scan by `mem_stack_foldScanFinal` and consumed by a
potential argument in the shape
`Geb.CobhamFold.potential_foldScanStep_le`'s.

`Variable.lean` states the potential chain at a growth condition restricted
to values satisfying a predicate the scan's stack carries, and derives the
unrestricted forms from it at the trivial predicate. The restriction is what
`algCh` needs and what the unrestricted condition does not give.
```

```bash
jj commit -m 'feat(cobham-term): keep the delimited-children fold linear in its input'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 7: The delimited-children algebra as an expression

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Bound.lean`
  (`semAt_comp1Of`, beside `semAt_compOf`)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/SelfDelim.lean`
  (re-prove `stepWord_comp1Of` through it)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`

**Interfaces:**

- Consumes: `Geb.CobhamFold.flattenOf`, `Geb.CobhamFold.semAt_flattenOf`,
  `Geb.CobhamFold.semAt_compOf`, `Geb.CobhamFold.smashFreeBool_flattenOf`
  (all from `Initial.lean`, the constructor branch);
  `Geb.CobhamFold.entryWordOf`, `Geb.CobhamFold.stepWord_entryWordOf`,
  `Geb.CobhamFold.dropEntryOf`, `Geb.CobhamFold.projOf`,
  `Geb.CobhamFold.compOf`, `Geb.CobhamFold.concatCompOf`,
  `Geb.CobhamFold.comp1Of`, and the `smashFreeBool_*` lemmas for each.
- Produces, in namespace `Geb.CobhamFold`:

```text
algChOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i)
semAt_algChOf (R) (i) (f) : semAt (R.arity i) (algChOf R i).1.1 (algChOf R i).2 f = algCh R i f
smashFreeBool_algChOf (R) (i) : smashFreeBool (algChOf R i).1.1.1 = true
semAt_comp1Of {n : ℕ} (e : COf 1) (a : COf n) (x : Fin n → List Bool) : semAt n (comp1Of e a).1.1 (comp1Of e a).2 x = stepWord e (semAt n a.1.1 a.2 x)
```

`flattenOf` is reused through `compOf` rather than a new combinator: the
constructor branch's `flattenOf n` concatenates an arity's slots, and
composing it against a family of per-slot expressions concatenates their
values.

- [ ] **Step 1: Add the expression**

`concatCompOf n a b` puts `b`'s value first, so the delimited half is the
second argument and the block-and-payloads half the first.

There is no `semAt_comp1Of` in the tree — `SelfDelim.lean`'s
`stepWord_comp1Of` is arity-one on both sides and does not cover
`comp1Of dropEntryOf (projOf (R.arity i) d) : COf (R.arity i)`. It goes in
`Bound.lean` beside `comp1Of` itself and beside the constructor branch's
`semAt_compOf`, by the same reasoning that put that one there.
`Bound.lean`'s `## Main statements` lists none of the `semAt` family, so
neither name is added to it. Re-prove `SelfDelim.lean`'s `stepWord_comp1Of`
through it in the same edit, replacing its `congrArg … funext` body with
`semAt_comp1Of e a ![u]` and leaving its statement unchanged — the
constructor branch does exactly this for `stepWord_compOf`, and leaving both
would state one fact twice.

```lean
/-- An arity-one expression's meaning at an `n`-ary argument.
`Geb.CobhamFold.stepWord_comp1Of` is this at arity one. -/
theorem semAt_comp1Of {n : ℕ} (e : COf 1) (a : COf n) (x : Fin n → List Bool) :
    semAt n (comp1Of e a).1.1 (comp1Of e a).2 x =
      stepWord e (semAt n a.1.1 a.2 x) :=
  congrArg (semAt 1 e.1.1 e.2) (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The delimited-children algebra as an expression of Cobham's class. Each
slot contributes its own second half, plain in the first argument and
delimited in the second; `Geb.CobhamFold.flattenOf` concatenates a family
through `Geb.CobhamFold.compOf`, so no new combinator is introduced. -/
def algChOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i) :=
  concatCompOf (R.arity i)
    (prependOf (R.code i)
      (compOf (flattenOf (R.arity i)) fun d ↦
        comp1Of dropEntryOf (projOf (R.arity i) d)))
    (comp1Of entryWordOf
      (compOf (flattenOf (R.arity i)) fun d ↦
        comp1Of entryWordOf (comp1Of dropEntryOf (projOf (R.arity i) d))))

/-- The expression computes the algebra. -/
theorem semAt_algChOf (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    semAt (R.arity i) (algChOf R i).1.1 (algChOf R i).2 f = algCh R i f := by
  rw [algChOf, semAt_concatCompOf, semAt_prependOf, semAt_comp1Of,
    semAt_compOf, semAt_compOf, semAt_flattenOf, semAt_flattenOf, algCh,
    algPara]
  simp only [semAt_comp1Of, semAt_projOf, stepWord_dropEntryOf,
    stepWord_entryWordOf]
```

- [ ] **Step 2: Build and repair**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- The `semAt_comp1Of` before the first `semAt_compOf` is not optional. The
  take-half branch is `comp1Of entryWordOf (…)`, and `comp1Of e a` is only
  definitionally `compOf e fun _ ↦ a`, so without it the second
  `rw [semAt_compOf]` fails with "Did not find an occurrence of the pattern",
  with a type-mismatch note about `COf (R.arity i)` against
  `{ e // e.arity = R.arity i }`.

- [ ] **Step 3: Add smash-freeness**

```lean
/-- The expression carries no `smash`, which is
`Geb.CobhamFold.smashFree_foldOutExprV`'s hypothesis at this algebra. -/
theorem smashFreeBool_algChOf (R : RankedAlphabet) (i : Fin R.card) :
    smashFreeBool (algChOf R i).1.1.1 = true :=
  smashFreeBool_concatCompOf (R.arity i) _ _
    (smashFreeBool_prependOf _ _
      (smashFreeBool_compOf _ _ (smashFreeBool_flattenOf (R.arity i))
        fun d ↦ smashFreeBool_comp1Of _ _ smashFreeBool_dropEntryOf
          (smashFreeBool_projOf (R.arity i) d)))
    (smashFreeBool_comp1Of _ _ smashFreeBool_entryWordOf
      (smashFreeBool_compOf _ _ (smashFreeBool_flattenOf (R.arity i))
        fun d ↦ smashFreeBool_comp1Of _ _ smashFreeBool_entryWordOf
          (smashFreeBool_comp1Of _ _ smashFreeBool_dropEntryOf
            (smashFreeBool_projOf (R.arity i) d))))
```

- [ ] **Step 4: Build, extend the docstring, commit**

```bash
lake build
```

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.algChOf` — that algebra as an expression of the class.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.semAt_algChOf`, `Geb.CobhamFold.smashFreeBool_algChOf` —
  what `Geb.CobhamFold.algChOf` computes, and that it carries no `smash`.
```

Add `smash-free` to `## Tags`.

```bash
jj commit -m 'feat(cobham-term): express the delimited-children algebra'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 8: The child reader

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/SelfDelim.lean`
  (drop `private` from `take_succ_append_take_one`, so Step 1's truncation
  split can be derived from it)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Variable.lean`
  (Step 1's two remainder-bearing stack-reading lemmas, and their two
  `## Main statements` bullets)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`
- Modify: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (Step 8 removes `childSem`)

**Interfaces:**

- Consumes: everything Tasks 4 to 7 produced; `Geb.CobhamFold.foldOutOfV`,
  `Geb.CobhamFold.foldOutSemV_eq`, `Geb.CobhamFold.outWordV`,
  `Geb.CobhamFold.foldOut_spell`, `Geb.CobhamFold.entryOf`,
  `Geb.CobhamFold.dropEntriesOf`,
  `Geb.CobhamFold.stepWord_dropEntriesOf_succ`,
  `Geb.CobhamFold.takeEntrySem_replicate`,
  `Geb.CobhamFold.dropEntrySem_entryWord`,
  `Geb.CobhamFold.takeEntrySem_entryWord`,
  `Geb.CobhamFold.length_dropEntrySem_le`, `Geb.CobhamFold.stackWordV_cons`;
  `Geb.CobhamFold.smashFree_foldOutExprV`,
  `Geb.CobhamFold.smashFreeBool_entryOf`,
  `Geb.CobhamFold.smashFreeBool_takeEntryOf`,
  `Geb.CobhamFold.smashFreeBool_comp1Of` (`SmashFree.lean`).
- Produces, in namespace `Geb.CobhamFold`:

```text
chFoldOf (R : RankedAlphabet) : COf 1
childOf (R : RankedAlphabet) (j : ℕ) : COf 1
childSem (R : RankedAlphabet) (j : ℕ) (t : R.Term) : List Bool
childSem_mk (R) (i) (ch) (j) (h : j < R.arity i) : childSem R j (Term.mk R i ch) = R.spell (ch ⟨j, h⟩)
childSem_of_le (R) (i) (ch) (j) (h : R.arity i ≤ j) : childSem R j (Term.mk R i ch) = []
stepWord_childOf (R) (i) (ch) (j) (h : j < R.arity i) : stepWord (childOf R j) (R.spell (Term.mk R i ch)) = R.spell (ch ⟨j, h⟩)
stepWord_childOf_of_le (R) (i) (ch) (j) (h : R.arity i ≤ j) : stepWord (childOf R j) (R.spell (Term.mk R i ch)) = []
smashFreeBool_chFoldOf (R) : smashFreeBool (chFoldOf R).1.1.1 = true
smashFreeBool_childOf (R) (j : ℕ) : smashFreeBool (childOf R j).1.1.1 = true
```

together with the reading lemmas Step 1 adds, which the block above does not
list because they are stated there in full.

`childOf` is total. At `j ≥ R.arity i` the entry primitive runs past the
entries and yields the empty word, which is proved rather than assumed.

- [ ] **Step 1: Add the reading lemmas**

Two edits before the Lean below. In `SelfDelim.lean`, remove the `private`
marker from `take_succ_append_take_one` (line 540) so
`take_append_length_add_one` can derive from it — left private, the
derivation fails with ``Unknown identifier `take_succ_append_take_one` ``
and an unsolved goal — and add it to that module's `## Main statements`:

```text
* `Geb.CobhamFold.take_succ_append_take_one` — a truncation splits at its
  last bit.
```

Then `stepWord_dropEntriesOf_stackWordV_append` and
`stepWord_entryOf_stackWordV_append` go in `Variable.lean`, beside
`stepWord_dropEntriesOf_stackWordV` (line 220) and
`stepWord_entryOf_stackWordV` (line 233), which read the same layout at the
empty remainder. The two existing forms are not instances of the new ones —
they are total in `k` and `j`, where the remainder-bearing forms need
`k ≤ st.length` — so both stay, as the general and the total statement of one
notion rather than as two copies; the spec's § What exists says so. Add these
beside their totals in that module's `## Main statements`:

```text
* `Geb.CobhamFold.stepWord_dropEntriesOf_stackWordV_append`,
  `Geb.CobhamFold.stepWord_entryOf_stackWordV_append` — the same two reads at
  a stack layout followed by an arbitrary remainder, which each need the
  count to be within the stack.
```

The rest of this step's lemmas are about the entry primitives at short words
and about composition, and go in `Destruct.lean` with the branch's own work.

```lean
/-- Splitting a truncation one bit past a prefix.
`Geb.CobhamFold.take_succ_append_take_one` is the same split at an arbitrary
index. Neither reaches for `List.take_add`, which `SelfDelim.lean` records as
`Classical.choice`-dependent. -/
private theorem take_append_length_add_one (u rest : List Bool) :
    (u ++ rest).take (u.length + 1) = u ++ rest.take 1 := by
  rw [take_succ_append_take_one u.length (u ++ rest), List.take_left' rfl,
    List.drop_left' rfl]

/-- The presence marker is absorbed into the entry's unary prefix rather than
left beside it, so the payload read from a marked value is the value's own
payload followed by one further bit of what the entry leaves. -/
theorem takeEntrySem_cons_true (u rest : List Bool) :
    takeEntrySem ![true :: (entryWord u ++ rest)] = u ++ rest.take 1 := by
  have hshape : true :: (entryWord u ++ rest) =
      List.replicate (u.length + 1) true ++ false :: (u ++ rest) := by
    rw [entryWord, List.replicate_succ]
    simp only [List.cons_append, List.append_assoc]
  rw [hshape, takeEntrySem_replicate, take_append_length_add_one]

/-- Dropping as many entries as a stack layout holds leaves what follows
it. `Geb.CobhamFold.stepWord_dropEntriesOf_stackWordV` is this at the empty
remainder, where the hypothesis is unnecessary. -/
theorem stepWord_dropEntriesOf_stackWordV_append :
    ∀ (k : ℕ) (st : List (List Bool)) (rest : List Bool), k ≤ st.length →
      stepWord (dropEntriesOf k) (stackWordV st ++ rest) =
        stackWordV (st.drop k) ++ rest :=
  Nat.rec (fun st rest _ ↦ by rw [dropEntriesOf_zero, stepWord_idOf,
      List.drop_zero])
    fun k ih st rest h ↦ match st with
      | [] => absurd h (Nat.not_succ_le_zero k)
      | a :: t => by
        rw [stackWordV_cons, List.append_assoc, stepWord_dropEntriesOf_succ,
          dropEntrySem_entryWord, ih t rest (Nat.le_of_succ_le_succ h),
          List.drop_succ_cons]

/-- The `j`-th entry of a stack layout is its `j`-th value, whatever follows
the layout. `Geb.CobhamFold.stepWord_entryOf_stackWordV` is this at the empty
remainder, read through `List.headD`. -/
theorem stepWord_entryOf_stackWordV_append (j : ℕ) (st : List (List Bool))
    (rest : List Bool) (h : j < st.length) :
    stepWord (entryOf j) (stackWordV st ++ rest) = st[j] := by
  rw [stepWord_entryOf,
    stepWord_dropEntriesOf_stackWordV_append j st rest (Nat.le_of_lt h),
    List.drop_eq_getElem_cons h, stackWordV_cons, List.append_assoc,
    takeEntrySem_entryWord]

/-- The payload primitive reads nothing from a word of at most one bit. -/
theorem takeEntrySem_of_length_le_one : ∀ r : List Bool, r.length ≤ 1 →
    takeEntrySem ![r] = []
  | [], _ => takeEntrySem_nil
  | b :: t, h => by
    have ht : t = [] := List.eq_nil_of_length_eq_zero (by
      rw [List.length_cons] at h
      omega)
    rw [ht, takeEntrySem_cons]
    cases b
    · rw [ite_eq_right (by simp)]
    · rw [ite_eq_left rfl, takeEntrySem_nil, dropEntrySem_nil, firstBitSem_eq]
      rfl

/-- Dropping entries never lengthens a word. -/
theorem length_stepWord_dropEntriesOf_le : ∀ (k : ℕ) (r : List Bool),
    (stepWord (dropEntriesOf k) r).length ≤ r.length :=
  Nat.rec (fun r ↦ by rw [dropEntriesOf_zero, stepWord_idOf])
    fun k ih r ↦ by
      rw [stepWord_dropEntriesOf_succ]
      exact Nat.le_trans (ih _) (length_dropEntrySem_le r)

/-- Dropping entries composes. -/
theorem stepWord_dropEntriesOf_add : ∀ (n k : ℕ) (x : List Bool),
    stepWord (dropEntriesOf (n + k)) x =
      stepWord (dropEntriesOf k) (stepWord (dropEntriesOf n) x) :=
  Nat.rec (fun k x ↦ by rw [Nat.zero_add, dropEntriesOf_zero, stepWord_idOf])
    fun n ih k x ↦ by
      rw [Nat.succ_add, stepWord_dropEntriesOf_succ, ih k,
        stepWord_dropEntriesOf_succ]
```

- [ ] **Step 2: Build and repair the reading lemmas**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- `List.eq_nil_of_length_eq_zero` may be spelled
  `List.length_eq_zero_iff.mp`; confirm with `lean_local_search`.
- `List.drop_eq_getElem_cons` is used by `Variable.lean`'s `headD_drop`, so
  it resolves; its argument is the bound `h : j < st.length`.
- `takeEntrySem_of_length_le_one`'s trailing `rfl` is required, not
  defensive: `firstBitSem_eq` leaves a `match [] with …` that `rw`'s
  reducible-only closing `rfl` does not discharge, and the step reports
  "unsolved goals" without it.

- [ ] **Step 3: Add the fold's shape at a constructed term**

```lean
/-- The fold's value at a constructed term, in the shape the entry
primitives read: the children's delimited spellings as one entry, then the
symbol's block and the children's spellings plain. -/
theorem fold_algCh_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    Term.fold R (algCh R) (Term.mk R i ch) =
      entryWord (stackWordV (List.ofFn fun d ↦ R.spell (ch d))) ++
        (R.code i ++ (List.ofFn fun d ↦ R.spell (ch d)).flatten) := by
  rw [Term.fold_mk, algCh, algPara, stackWordV_ofFn]
  exact congrArg (fun g ↦ entryWord ((List.ofFn fun d ↦ entryWord (g d)).flatten) ++
      (R.code i ++ (List.ofFn g).flatten))
    (funext fun d ↦ dropEntry_algPara R _ (ch d))
```

- [ ] **Step 4: Add the semantic child reader**

These two go through `Geb.CobhamFold.stepWord_entryOf_stackWordV`, which
`Variable.lean` already carries in the form they need. The `…_append` forms
Step 1 adds are needed only at the expression layer, in Step 5, where the
readout's presence marker leaves a trailing bit past the entries.

```lean
/-- The `j`-th child's spelling, read from a term's fold value. -/
def childSem (R : RankedAlphabet) (j : ℕ) (t : R.Term) : List Bool :=
  stepWord (entryOf j) (takeEntrySem ![Term.fold R (algCh R) t])

/-- It recovers the `j`-th child's spelling. -/
theorem childSem_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) (j : ℕ) (h : j < R.arity i) :
    childSem R j (Term.mk R i ch) = R.spell (ch ⟨j, h⟩) := by
  rw [childSem, takeEntry_algCh, ← stackWordV_ofFn,
    stepWord_entryOf_stackWordV,
    List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact h)]
  exact List.getElem_ofFn _

/-- And returns the empty word past the last child, so it is total. -/
theorem childSem_of_le (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) (j : ℕ) (h : R.arity i ≤ j) :
    childSem R j (Term.mk R i ch) = [] := by
  rw [childSem, takeEntry_algCh, ← stackWordV_ofFn,
    stepWord_entryOf_stackWordV,
    List.drop_eq_nil_of_le (by rw [List.length_ofFn]; exact h)]
  rfl
```

- [ ] **Step 5: Add the expression-layer child reader**

```lean
/-- The delimited-children fold as an expression, at its declared arity. The
multiplier is `foldOutOfV`'s bound taken with equality, so it carries no
hypothesis of its own. -/
def chFoldOf (R : RankedAlphabet) : COf 1 :=
  foldOutOfV R (algChOf R) (algCh R) (semAt_algChOf R) (2 * chGrowth R + 2)
    (chGrowth R) (stackSize_algCh_le R) (Nat.le_refl _)

/-- The `j`-th child's spelling, as an expression of Cobham's class: the
`j`-th entry of the fold's payload. -/
def childOf (R : RankedAlphabet) (j : ℕ) : COf 1 :=
  comp1Of (entryOf j) (comp1Of takeEntryOf (chFoldOf R))

/-- The fold expression's value, spelled by `Geb.CobhamFold.outWordV`. -/
theorem stepWord_chFoldOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (chFoldOf R) w = outWordV (foldOut R (algCh R) w) :=
  foldOutSemV_eq R (algChOf R) (algCh R) (semAt_algChOf R)
    (2 * chGrowth R + 2) (chGrowth R) (stackSize_algCh_le R) (Nat.le_refl _) w

/-- The `j`-th child's spelling, recovered from the spelling of the term. -/
theorem stepWord_childOf (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) (j : ℕ) (h : j < R.arity i) :
    stepWord (childOf R j) (R.spell (Term.mk R i ch)) = R.spell (ch ⟨j, h⟩) := by
  have hlen : (List.ofFn fun d ↦ R.spell (ch d)).length = R.arity i :=
    List.length_ofFn
  rw [childOf, stepWord_comp1Of, stepWord_comp1Of, stepWord_takeEntryOf,
    stepWord_chFoldOf, foldOut_spell]
  change stepWord (entryOf j)
    (takeEntrySem ![true :: Term.fold R (algCh R) (Term.mk R i ch)]) = _
  rw [fold_algCh_mk, takeEntrySem_cons_true,
    stepWord_entryOf_stackWordV_append j _ _ (by rw [hlen]; exact h),
    List.getElem_ofFn]

/-- And the empty word past the last child, so the expression is total. -/
theorem stepWord_childOf_of_le (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) (j : ℕ) (h : R.arity i ≤ j) :
    stepWord (childOf R j) (R.spell (Term.mk R i ch)) = [] := by
  have hlen : (List.ofFn fun d ↦ R.spell (ch d)).length = R.arity i :=
    List.length_ofFn
  have hshort : ((R.code i ++
      (List.ofFn fun d ↦ R.spell (ch d)).flatten).take 1).length ≤ 1 :=
    Nat.le_trans (Nat.le_of_eq List.length_take) (Nat.min_le_left 1 _)
  rw [childOf, stepWord_comp1Of, stepWord_comp1Of, stepWord_takeEntryOf,
    stepWord_chFoldOf, foldOut_spell]
  change stepWord (entryOf j)
    (takeEntrySem ![true :: Term.fold R (algCh R) (Term.mk R i ch)]) = _
  rw [fold_algCh_mk, takeEntrySem_cons_true, stepWord_entryOf,
    ← Nat.add_sub_cancel' h, stepWord_dropEntriesOf_add,
    stepWord_dropEntriesOf_stackWordV_append (R.arity i) _ _ (by rw [hlen]),
    List.drop_eq_nil_of_le (Nat.le_of_eq hlen), stackWordV_nil,
    List.nil_append]
  exact takeEntrySem_of_length_le_one _
    (Nat.le_trans (length_stepWord_dropEntriesOf_le _ _) hshort)
```

- [ ] **Step 6: Build and repair**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- `Nat.le_refl _` discharges `2 * chGrowth R + 2 ≤ 2 * chGrowth R + 2`
  outright, the multiplier being written inline rather than behind a name the
  elaborator would have to unfold.
- `stepWord_chFoldOf`'s term proof relies on `stepWord (chFoldOf R) w` being
  definitionally `foldOutSemV ... ![w]`; if the elaborator does not see it,
  prove it `by rw [stepWord]; exact foldOutSemV_eq ...` or insert
  `show foldOutSemV ... ![w] = _`.
- `outWordV (some a) = true :: a` holds by `rfl`; the `change` steps are
  what put the goal in that form. If `change` fails, `rw [outWordV]`.

- [ ] **Step 7: Place the expressions in the subalgebra**

`smashFreeBool_algChOf` is the hypothesis, not the conclusion:
`Cobham.SmashFree e` is `smashFreeBool e.1.1 = true` at `e : Cobham.C`, and
`smashFreeBool_algChOf` speaks of the algebra's expression, not the fold's.
Without these two the fourth obligation is discharged and consumed by
nothing, and no expression this branch builds is shown to lie in the
subalgebra.

```lean
/-- The delimited-children fold carries no `smash`, its algebra's own
expressions carrying none. -/
theorem smashFreeBool_chFoldOf (R : RankedAlphabet) :
    smashFreeBool (chFoldOf R).1.1.1 = true :=
  smashFree_foldOutExprV R (algChOf R) (smashFreeBool_algChOf R) (algCh R)
    (semAt_algChOf R) (2 * chGrowth R + 2) (chGrowth R) (stackSize_algCh_le R)
    (Nat.le_refl _)

/-- So does the child reader, so with [Strahm2003] Theorem 1(2)'s
left-to-right inclusion it is computable simultaneously in polynomial time
and linear space. -/
theorem smashFreeBool_childOf (R : RankedAlphabet) (j : ℕ) :
    smashFreeBool (childOf R j).1.1.1 = true :=
  smashFreeBool_comp1Of _ _ (smashFreeBool_entryOf j)
    (smashFreeBool_comp1Of _ _ smashFreeBool_takeEntryOf
      (smashFreeBool_chFoldOf R))
```

`Cobham.SmashFree e` is by definition `smashFreeBool e.1.1 = true`, so these
two are already the membership statements and no `SmashFree`-spelled
restatement is added: it would be definitionally the same theorem twice.
`smashFree_foldOutExprV` concludes `SmashFree (foldOutExprV …)`, which
unfolds to `smashFreeBool (foldOutOfV …).1.1.1 = true`; `chFoldOf R` is that
`foldOutOfV` application, so the term typechecks without a bridge.

```bash
lake build
```

Expected: no errors.

- [ ] **Step 8: Remove `childSem` from `Boundary.lean`**

`childSem` now lives in `Destruct.lean`. Delete its `def` and docstring from
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`, together
with its `## Main definitions` bullet, and amend the summary's first sentence
to name only what the module still holds:

```text
`Geb.CobhamFold.childSem` at the two-symbol alphabet, checked by `#guard`,
and the fold's value read against the term's node count.
```

The three `#guard`s that name `childSem` stay where they are; they resolve to
the moved declaration through that module's `open Geb.CobhamFold`, and Task
10 moves them into the new test module.

```bash
lake build GebTests
```

Expected: no errors and no warnings, the `#guard`s still evaluating.

- [ ] **Step 9: Extend the module docstring and commit**

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.chFoldOf` — the delimited-children fold as an expression.
* `Geb.CobhamFold.childSem`, `Geb.CobhamFold.childOf` — a child's spelling,
  read from a fold's value and read by an expression.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.takeEntrySem_cons_true` — the presence marker is absorbed
  into the entry's unary prefix, so one further bit is read from what follows
  the entry.
* `Geb.CobhamFold.fold_algCh_mk` — the fold's value at a constructed term.
* `Geb.CobhamFold.childSem_mk`, `Geb.CobhamFold.childSem_of_le`,
  `Geb.CobhamFold.stepWord_childOf`,
  `Geb.CobhamFold.stepWord_childOf_of_le` — the child reader recovers a
  child's spelling and is total.
* `Geb.CobhamFold.smashFreeBool_chFoldOf`,
  `Geb.CobhamFold.smashFreeBool_childOf` — the fold and the child reader
  carry no `smash`, which is what `Cobham.SmashFree` names.
```

Add to `## Implementation notes`:

```text
`Geb.CobhamFold.foldOutExprV`'s readout emits `Geb.CobhamFold.outWordV`,
which prefixes a presence marker. The marker is absorbed into the entry's
unary prefix rather than left beside it, so one further bit is read from what
follows the entry. Each equation is therefore stated in the "entries followed
by an arbitrary remainder" form, which `takeEntrySem` at an `entryWord`
tolerates, and the case past the last child is proved against that extra bit
rather than in its absence.
```

```bash
jj commit -m 'feat(cobham-term): read a subterm'\''s spelling inside the class'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 9: The inverse laws

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`

**Interfaces:**

- Consumes: `WType.toSigma`, `WType.ofSigma_toSigma` (`Mathlib.Data.W.Basic`);
  `Geb.CobhamFold.mkOf`, `Geb.CobhamFold.semAt_mkOf`,
  `Geb.CobhamFold.algMk` (`Initial.lean`);
  `RankedAlphabet.parse_eq_some_iff`, `RankedAlphabet.spell_mk`.
- Produces, in namespace `Geb.CobhamFold`:

```text
toSigma_mk (R : RankedAlphabet) (i : Fin R.card) (ch : Fin (R.arity i) → R.Term) : WType.toSigma (Term.mk R i ch) = ⟨i, ch⟩
semAt_mkOf_spell (R) (i) (ch) : semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 (fun d ↦ R.spell (ch d)) = R.spell (Term.mk R i ch)
semAt_mkOf_childOf (R) (i) (ch) (w) (hw : R.parse w = some (Term.mk R i ch)) : semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 (fun d ↦ stepWord (childOf R d.val) w) = w
```

Three statements make up the expression layer of the inverse laws:
`semAt_mkOf_spell`, that the constructor at the children's spellings is the
spelling of the constructed term; that `codeOf` and `childOf` recover the
symbol and the children's spellings, which Tasks 3 and 8 already delivered;
and `semAt_mkOf_childOf`, the round trip.

Under the preorder encoding the structure map is the identity on
representations, `spell_mk` stating that a symbol's block followed by its
children's spellings is the spelling of the term they build. The content of
the inverse laws is therefore that a valid word determines the symbol and the
children's spellings.

- [ ] **Step 1: Add the term-algebra half**

`WType.toSigma` is mathlib's destructor; the one statement this branch adds
at that layer bridges it to `Term.mk`, which mathlib does not know. The other
law is `WType.ofSigma_toSigma`, cited rather than restated.

```lean
/-- The term algebra's destructor at the `RankedAlphabet.Term.mk`
presentation. `WType.ofSigma_toSigma` is the other inverse law, which mathlib
already carries. -/
theorem toSigma_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    WType.toSigma (Term.mk R i ch) = ⟨i, ch⟩ := rfl
```

- [ ] **Step 2: Add the constructor at the children's spellings**

```lean
/-- The constructor's expression at the children's spellings is the spelling
of the term they build. Under the preorder encoding the structure map is the
identity on representations, which is what `RankedAlphabet.spell_mk`
states. -/
theorem semAt_mkOf_spell (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 (fun d ↦ R.spell (ch d)) =
      R.spell (Term.mk R i ch) := by
  rw [semAt_mkOf, algMk, ← spell_mk]
```

- [ ] **Step 3: Add the round trip**

```lean
/-- The constructor at the children the destructor reads returns the word.
It is stated under `R.parse w = some (Term.mk R i ch)` with `i` given rather
than read, so no dispatch over the block is needed; `Geb.CobhamFold.childOf`
and `Geb.CobhamFold.mkOf` are total and return an unspecified word off the
recognized language. -/
theorem semAt_mkOf_childOf (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) (w : List Bool)
    (hw : R.parse w = some (Term.mk R i ch)) :
    semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2
        (fun d ↦ stepWord (childOf R d.val) w) = w := by
  have hspell : R.spell (Term.mk R i ch) = w := R.parse_eq_some_iff.mp hw
  have hchild : (fun d : Fin (R.arity i) ↦ stepWord (childOf R d.val) w) =
      fun d ↦ R.spell (ch d) := by
    funext d
    rw [← hspell, stepWord_childOf R i ch d.val d.isLt]
  rw [semAt_mkOf, algMk, hchild, ← spell_mk, hspell]
```

- [ ] **Step 4: Build and repair**

```bash
lake build
```

Expected: no errors. Repairs to expect:

- `stepWord_childOf R i ch d.val d.isLt` returns
  `R.spell (ch ⟨d.val, d.isLt⟩)`; `Fin.eta` closes the gap to
  `R.spell (ch d)`. If `rw` leaves the anonymous constructor, append
  `Fin.eta` to the rewrite list or use `congrArg (R.spell ∘ ch) (Fin.eta d _)`.
- `toSigma_mk`'s `rfl` needs `WType.toSigma` to reduce at `WType.mk`, which
  it does: `Term.mk R i ch` is `WType.mk i ch` by definition and `toSigma`
  matches on the constructor. mathlib carries no `WType.toSigma_mk` to fall
  back on.

- [ ] **Step 5: Extend the docstring and commit**

Add to `## Main statements`:

```text
* `Geb.CobhamFold.toSigma_mk` — the term algebra's destructor at the
  `RankedAlphabet.Term.mk` presentation.
* `Geb.CobhamFold.semAt_mkOf_spell` — the constructor's expression at the
  children's spellings is the spelling of the term they build.
* `Geb.CobhamFold.semAt_mkOf_childOf` — the constructor at the children the
  destructor reads returns the word.
```

Add a third paragraph to the summary, after the one on `algPara`:

```text
Under the preorder encoding the structure map is the identity on
representations, `RankedAlphabet.spell_mk` stating that a symbol's block
followed by its children's spellings is the spelling of the term they build.
The content of the inverse laws is therefore that a valid word determines the
symbol and the children's spellings.
```

`## References` and `## Tags` need no further entry: `[Meertens1992]` was
added in Task 4 and `destructor` is in the tag list from Task 3.

```bash
jj commit -m 'feat(cobham-term): close the constructor and destructor round trip'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 10: The test module, and the end of `Boundary.lean`

**Files:**

- Create: `GebTests/Internal/Computability/CobhamFoldProto/Destruct.lean`
- Delete: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
- Modify: `GebTests/Internal/Computability/CobhamFoldProto.lean` (swap the
  import)

**Interfaces:**

- Consumes: `Geb.CobhamFold.childSem`, `Geb.CobhamFold.algCh`,
  `Geb.CobhamFold.Term.fold`; `RankedAlphabet.Binary.binRanked`,
  `RankedAlphabet.Binary.leaf`, `RankedAlphabet.Binary.node`.
- Produces, in namespace `GebTests.CobhamFold`: `destSample`,
  `valueBounded`, and the `#guard`s.

- [ ] **Step 1: Write the test module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto
public meta import Geb.Internal.Computability.CobhamFoldProto  -- shake: keep; #guard needs it

/-!
# The term algebra's destructor, on samples

`Geb.CobhamFold.childSem` at the two-symbol alphabet, checked by `#guard`
against a term whose two children differ, and the fold's value read against
the term's node count.

The samples exercise the semantic layer.
`Geb.CobhamFold.stepWord_childOf` identifies the expression with it
symbolically, so no sample forces the readout's `Cobham.casesOf` tree, whose
branch family is `2 ^ Geb.CobhamFold.readoutWidthV R` wide.

## Main definitions

* `GebTests.CobhamFold.destSample` — a term whose two children differ.
* `GebTests.CobhamFold.valueBounded` — the length bound read at that
  alphabet.

## Tags

Cobham, ranked tree, destructor, subterm, test
-/

@[expose] public section

namespace GebTests.CobhamFold

open Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- A sample term whose two children differ. -/
def destSample : binRanked.Term := node leaf (node leaf leaf)

#guard binRanked.spell destSample = [true, false, true, false, false]
#guard childSem binRanked 0 destSample = [false]
#guard childSem binRanked 1 destSample = [true, false, false]

/-- At `binRanked`, the fold's value stays within six times the term's node
count. The factor is this alphabet's; no general bound is proved here. -/
def valueBounded (t : binRanked.Term) : Bool :=
  (Term.fold binRanked (algCh binRanked) t).length ≤ 6 * t.size

#guard valueBounded leaf
#guard valueBounded (node leaf leaf)
#guard valueBounded destSample
#guard valueBounded (node (node leaf leaf) (node leaf leaf))

end GebTests.CobhamFold

end
```

- [ ] **Step 2: Delete `Boundary.lean` and swap the index import**

At this point `Boundary.lean` holds only `destSample`, `valueBounded` and the
`#guard`s: Tasks 2, 4, 5 and 8 moved everything else out. Confirm that before
deleting:

```bash
grep -n '^def \|^theorem \|^abbrev \|^#guard ' \
  GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean
```

Expected: `destSample`, `valueBounded` and the seven `#guard` lines, and
nothing else — Task 8 Step 8 already moved `childSem` to `Destruct.lean`. If
anything else remains, it belongs to a task that did not finish; do not
delete until it does.

```bash
rm GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean
```

Then in `GebTests/Internal/Computability/CobhamFoldProto.lean`:

```lean
import GebTests.Internal.Computability.CobhamFoldProto.Destruct
import GebTests.Internal.Computability.CobhamFoldProto.Fold
```

- [ ] **Step 3: Build and check the guards**

```bash
lake build GebTests
lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
```

Expected: all three exit zero. A `#guard` failure is a build error; the
`public meta import` is what makes the guards evaluate across the module
boundary, and `-- shake: keep` on it is the sanctioned suppression.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'test(cobham-term): check the child reader on differing children'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 11: Documentation and the amended obligations

**Files:**

- Modify: `docs/index.md` (the new `Destruct.lean` entry, and the existing
  `Fold.lean`, `Variable.lean` and `Bound.lean` entries)
- Modify: `TODO.md` (§ The fold over recognized terms, § Deferred items from
  the tree recognizers)

**Interfaces:**

- Consumes: every name Tasks 3 to 9 produced.
- Produces: no Lean.

- [ ] **Step 1: Add the `docs/index.md` entry**

Insert after the `Initial.lean` entry the constructor branch added:

```markdown
- `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean` — the inverse of
  the initial algebra's structure map, as expressions of Cobham's class, and
  the paramorphism at the same representation. `codeOf` and `dropCodeOf` read
  a word's leading block and what follows it through a constant unary prefix
  that makes the word a self-delimiting entry whose payload is that block, so
  no dispatch over the block is needed. `algPara` is the paramorphism as a
  fold, at a carrier pairing a subterm's spelling with the step's value, the
  value delimited so the two are separable; the delimiting does not nest,
  each level reading only the spelling half of a child's value, which is what
  a value linear in the subterm would need; `TODO.md` records that linearity
  as unproved at a symbolic alphabet. `dropEntry_algPara` and
  `takeEntry_algPara`
  are its two laws and `algPara_eq_para` identifies it with `WType.para` at
  the step that sees each child's spelling in place of the subtree, so the
  recursion scheme is [Meertens1992]'s rather than one introduced here.
  `growth_algPara` gives the per-symbol growth `2 * cphi + R.width + 1` for a
  step bounded by its children's values, resting on `SelfDelim.lean`'s
  weighted bound and so holding at arbitrary arguments. `algCh` is the
  instance whose step returns the children's spellings, each delimited, and
  it is the one that fails the growth condition, duplicating its children's
  payloads; `five_mul_length_dropEntrySem_algCh_le` is the property of its
  outputs that replaces it; `Fold.lean`'s `mem_stack_foldScanFinal` carries
  that property along the scan, and `Variable.lean`'s potential chain,
  generalised there to take a predicate the stack's values satisfy, runs the
  argument with the growth condition so restricted, giving
  `stackSize_algCh_le` at the constant
  `chGrowth`. `algChOf` computes `algCh` inside the class, reusing
  `Initial.lean`'s `flattenOf` through `compOf`; `smashFreeBool_algChOf` says
  that expression carries no `smash`, and `smashFreeBool_chFoldOf` and
  `smashFreeBool_childOf` carry that through the fold and the child reader,
  placing both in the subalgebra `Cobham.SmashFree` names. `childSem` and
  `childOf` read the `j`-th child's spelling, semantically and as an
  expression, `chFoldOf` carrying the fold the expression reads from and
  `stepWord_chFoldOf` its value; both readers are total, `childSem_of_le`
  and `stepWord_childOf_of_le` returning the empty word past the last child,
  and the expression's
  equations are stated in the "entries followed by an arbitrary remainder"
  form because the readout's presence marker is absorbed into the entry's
  unary prefix. `toSigma_mk` bridges mathlib's `WType.toSigma` to
  `RankedAlphabet.Term.mk`, `semAt_mkOf_spell` reads the constructor at the
  children's spellings as the spelling of the term they build, and
  `semAt_mkOf_childOf` closes the round trip:
  the constructor at the children the destructor reads returns the word,
  under `R.parse w = some (Term.mk R i ch)` with the symbol given rather than
  read. Depends on
  `Geb.Internal.Computability.CobhamFoldProto.Initial` and
  `Geb.Mathlib.Data.W.Basic`. `Classical.choice`-free.
```

`codeOf`, `dropCodeOf`, `growth_algPara`, `toSigma_mk` and
`smashFreeBool_childOf` are each defined by this branch and consumed by no
later declaration in it. All are spec deliverables or their corollaries —
`codeOf`, `dropCodeOf` and `toSigma_mk` named in D4 and D5,
`growth_algPara` the constant D6 leaves for a caller supplying its own step —
so the entry names them as the interface they are, not as dead code.

- [ ] **Step 2: Amend the `Fold.lean`, `Variable.lean` and `Bound.lean` entries**

Each of these entries enumerates its module's declarations, and this branch
adds to all three, so all three are amended in the branch that adds them — as
Task 2 Step 4 already does for `SelfDelim.lean`.

Append to the `Geb/Internal/Computability/CobhamFoldProto/Fold.lean` entry,
before its `Depends on` sentence, indented two spaces to match that entry's
continuation lines:

```text
`mem_stack_foldScanFinal` reads the stack as holding only values the algebra
produced, the completing pop being the only clause that pushes; it is what
lets a growth condition be assumed of the scan's own values rather than of
arbitrary arguments.
```

Append to the `Geb/Internal/Computability/CobhamFoldProto/Variable.lean`
entry, before its `Depends on` sentence:

```text
`potential_foldScanStep_le_of_invariant`,
`potential_foldScanFinal_le_of_invariant` and
`stackSize_le_of_growth_of_invariant` are those three at a growth condition
restricted to values satisfying a predicate the stack's entries carry, which
an algebra duplicating its children's payloads needs and the unrestricted
form does not give; each unrestricted form is re-derived from its
generalisation at the trivial predicate.
`stepWord_dropEntriesOf_stackWordV_append` and
`stepWord_entryOf_stackWordV_append` read the same layout followed by an
arbitrary remainder, which a readout prefixing a presence marker leaves past
the entries; they need `k ≤ st.length` where the totals do not, so both
forms stand.
```

Append to the `Geb/Internal/Computability/CobhamFoldProto/Bound.lean` entry,
before its `Depends on` sentence, indented two spaces to match its
continuation lines:

```text
`semAt_comp1Of` reads an arity-one expression's meaning at an `n`-ary
argument, `CobhamFoldProto/SelfDelim.lean`'s `stepWord_comp1Of` being its
arity-one instance.
```

- [ ] **Step 3: Amend § Deferred items from the tree recognizers**

The first bullet's middle clause reads:

```text
the paramorphism whose step receives a subterm's
spelling, which the head-locality of the state layout admits only at
quadratic cost;
```

The bullet opens with a three-item sentence and closes with sentences about
the fold at an infinite carrier and `smashFree_foldOutExprV`. Replace the
opening sentence only, leaving those closing sentences in place:

```text
- The Bellantoni-Cook port of the scan combinator, whose signature is over
  arities in normal and safe position and so is a branch rather than a
  transcription; and the depth-first unary degree sequence encoding, whose
  condition for adoption is unbounded arity.
```

Then add, after that bullet's closing sentences, indented two spaces so it
stays inside the list item — unindented it terminates the list and
`markdownlint` reports MD032:

```text
`Geb.CobhamFold.algPara` computes the paramorphism whose step receives a
subterm's spelling, carrying the spelling in the fold's carrier rather than
reading it from the state, so the head-locality the quadratic-cost estimate
rests on does not bind. What the carrier costs is a value linear in the
subterm, which is unproved at a symbolic alphabet:
`Geb.CobhamFold.stackSize_algCh_le` bounds the pending values' total by a
multiple of the input word's length, not a subterm's fold value by that
subterm. Nothing here measures reduction steps, so this replaces the
estimate's premise rather than its arithmetic.
```

- [ ] **Step 4: Amend § The fold over recognized terms**

Append a bullet:

```text
- No single expression destructs an unknown symbol.
  `Geb.CobhamFold.semAt_mkOf_childOf` is stated under
  `R.parse w = some (Term.mk R i ch)` with the symbol given rather than read,
  so no dispatch over the block is needed; `Geb.CobhamFold.childOf` and
  `Geb.CobhamFold.mkOf` are total and return an unspecified word off the
  recognized language. A guarded total form is available by composing
  `Cobham.isRankedOf` and is not built.
```

- [ ] **Step 5: Lint and commit**

```bash
markdownlint-cli2 'docs/index.md' 'TODO.md'
bash scripts/check-md-links.sh
doctoc --dryrun --update-only .
jj commit -m 'doc(cobham-term): index the destructor and amend its obligations'
jj bookmark set feat/cobham-term-dest -r @-
```

---

## Task 12: Verify the branch and remove the spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md`
- Delete: `docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md`

**Interfaces:**

- Consumes: the whole branch.
- Produces: a branch whose working tree carries no transient artifact.

- [ ] **Step 1: Run the authoritative gate**

`scripts/pre-push.sh` is the authoritative checklist under
CONTRIBUTING.md § Working and docs/rules/ci-and-workflow.md § Pre-push
checklist, and it is a superset of any command listed here.

```bash
bash scripts/pre-push.sh
```

Expected: exit zero. The script exits non-zero on the first failure and names
the step; read the script for what each step runs rather than relying on a
list in this plan, which would drift from it. To narrow a failure, re-run the
named step alone, then re-run the whole script.

- [ ] **Step 2: Run the mandated review skills**

CLAUDE.md § Phase-driven workflow binds
`superpowers:verification-before-completion` at the pre-commit phase, and
docs/rules/lean-coding.md § Lean 4 skill workflows names `review` for
pre-commit Lean review and `golf` for polishing a proof. Run them on this
branch's Lean diff before the next step.

Do not claim the branch passes without the output of Step 1 in hand. If any
step fails, fix the cause in the task that introduced it and re-run the whole
script.

- [ ] **Step 3: Remove the spec and the plan**

```bash
rm docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md
rm docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md
```

- [ ] **Step 4: Re-gate the state that will be committed**

```bash
markdownlint-cli2 '**/*.md'
bash scripts/check-md-links.sh
bash scripts/pre-push.sh
```

Expected: all three exit zero. The authoritative gate is re-run after the
removal, so the state that is committed is the state that was gated.

- [ ] **Step 5: Commit**

`scripts/pre-push.sh` runs `check-commit-msg.sh` over
`fork_point(main | @)..@`, which does not yet include the commit this step
creates, so check this one subject by hand first. It reads subjects from
stdin, one per line.

```bash
printf '%s\n' \
  'doc(cobham-term): remove the transient destructor spec and plan' \
  | bash scripts/check-commit-msg.sh
jj commit -m 'doc(cobham-term): remove the transient destructor spec and plan'
jj bookmark set feat/cobham-term-dest -r @-
```

The subject is 63 characters and conforms; the check is here so the last
commit is not the one nothing verified.

- [ ] **Step 6: Hand off**

Both branches are ready for the user's line-by-line review. Do not push: no
`jj git push` runs without that review, first-creation pushes included. State
plainly which gate commands were run and what they returned, and which of the
risks below were hit.

---

## Risks this plan carries

- Three `omega` calls close only because a step `omega` cannot take is
  supplied by hand, and each fails silently-looking if that step is dropped.
  `five_mul_length_flatten_dropEntrySem_le` (Task 6 Step 6) needs its `hd`
  `have`, `4 * R.width * (t.length + 1)` and `4 * R.width * t.length` being
  separate atoms. `growth_algPara` (Task 4 Step 3) and
  `growth_algCh_of_dropEntrySem_le` (Task 6 Step 6) each need
  `Function.comp_def` in their `simp only`, without which `List.map_ofFn`
  leaves `List.ofFn (f ∘ g)` against the goal's `List.ofFn fun d ↦ f (g d)`
  as two unrelated atoms; and the last additionally needs the monotonicity
  and commutation `have`s, `4 * R.width * R.arity i ≤ 4 * R.maxArity * R.width`
  being a product of two variables. Each is written in the form that
  elaborates, with the reason recorded beside it. These argument lists are
  sensitive in both directions and must not be copied between sites:
  `length_algCh` (Task 5 Step 2) takes `List.length_ofFn` alone, and adding
  `List.map_ofFn` or `Function.comp_def` there is an error, `unusedSimpArgs`
  being fatal under `weak.warningAsError` exactly as a missing argument is.
  Read each list off the elaborator rather than from a neighbouring proof.
- Two proofs do not close the way the surrounding pattern suggests:
  `mem_stack_foldScanFinal` (Task 6 Step 2) needs
  `simp [foldScanFinal, foldScanFrom]`, a bare `simp` making no progress; and
  `take_append_length_add_one` (Task 8 Step 1) is derived from
  `SelfDelim.lean`'s existing split rather than re-proved; if the derivation
  does not elaborate, the direct recursion is the fallback, and its base case
  needs a second `List.nil_append`, `rw`'s trailing `rfl` being
  reducible-only.
- Task 6 is the one piece whose mathematics, not only whose proof, is new.
  `hsize` for `algCh` has no precedent of its own shape; it is a proof
  argument of `foldOutOfV`, so `chFoldOf` and everything reading through it —
  Task 8 Steps 5 to 7 and Task 9 Step 3 — cannot be written until it is done.
  Task 8's other steps and Task 9 Steps 1 and 2 use nothing from it and can
  proceed in parallel. Restricting to `binRanked` does not avoid it. If it
  does not close, the fallback the spec records is
  Tasks 4, 5 and 9's semantic content alone — which `Boundary.lean` already
  exhibits — with `algChOf`, `childOf` and `semAt_mkOf_childOf` dropped and
  the expression layer recorded in `TODO.md` instead. Taking that fallback
  changes the branch's deliverable, so it is the user's call, not the
  implementer's: stop and report rather than reshaping the branch.
- The expressions may not evaluate in budget, which is why the test module's
  `#guard`s stay at the semantic layer and no `#guard` against an
  expression's output word is a deliverable.
- Every Lean core and mathlib name used above may move under a toolchain
  bump; all resolve today. `List.mem_of_mem_drop` and
  `List.eq_nil_of_length_eq_zero` is called out where it is used, and
  `List.mem_of_mem_drop` appears once, in Task 6 Step 1's Lean; the check
  applies to all of them — `List.take_left'`, `List.drop_left'`,
  `List.drop_eq_getElem_cons`, `List.mem_ofFn`, `List.getElem_ofFn`,
  `List.flatMap_def`, `List.drop_eq_nil_of_le`, `List.length_take`,
  `Nat.add_sub_cancel'` and `Nat.min_le_left` among them. Run the check
  (`lean_local_search`, then `lean_hover_info` on the found name) before
  substituting any of them. Do not reach for
  `List.take_add`: `SelfDelim.lean` records it as choice-dependent, which is
  why `take_append_length_add_one` is proved here.
