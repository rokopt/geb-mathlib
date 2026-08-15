# The ranked term algebra's constructor in the fold's language — plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Where `Boundary.lean` is first committed](#where-boundarylean-is-first-committed)
- [Task 1: Create the branch and commit the spec and this plan](#task-1-create-the-branch-and-commit-the-spec-and-this-plan)
- [Task 2: Commit the evidence module whole](#task-2-commit-the-evidence-module-whole)
- [Task 3: Move the structure map into `Initial.lean`](#task-3-move-the-structure-map-into-initiallean)
- [Task 4: The expression computing the structure map](#task-4-the-expression-computing-the-structure-map)
- [Task 5: The four obligations](#task-5-the-four-obligations)
- [Task 6: The identity theorem at the expression layer](#task-6-the-identity-theorem-at-the-expression-layer)
- [Task 7: Documentation and the amended obligation](#task-7-documentation-and-the-amended-obligation)
- [Task 8: Verify the branch and remove the spec and plan](#task-8-verify-the-branch-and-remove-the-spec-and-plan)
- [Risks this plan carries](#risks-this-plan-carries)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver the initial algebra's structure map at the carrier
`List Bool` — as a fold-algebra, as an expression of Cobham's class, and as
the fold whose value is its own argument — in
`Geb/Internal/Computability/CobhamFoldProto/Initial.lean`.

**Architecture:** `algMk R i f = R.code i ++ (List.ofFn f).flatten` is
`RankedAlphabet.spell`'s own `WType.elim` step named apart from it, so
`Term.fold R (algMk R) = R.spell` holds by `rfl`. Its expression `mkOf R i`
prepends the symbol's block to `flattenOf (R.arity i)`, a `Nat.rec` over the
arity concatenating the slots in index order. The three obligations
`foldOutExprV` takes and the fourth `smashFree_foldOutExprV` takes are
discharged at that expression, and the identity theorem is read off
`foldOutSemV_eq` composed with `foldOut_eq` and `parse_eq_some_iff`.

**Tech Stack:** Lean 4 (toolchain from `lean-toolchain`), mathlib, `lake`,
`jj` in colocated mode.

**Spec:**
[docs/superpowers/specs/2026-08-15-ranked-term-constructor-design.md](../specs/2026-08-15-ranked-term-constructor-design.md)

## Global Constraints

- Branch: `feat/cobham-term-mk`, stacked on `feat/cobham-fold-proto`
  (change `yxzxwwpm`), an unmerged topic branch. `main` has advanced past
  that branch's base, so `yxzxwwpm` is not an ancestor of `main`. Whether
  `feat/cobham-fold-proto` is first rebased onto `main` is that branch's
  decision, not this one's; if it is, re-read `scripts/pre-push.sh` before
  Task 8, since its contents differ between the two bases.
- All state-mutating version control goes through `jj`. Raw mutating `git`
  subcommands are blocked by `scripts/hooks/block-mutating-git.sh`. After
  every `jj commit` on the branch, run
  `jj bookmark set feat/cobham-term-mk -r @-`: jj bookmarks do not
  auto-advance.
- No `noncomputable`. No `Classical` beyond what the imported modules already
  carry; every declaration this branch adds is `Classical.choice`-free, which
  `GebMeta.detectNonstandardAxiom` enforces through `lake lint` and
  `lake lint -- GebTests`.
- No `sorry` and no `admit` in any committed state. Between edits within a
  task, use `_` to expose a hole; elaboration reports it as an error.
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
  `[Strahm2003]` and `[GambinoHyland2004]` are all already recorded there.
- No expression is evaluated. Acceptance is symbolic throughout: the
  readout's dispatch has `2 ^ readoutWidthV R` branches and an evaluation of
  it at a one-entry state was measured not to return, so no `#guard` against
  an expression's output word is a deliverable and this branch adds no test
  module.

## Where `Boundary.lean` is first committed

`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean` is in the
working copy uncommitted, holding the semantic content of both branches. It
is committed whole, once, by Task 2 of this branch, before anything is moved
out of it. The destructor branch takes the remainder and deletes the module;
nothing on either branch re-adds it. The spec's § Scope authorises carrying
it.

This is a deliberate deferral against CONTRIBUTING.md § Concern shape, which
says "One concern per branch" and, of code worth refactoring outside a
branch's scope, "create a separate branch for it rather than bundling it with
unrelated work". From Task 2 until the destructor branch's final relocating
task, the one that deletes the module, the committed tree carries `ParaStep`,
`algPara`, `algCh`, their laws, `childSem`,
`two_mul_length_takeEntrySem_add_length_dropEntrySem_le`,
`destSample` and `valueBounded` — the destructor's concern, on the
constructor's branch. Every one of them is relocated by the branch that owns
them, and none is authored here.

Two arguments for the order do not survive: that what is committed first is
what has been verified (the reduced module builds and is verified too, at
Task 3 Step 5), and that each extraction reads as a relocation against a
committed baseline (a reviewer of this branch sees an add-then-move round
trip inside one branch, which is more diff, not less). What is left is that
the evidence module enters history as the artifact it was, so a later reader
sees exactly what the two branches distilled, and that this ordering was
chosen deliberately rather than drifted into.

The alternative, which is the shorter diff: drop Task 2 and Task 3 Step 4,
author `Initial.lean` in Task 3, commit only the `Geb` module and its index
line, and leave `Boundary.lean` uncommitted for the destructor branch to
commit already reduced. This branch would then touch no `GebTests` file at
all. It contradicts the spec's § Scope, which states that the branch carries
`Boundary.lean` and moves four declarations out of it, so adopting it means
amending the spec first. Changing to it is a decision about the branch's
shape, not an implementation detail.

---

## Task 1: Create the branch and commit the spec and this plan

**Files:**

- Edit and commit:
  `docs/superpowers/specs/2026-08-15-ranked-term-constructor-design.md`
  (Step 3 de-links its reference to the destructor spec)
- Commit: `docs/superpowers/plans/2026-08-15-ranked-term-constructor-plan.md`

**Interfaces:**

- Consumes: nothing.
- Produces: the branch `feat/cobham-term-mk` with its spec and plan as its
  first commit, on top of `feat/cobham-fold-proto`.

- [ ] **Step 1: Confirm the starting point**

```bash
jj log -r 'ancestors(@, 3)' --no-graph \
  -T 'change_id.short() ++ " " ++ bookmarks ++ " " ++ description.first_line() ++ "\n"'
jj st
```

Expected: `@` is a working copy with no description whose parent is
`yxzxwwpm` carrying the bookmark `feat/cobham-fold-proto`; `jj st` lists six
entries — the constructor and destructor specs, the constructor and
destructor plans, `Boundary.lean` added, and the test index modified.

- [ ] **Step 2: Regenerate the TOC of this plan and lint it**

The plan has more than one `##` heading, so it carries a doctoc TOC. The
`<!-- START doctoc -->` / `<!-- END doctoc -->` markers are already in the
file; `doctoc` fills them in place.

```bash
doctoc --update-only docs/superpowers/plans/2026-08-15-ranked-term-constructor-plan.md
markdownlint-cli2 'docs/superpowers/plans/*.md' 'docs/superpowers/specs/*.md'
bash scripts/check-md-links.sh
```

Expected: all three exit zero. `doctoc` reports `Everything is OK` and
rewrites nothing — the plan's TOC is already current — so a rewrite here
means the plan's headings have drifted.

- [ ] **Step 3: De-link the spec's reference to the destructor spec**

The constructor spec's § Scope carries a Markdown link whose target is the
destructor spec's filename, and Step 4 parks that file out of the working
copy. `scripts/check-md-links.sh` resolves targets against the linking file's
directory and fails on a missing one, so from Step 4 until Task 8 the link
checker would fail on every run — Task 7 Step 4 and Task 8 Step 1 included.

Replace the whole sentence, so that no link remains and the prose still
reads. It currently says "The destructor, the inverse laws and the
paramorphism are a separate concern and a separate branch, specified in
[link], which depends on this one." Make it:

```text
The destructor, the inverse laws and the paramorphism are a separate concern
and a separate branch, which depends on this one and delivers
`Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`.
```

The destructor plan's Task 1 makes the mirror-image substitution in its own
spec, for the same reason.

```bash
bash scripts/check-md-links.sh
```

Expected: exit zero, with both specs still in the working copy.

- [ ] **Step 4: Commit this branch's two files by path**

`jj commit PATHS` commits only the matching changes and leaves the rest in
the new working copy. It is safe here, and only here, because `@` carries no
description: telling it to commit paths while the working copy is an
already-described commit repurposes that commit's description and splits its
content.

```bash
jj commit \
  docs/superpowers/specs/2026-08-15-ranked-term-constructor-design.md \
  docs/superpowers/plans/2026-08-15-ranked-term-constructor-plan.md \
  -m 'doc(cobham-term): add the ranked-term constructor spec and plan'
jj bookmark set feat/cobham-term-mk -r @-
jj st
```

Expected: the new commit carries the bookmark `feat/cobham-term-mk` and its
parent is `feat/cobham-fold-proto`; `jj st` lists the destructor spec, the
destructor plan, `Boundary.lean` and the modified test index.

- [ ] **Step 5: Park the destructor branch's two files**

They belong to `feat/cobham-term-dest`. Park them outside the working copy so
Tasks 3 to 8 can use a plain `jj commit`.

`.superpowers/` is in `.gitignore` and in `.markdownlint-cli2.jsonc`'s
`ignores` list, so a directory under it is neither committed nor
markdownlinted, and it is named repo-relative rather than by a path on one
machine. `doctoc --dryrun --update-only .` does descend into it, so the
parked copies must carry current TOCs — they do, Task 1 Step 2 having just
regenerated this plan's, and the destructor plan carrying its own.

```bash
mkdir -p .superpowers/cobham-term-handoff
cp docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md \
  docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md \
  .superpowers/cobham-term-handoff/
jj restore docs/superpowers/specs/2026-08-15-ranked-term-destructor-design.md \
  docs/superpowers/plans/2026-08-15-ranked-term-destructor-plan.md
jj st
```

Expected: `jj st` lists only `Boundary.lean` and the modified test index,
which are Task 2's. If the parked copies are ever lost, `jj op log` names the
operation this `jj restore` performed and `jj op restore <id>` rolls back to
the state before it, so the two files are recoverable from the operation log
as well as from `.superpowers/`.

---

## Task 2: Commit the evidence module whole

**Files:**

- Create: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (already in the working copy, unmodified since the start of this branch)
- Modify: `GebTests/Internal/Computability/CobhamFoldProto.lean` (one import
  line, already in the working copy)

**Interfaces:**

- Consumes: `Geb.Internal.Computability.CobhamFoldProto` (the index),
  `Geb.Mathlib.Data.W.Basic` (`WType.para`, `WType.para_mk`).
- Produces, in namespace `GebTests.CobhamFold`: `algMk`, `fold_algMk`,
  `length_algMk`, `foldOut_algMk`,
  `two_mul_length_takeEntrySem_add_length_dropEntrySem_le`, `ParaStep`,
  `algPara`, `dropEntry_algPara`, `takeEntry_algPara`, `algPara_eq_para`,
  `algCh`, `dropEntry_algCh`, `takeEntry_algCh`, `childSem`, `destSample`,
  `valueBounded`. Task 3 moves the first four into `Initial.lean`; the
  destructor branch takes the rest.

- [ ] **Step 1: Confirm the module and its index line**

Both are already in the working copy, left there by Task 1.

```bash
jj st
```

Expected: exactly two entries, `Boundary.lean` added and
`GebTests/Internal/Computability/CobhamFoldProto.lean` modified. The index
edit adds the import in alphabetical order before the existing one:

```lean
import GebTests.Internal.Computability.CobhamFoldProto.Boundary
import GebTests.Internal.Computability.CobhamFoldProto.Fold
```

- [ ] **Step 2: Build and check the test library**

```bash
lake build GebTests
```

Expected: no errors and no warnings. The module's `#guard`s — the sample's
spelling, `childSem` at 0 and at 1, and `valueBounded` at four terms — are
evaluated by this build; a `#guard` failure is a build error, not a
diagnostic.

- [ ] **Step 3: Run the axiom and import linters**

```bash
lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
```

Expected: both exit zero. `Boundary.lean`'s third import line carries
`-- shake: keep; #guard needs it`; if `lake shake` still reports it, do not
delete the import — the `public meta import` is what makes the `#guard`s
evaluate across the module boundary.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'test(cobham-term): record the term algebra'\''s semantic operations'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 3: Move the structure map into `Initial.lean`

**Files:**

- Create: `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`
- Modify: `Geb/Internal/Computability/CobhamFoldProto.lean` (one import line)
- Modify: `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`
  (remove the four moved declarations and their docstring lines)

**Interfaces:**

- Consumes: `Geb.CobhamFold.Term.fold`, `Geb.CobhamFold.foldOut`,
  `Geb.CobhamFold.foldOut_eq` (`Fold.lean`); `RankedAlphabet.code`,
  `RankedAlphabet.length_code`, `RankedAlphabet.spell`,
  `RankedAlphabet.parse`, `RankedAlphabet.parse_eq_some_iff`.
- Produces, in namespace `Geb.CobhamFold`:

```text
algMk (R : RankedAlphabet) (i : Fin R.card) (f : Fin (R.arity i) → List Bool) : List Bool
fold_algMk (R : RankedAlphabet) : Term.fold R (algMk R) = R.spell
length_algMk (R) (i) (f) : (algMk R i f).length = (List.ofFn fun d ↦ (f d).length).sum + R.width
foldOut_algMk (R) (w : List Bool) : foldOut R (algMk R) w = (R.parse w).map (fun _ ↦ w)
```

- [ ] **Step 1: Create the module with the structure map**

Write `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.SmashFree

/-!
# The term algebra's constructor in the fold's language

The initial algebra's structure map at the carrier `List Bool`, whose
elements are read as spellings.

`Term.fold` at `algMk` is `RankedAlphabet.spell` itself, so `algMk` is the
step `spell`'s own `WType.elim` runs, named apart from it, and the preorder
encoding is the unique morphism from the term algebra into it by the
initiality `Term.fold_unique` carries [GambinoHyland2004]. The carrier
`List Bool` is not itself initial — the spellings are a proper subalgebra of
it — so what the equation says is that `algMk` is the initial algebra's
structure map transported along the encoding.

## Main definitions

* `Geb.CobhamFold.algMk` — the initial algebra's structure map.

## Main statements

* `Geb.CobhamFold.fold_algMk` — the fold at that map is the spelling.
* `Geb.CobhamFold.length_algMk` — it lengthens by the alphabet's width.
* `Geb.CobhamFold.foldOut_algMk` — the fold at that map is the identity on
  the recognized language.

## References

* [Cobham1965]
* [GambinoHyland2004]

## Tags

Cobham, ranked tree, initial algebra, term algebra, preorder encoding
-/

@[expose] public section

namespace Geb.CobhamFold

/-- The initial algebra's structure map, at the carrier `List Bool`: a
symbol's block followed by its children's spellings. -/
def algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) : List Bool :=
  R.code i ++ (List.ofFn f).flatten

/-- The fold at that map is the preorder encoding, so `RankedAlphabet.spell`
is the unique morphism from the term algebra into it, by the initiality
`Geb.CobhamFold.Term.fold_unique` carries [GambinoHyland2004]. -/
theorem fold_algMk (R : RankedAlphabet) : Term.fold R (algMk R) = R.spell := rfl

/-- It lengthens its arguments' total by exactly the alphabet's width. -/
theorem length_algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algMk R i f).length = (List.ofFn fun d ↦ (f d).length).sum + R.width := by
  rw [algMk, List.length_append, R.length_code, List.length_flatten,
    List.map_ofFn]
  exact Nat.add_comm _ _

/-- The fold at that map is the identity on the recognized language. -/
theorem foldOut_algMk (R : RankedAlphabet) (w : List Bool) :
    foldOut R (algMk R) w = (R.parse w).map (fun _ ↦ w) := by
  rw [foldOut_eq]
  cases h : R.parse w with
  | none => rfl
  | some t => exact congrArg some (R.parse_eq_some_iff.mp h)

end Geb.CobhamFold

end
```

- [ ] **Step 2: Add the index line**

In `Geb/Internal/Computability/CobhamFoldProto.lean`, add the import last,
so the list reads in dependency order:

```lean
public import Geb.Internal.Computability.CobhamFoldProto.SmashFree
public import Geb.Internal.Computability.CobhamFoldProto.Degenerate
public import Geb.Internal.Computability.CobhamFoldProto.Initial
```

`Initial.lean` imports `SmashFree.lean`, so it goes after it in the index.

- [ ] **Step 3: Build the library**

```bash
lake build
```

Expected: no errors and no warnings. The import is broader than this task
needs — `SmashFree.lean`'s own contents are first used at Task 5, Task 4
reaching only `Fold.lean` and `Bound.lean` through the same chain — so leave
it
rather than narrowing and re-widening; `lake shake` runs at Task 2 Step 3 and
again at Task 8, by
which time Task 5's lemmas make it exact.

- [ ] **Step 4: Remove the moved declarations from `Boundary.lean`**

Delete from `GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`:

- the `algMk` `def` and its docstring;
- the `fold_algMk`, `length_algMk` and `foldOut_algMk` theorems and their
  docstrings;
- the `## Main definitions` bullet for `GebTests.CobhamFold.algMk`;
- the `## Main statements` bullets for `GebTests.CobhamFold.fold_algMk`,
  `GebTests.CobhamFold.length_algMk` and `GebTests.CobhamFold.foldOut_algMk`;
- `* [GambinoHyland2004]` from `## References` — the remaining half cites
  only `[Meertens1992]`;
- `initial algebra` from `## Tags`, which after the move reads
  `Cobham, ranked tree, subterm, paramorphism, self-delimiting`;
- the module docstring's second paragraph, which is about `algMk` alone:

```text
`algMk` is that structure map at the carrier `List Bool`: `Term.fold` at it is
`RankedAlphabet.spell` itself, so the preorder encoding is the unique morphism
from the term algebra into `algMk` rather than a construction beside it.
```

and replace the docstring's title and opening summary, which now describe
one half:

```text
# The term algebra's destructor, at the semantic layer

The algebra from which a subterm's spelling is recovered, and the
paramorphism it instantiates.
```

- [ ] **Step 5: Rebuild both libraries**

```bash
lake build
lake build GebTests
```

Expected: no errors and no warnings. Nothing surviving in `Boundary.lean`
names any of the four moved declarations — `algPara` spells `R.code i ++ …`
itself rather than calling `algMk` — so the removal leaves no dangling
reference and the module's `open Geb.CobhamFold` raises no ambiguity.

- [ ] **Step 6: Commit**

```bash
jj commit -m 'feat(cobham-term): add the initial algebra'\''s structure map'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 4: The expression computing the structure map

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Bound.lean` (add
  `semAt_compOf` after `semAt_concatCompOf`)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/SelfDelim.lean`
  (re-prove `stepWord_compOf` through it)
- Modify: `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`

**Interfaces:**

- Consumes: `Cobham.COf`, `Cobham.semAt`, `Cobham.zeroAtOf`,
  `Cobham.prependOf`, `Geb.CobhamFold.projOf`, `Geb.CobhamFold.compOf`,
  `Geb.CobhamFold.concatCompOf`, `Geb.CobhamFold.semAt_prependOf`,
  `Geb.CobhamFold.semAt_projOf`, `Geb.CobhamFold.semAt_concatCompOf`.
- Produces, in namespace `Geb.CobhamFold`, `semAt_compOf` into `Bound.lean`
  and the rest into `Initial.lean`:

```text
semAt_compOf {n m : ℕ} (head : COf m) (args : Fin m → COf n) (x : Fin n → List Bool) : semAt n (compOf head args).1.1 (compOf head args).2 x = semAt m head.1.1 head.2 fun i ↦ semAt n (args i).1.1 (args i).2 x
flattenOf : (n : ℕ) → COf n
flattenOf_succ (n : ℕ) : flattenOf (n + 1) = concatCompOf (n + 1) (compOf (flattenOf n) fun i ↦ projOf (n + 1) i.succ) (projOf (n + 1) 0)
semAt_flattenOf : ∀ (n : ℕ) (x : Fin n → List Bool), semAt n (flattenOf n).1.1 (flattenOf n).2 x = (List.ofFn x).flatten
mkOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i)
semAt_mkOf (R : RankedAlphabet) (i : Fin R.card) (f : Fin (R.arity i) → List Bool) : semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 f = algMk R i f
```

`semAt_mkOf R` has exactly the type `foldOutExprV`'s `halg` argument takes.

- [ ] **Step 1: Add the composition lemma to `Bound.lean`**

Its family — `semAt_prependOf`, `semAt_constAtOf`, `semAt_projOf`,
`semAt_concatCompOf` — lives in `Bound.lean` beside `compOf` itself, so it
goes there, after `semAt_concatCompOf` (`Bound.lean:200`).
`SelfDelim.lean`'s `stepWord_compOf` states the same fact at arity one, and
Step 2 re-proves it through this one rather than leaving two `rfl` proofs of
one fact.

```lean
/-- A composition's meaning at every arity. `Geb.CobhamFold.stepWord_compOf`
is this at arity one. -/
theorem semAt_compOf {n m : ℕ} (head : COf m) (args : Fin m → COf n)
    (x : Fin n → List Bool) :
    semAt n (compOf head args).1.1 (compOf head args).2 x =
      semAt m head.1.1 head.2 fun i ↦ semAt n (args i).1.1 (args i).2 x := rfl
```

- [ ] **Step 2: Re-prove `stepWord_compOf` through it**

In `SelfDelim.lean`, replace the body of `stepWord_compOf`
(`SelfDelim.lean:412`) — currently `rfl` — with the arity-one instance. The
statement is unchanged, so no consumer moves.

```lean
/-- A composition's value at an arity-one step. -/
theorem stepWord_compOf {m : ℕ} (head : COf m) (args : Fin m → COf 1)
    (u : List Bool) :
    stepWord (compOf head args) u =
      semAt m head.1.1 head.2 fun i ↦ stepWord (args i) u :=
  semAt_compOf head args ![u]
```

`stepWord e r` is `semAt 1 e.1.1 e.2 ![r]` by definition, so the instance
typechecks. Leaving the original `rfl` is not an option: the spec's § Scope
rules out the two lemmas stating the same fact twice.

- [ ] **Step 3: Build to confirm both are definitional**

```bash
lake build
```

Expected: no errors. `rfl` closes `semAt_compOf`: `compOf`'s `semAt` is the
head's meaning at the arguments' meanings by construction. `Bound.lean` and
`SelfDelim.lean` are both in `Initial.lean`'s import closure, so the whole
prototype rebuilds here.

- [ ] **Step 4: Add the slot concatenation and its unfolding lemma**

`flattenOf` is the first declaration to name `Cobham`'s own constants, so add
`open Cobham` under `namespace Geb.CobhamFold` in the same edit; Task 3's
declarations reach everything they use by dot notation on `R` or from
`Geb.CobhamFold` itself.

`flattenOf` is a bare `Nat.rec`, for which Lean generates no equation lemma,
so the unfolding at a successor is stated explicitly, as
`RankedAlphabet.parseChildren_succ` is for the same reason. The recursion
shifts the slots at each step: the arity-`n` tail is composed against
`fun i ↦ projOf (n + 1) i.succ`, so no `def` calls itself.

```lean
/-- The concatenation of an arity's slots, in index order. Built by `Nat.rec`
on the arity, the arity-`n` tail composed against the shifted projections, so
no `def` calls itself. -/
def flattenOf : (n : ℕ) → COf n :=
  Nat.rec (zeroAtOf 0) fun n ih ↦
    concatCompOf (n + 1) (compOf ih fun i ↦ projOf (n + 1) i.succ)
      (projOf (n + 1) 0)

/-- One more slot concatenates onto the shifted tail, its own value first.
`flattenOf` is a bare `Nat.rec`, for which Lean generates no equation
lemma. -/
theorem flattenOf_succ (n : ℕ) :
    flattenOf (n + 1) =
      concatCompOf (n + 1) (compOf (flattenOf n) fun i ↦ projOf (n + 1) i.succ)
        (projOf (n + 1) 0) := rfl
```

- [ ] **Step 5: Prove that it computes the slots' concatenation**

`concatCompOf n a b` puts `b`'s value first, so the nesting is in the first
argument and the head slot is the second.

```lean
/-- It computes the concatenation of its slots. The single unfolding step is
definitional but the closed form is not, `List.ofFn_succ` itself not being
`rfl`. -/
theorem semAt_flattenOf : ∀ (n : ℕ) (x : Fin n → List Bool),
    semAt n (flattenOf n).1.1 (flattenOf n).2 x = (List.ofFn x).flatten :=
  Nat.rec (fun x ↦ by rw [List.ofFn_zero, List.flatten_nil]; rfl)
    fun n ih x ↦ by
      rw [flattenOf_succ, semAt_concatCompOf, semAt_projOf, semAt_compOf]
      simp only [semAt_projOf]
      rw [ih fun i ↦ x i.succ, List.ofFn_succ, List.flatten_cons]
```

The `simp only [semAt_projOf]` is not optional. Without it the
`semAt_compOf` rewrite leaves the argument family as
`fun i ↦ semAt (n + 1) (projOf (n + 1) i.succ).1.1 _ x`, and the `ih` rewrite
fails with "Tactic `rewrite` failed: Did not find an occurrence of the
pattern". Beneath that headline the elaborator adds a note that the target is
not type-correct at `implicit` transparency, and a `Full error` reading "The
argument `flattenOf n` has type `COf n` but is expected to have type
`{ e // e.arity = n }`" — that mismatch is the cause, the pattern-not-found
line the symptom.

- [ ] **Step 6: Build**

```bash
lake build
```

Expected: no errors.

- [ ] **Step 7: Add the structure map's expression and its meaning**

```lean
/-- The initial algebra's structure map as an expression of Cobham's class:
the symbol's block prepended to the concatenation of the slots. -/
def mkOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i) :=
  prependOf (R.code i) (flattenOf (R.arity i))

/-- The expression computes the structure map. -/
theorem semAt_mkOf (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 f = algMk R i f := by
  rw [mkOf, semAt_prependOf, semAt_flattenOf, algMk]
```

- [ ] **Step 8: Extend the module docstring**

Add to `## Main definitions`:

```text
* `Geb.CobhamFold.flattenOf` — the concatenation of an arity's slots.
* `Geb.CobhamFold.mkOf` — the structure map as an expression of the class.
```

Add to `## Main statements`:

```text
* `Geb.CobhamFold.flattenOf_succ` — the slot concatenation at a successor,
  which `Nat.rec` generates no equation lemma for.
* `Geb.CobhamFold.semAt_flattenOf`, `Geb.CobhamFold.semAt_mkOf` — what those
  two expressions compute.
```

Add to the summary paragraph, after the sentence ending "…so what the
equation says is that `algMk` is the initial algebra's structure map
transported along the encoding.":

```text
`mkOf` computes that map inside the class: the symbol's block prepended to
`flattenOf`, a `Nat.rec` on the arity whose step composes the arity-`n` tail
against the shifted projections, so no `def` calls itself.
```

Append `expression` to `## Tags`, which then reads, still on one line:

```text
Cobham, ranked tree, initial algebra, term algebra, preorder encoding, expression
```

- [ ] **Step 9: Build and commit**

```bash
lake build
jj commit -m 'feat(cobham-term): compute the structure map inside the class'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 5: The four obligations

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`

**Interfaces:**

- Consumes: `Geb.CobhamFold.foldScanFinal` (`Fold.lean`);
  `Geb.CobhamFold.stackSize`, `Geb.CobhamFold.stackSize_le_of_growth`
  (`Variable.lean`); `Cobham.smashFreeBool`,
  `Geb.CobhamFold.smashFreeBool_zeroAtOf`,
  `Geb.CobhamFold.smashFreeBool_concatCompOf`,
  `Geb.CobhamFold.smashFreeBool_compOf`, `Geb.CobhamFold.smashFreeBool_projOf`,
  `Geb.CobhamFold.smashFreeBool_prependOf` (`SmashFree.lean`).
- Produces, in namespace `Geb.CobhamFold`:

```text
growth_algMk (R : RankedAlphabet) (i : Fin R.card) (f : Fin (R.arity i) → List Bool) : (algMk R i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + R.width
stackSize_algMk_le (R : RankedAlphabet) (w : List Bool) : stackSize (foldScanFinal R (algMk R) w).stack ≤ R.width * w.length
smashFreeBool_flattenOf : ∀ n : ℕ, smashFreeBool (flattenOf n).1.1.1 = true
smashFreeBool_mkOf (R : RankedAlphabet) (i : Fin R.card) : smashFreeBool (mkOf R i).1.1.1 = true
```

`growth_algMk` states a `≤` without an `_le` suffix. The naming guide has no
rule mandating one; it follows from the describe-the-conclusion convention,
and the sibling `stackSize_algMk_le` in this module does carry it. The bare
form is a deliberate choice, taken for consistency with
`GebTests`' `growth_leafCountAlg`, which names the same obligation at the
leaf-counting algebra, and with `growth_algPara` on the destructor branch;
`length_algMk_le` would be the upstream-conforming name.
`stackSize_algMk_le` does carry the suffix, following `length_foldSemV_le`
and `stackSize_le_of_growth` in `Variable.lean`.

Together with `semAt_mkOf` from Task 4 these are the four obligations: the
`semAt` lemma and the linearity hypothesis and the multiplier constraint that
`foldOutExprV` takes, and the smash-freeness that `smashFree_foldOutExprV`
takes. The multiplier constraint is `2 * R.width + 2 ≤ mult`, which is
`foldOutExprV`'s `hmult` at `c = R.width`; it is a hypothesis of the
statements in Task 6 rather than a theorem, the multiplier being the caller's
choice.

- [ ] **Step 1: Add the growth condition and the linearity hypothesis**

`length_algMk` is an equality, so the growth condition at the constant
`R.width` is exactly it, and `stackSize_le_of_growth` bridges it to the
hypothesis `foldOutExprV` consumes.

```lean
/-- The growth condition at the constant `R.width`, which `length_algMk`
gives with equality. -/
theorem growth_algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algMk R i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + R.width :=
  Nat.le_of_eq (length_algMk R i f)

/-- The pending values stay linear in the input, at the same constant. This
is the hypothesis `Geb.CobhamFold.foldOutExprV` takes, discharged by
`Geb.CobhamFold.stackSize_le_of_growth` from the per-symbol condition
alone. -/
theorem stackSize_algMk_le (R : RankedAlphabet) (w : List Bool) :
    stackSize (foldScanFinal R (algMk R) w).stack ≤ R.width * w.length :=
  stackSize_le_of_growth R (algMk R) R.width (growth_algMk R) w
```

- [ ] **Step 2: Build**

```bash
lake build
```

Expected: no errors. `stackSize_le_of_growth`'s argument order is `R`, the
algebra, the constant, the growth proof, then the word, and `growth_algMk R`
supplies the fourth at the type `∀ i f, (algMk R i f).length ≤ _ + R.width`.

- [ ] **Step 3: Add smash-freeness**

```lean
/-- The slot concatenation carries no `smash`: the empty bitstring at arity
zero, and a `concat` composition of projections at every successor. -/
theorem smashFreeBool_flattenOf : ∀ n : ℕ,
    smashFreeBool (flattenOf n).1.1.1 = true :=
  Nat.rec (smashFreeBool_zeroAtOf 0) fun n ih ↦
    smashFreeBool_concatCompOf (n + 1) _ _
      (smashFreeBool_compOf _ _ ih fun i ↦ smashFreeBool_projOf (n + 1) i.succ)
      (smashFreeBool_projOf (n + 1) 0)

/-- The structure map's expression carries no `smash`, which is
`Geb.CobhamFold.smashFree_foldOutExprV`'s hypothesis at this algebra. -/
theorem smashFreeBool_mkOf (R : RankedAlphabet) (i : Fin R.card) :
    smashFreeBool (mkOf R i).1.1.1 = true :=
  smashFreeBool_prependOf _ _ (smashFreeBool_flattenOf (R.arity i))
```

- [ ] **Step 4: Build and repair**

```bash
lake build
```

Expected: no errors. `smashFreeBool_flattenOf`'s successor case is stated
against `flattenOf (n + 1)`, which `Nat.rec` presents definitionally, so the
term needs no `flattenOf_succ` rewrite.

- [ ] **Step 5: Extend the module docstring**

Add to `## Main statements`:

```text
* `Geb.CobhamFold.growth_algMk`, `Geb.CobhamFold.stackSize_algMk_le` — the
  per-symbol growth condition at the constant `R.width`, and the linearity
  hypothesis it discharges.
* `Geb.CobhamFold.smashFreeBool_flattenOf`,
  `Geb.CobhamFold.smashFreeBool_mkOf` — those expressions carry no `smash`.
```

Append `smash-free` to `## Tags`, which then reads, still on one line:

```text
Cobham, ranked tree, initial algebra, term algebra, preorder encoding, expression, smash-free
```

- [ ] **Step 6: Commit**

```bash
jj commit -m 'feat(cobham-term): discharge the fold'\''s obligations at the structure map'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 6: The identity theorem at the expression layer

**Files:**

- Modify: `Geb/Internal/Computability/CobhamFoldProto/Initial.lean`

**Interfaces:**

- Consumes: `Geb.CobhamFold.foldOutSemV`, `Geb.CobhamFold.foldOutSemV_eq`,
  `Geb.CobhamFold.foldOutExprV`, `Geb.CobhamFold.outWordV` (`Variable.lean`);
  `Geb.CobhamFold.smashFree_foldOutExprV` (`SmashFree.lean`);
  `Cobham.SmashFree`.
- Produces, in namespace `Geb.CobhamFold`:

```text
foldOutSemV_algMk (R : RankedAlphabet) (mult : ℕ) (hmult : 2 * R.width + 2 ≤ mult) (w : List Bool) : foldOutSemV R (mkOf R) (algMk R) (semAt_mkOf R) mult R.width (stackSize_algMk_le R) hmult ![w] = outWordV ((R.parse w).map fun _ ↦ w)
smashFree_foldOutExprV_mkOf (R : RankedAlphabet) (mult : ℕ) (hmult : 2 * R.width + 2 ≤ mult) : SmashFree (foldOutExprV R (mkOf R) (algMk R) (semAt_mkOf R) mult R.width (stackSize_algMk_le R) hmult)
```

- [ ] **Step 1: Add the expression-layer identity theorem**

The output word is characterised for every input word, symbolically: the
proof composes `foldOutSemV_eq`, which identifies the expression's value with
`outWordV` of `foldOut`, with the semantic equation `foldOut_algMk`. Nothing
is evaluated.

```lean
/-- The expression at the structure map returns its own input, spelled by
`Geb.CobhamFold.outWordV`, on the recognized language and the absence marker
off it. The output word is characterised for every input word rather than
computed from one, the readout's dispatch having `2 ^ readoutWidthV R`
branches. -/
theorem foldOutSemV_algMk (R : RankedAlphabet) (mult : ℕ)
    (hmult : 2 * R.width + 2 ≤ mult) (w : List Bool) :
    foldOutSemV R (mkOf R) (algMk R) (semAt_mkOf R) mult R.width
        (stackSize_algMk_le R) hmult ![w] =
      outWordV ((R.parse w).map fun _ ↦ w) := by
  rw [foldOutSemV_eq, foldOut_algMk]
```

- [ ] **Step 2: Build**

```bash
lake build
```

Expected: no errors. `foldOutSemV_eq`'s arguments are `R`, `algOf`, `alg`,
`halg`, `mult`, `c`, `hsize`, `hmult`, `w` in that order; the `rw` supplies
them by unification from the goal's left-hand side.

- [ ] **Step 3: Add the subalgebra membership**

The spec's D2 names this outright — its fourth bullet asks for
`smashFreeBool_mkOf` "together with the membership it gives:
`smashFree_foldOutExprV` at `mkOf` and `algMk`". It is one term, and it
follows the pattern `GebTests`' `smashFree_leafCountExpr` sets at the
leaf-counting algebra.

```lean
/-- That expression lies in the subalgebra `Cobham.SmashFree` names, so with
[Strahm2003] Theorem 1(2)'s left-to-right inclusion it is computable
simultaneously in polynomial time and linear space. -/
theorem smashFree_foldOutExprV_mkOf (R : RankedAlphabet) (mult : ℕ)
    (hmult : 2 * R.width + 2 ≤ mult) :
    SmashFree (foldOutExprV R (mkOf R) (algMk R) (semAt_mkOf R) mult R.width
      (stackSize_algMk_le R) hmult) :=
  smashFree_foldOutExprV R (mkOf R) (smashFreeBool_mkOf R) (algMk R)
    (semAt_mkOf R) mult R.width (stackSize_algMk_le R) hmult
```

- [ ] **Step 4: Extend the module docstring**

Add to `## Main statements`:

```text
* `Geb.CobhamFold.foldOutSemV_algMk` — the expression at that algebra returns
  its own input on the recognized language, characterised for every input
  word; `## Implementation notes` records why it is characterised rather than
  computed.
* `Geb.CobhamFold.smashFree_foldOutExprV_mkOf` — that expression lies in the
  subalgebra `Cobham.SmashFree` names.
```

Add an `## Implementation notes` section, placed after `## Main statements`
and before `## References`:

```text
## Implementation notes

Nothing here is evaluated. `readoutWidthV R` is six at
`RankedAlphabet.Binary.binRanked`, so the readout dispatches on `2 ^ 6`
branches. `foldOutSemV_algMk` characterises the output word for every input
word instead, which needs no branch of that tree.

`algMk` and the step `RankedAlphabet.spell`'s own `WType.elim` runs agree by
`rfl` rather than sharing one definition: factoring that step out of `spell`
would touch `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`.
```

Add `* [Strahm2003]` to `## References`: `smashFree_foldOutExprV_mkOf`'s
docstring cites it, and `docs/rules/lean-coding.md` § Documentation has
`## References` list the keys a module cites. Listing a key no declaration
cites is not thereby forbidden — `SelfDelim.lean` and `Degenerate.lean` both
list `[Cobham1965]` for the class they work in — but a cited key must appear.

Append `catamorphism` to `## Tags`. That takes the line past 100 characters,
so wrap it here — the only wrap the sequence needs:

```text
Cobham, ranked tree, initial algebra, term algebra, preorder encoding,
expression, smash-free, catamorphism
```

- [ ] **Step 5: Build and commit**

```bash
lake build
jj commit -m 'feat(cobham-term): characterise the structure map fold'\''s output word'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 7: Documentation and the amended obligation

**Files:**

- Modify: `docs/index.md` (the new `Initial.lean` entry, and the existing
  `Bound.lean` entry)
- Modify: `TODO.md` (§ The fold over recognized terms, first bullet)

**Interfaces:**

- Consumes: every name Tasks 3 to 6 produced.
- Produces: no Lean.

- [ ] **Step 1: Add the `docs/index.md` entry**

Insert after the `Geb/Internal/Computability/CobhamFoldProto/SmashFree.lean`
entry, which is the last of the group, matching the surrounding entries'
form — the module path, what it holds, the names, then `Depends on` and the
axiom note:

```markdown
- `Geb/Internal/Computability/CobhamFoldProto/Initial.lean` — the initial
  algebra's structure map at the carrier `List Bool`, and that map as an
  expression of Cobham's class. `algMk` is a symbol's block followed by its
  children's spellings, so `fold_algMk` reads `Term.fold` at it as
  `RankedAlphabet.spell` itself by `rfl`: `algMk` is the step `spell`'s own
  `WType.elim` runs, named apart from it, and the preorder encoding is the
  unique morphism from the term algebra into it by the initiality
  `Term.fold_unique` carries. The carrier is not itself initial, the
  spellings being a proper subalgebra of `List Bool`, so what the equation
  says is that `algMk` is the structure map transported along the encoding.
  `length_algMk` reads its growth as exactly `R.width`, and `foldOut_algMk`
  reads the fold as the identity on the recognized language. `flattenOf`
  concatenates an arity's slots, by `Nat.rec` on the arity with the
  arity-`n` tail composed against the shifted projections, and `mkOf`
  prepends the symbol's block to it; `semAt_flattenOf` and `semAt_mkOf` say
  what each computes. `growth_algMk`,
  `stackSize_algMk_le`, `smashFreeBool_flattenOf` and `smashFreeBool_mkOf`
  discharge the obligations `foldOutExprV` and `smashFree_foldOutExprV` take,
  the multiplier constraint `2 * R.width + 2 ≤ mult` remaining a hypothesis
  since the multiplier is the caller's. `foldOutSemV_algMk` characterises the
  expression's output word for every input word — `outWordV` of the input on
  the recognized language and the absence marker off it — without evaluating
  the readout's dispatch, and `smashFree_foldOutExprV_mkOf` places the
  expression in the subalgebra `Cobham.SmashFree` names. Depends on
  `Geb.Internal.Computability.CobhamFoldProto.SmashFree`.
  `Classical.choice`-free.
```

- [ ] **Step 2: Amend the `Bound.lean` entry**

Task 4 adds `semAt_compOf` to `Bound.lean` and re-proves
`SelfDelim.lean`'s `stepWord_compOf` through it, so those two entries are
amended in the branch that changes them.

Append to the `Geb/Internal/Computability/CobhamFoldProto/Bound.lean` entry,
before its `Depends on` sentence, matching that entry's two-space
continuation indent:

```markdown
  `semAt_compOf` reads a composition's meaning at every arity, as
  `semAt_prependOf`, `semAt_constAtOf`, `semAt_projOf` and
  `semAt_concatCompOf` do for their own combinators;
  `CobhamFoldProto/SelfDelim.lean`'s `stepWord_compOf` is its arity-one
  instance.
```

`docs/index.md`'s `SelfDelim.lean` entry does not name `stepWord_compOf` at
all, so it needs no amendment.

- [ ] **Step 3: Amend `TODO.md`**

In § The fold over recognized terms, the first bullet reads:

```text
- Neither construction is exercised on an input at the expression level. The
  samples evaluate the semantic fold, and the `decide` on `unitExpr` checks
  tree shape rather than value, so no expression's output word has been computed
  from an input word.
```

Replace it with:

```text
- Neither construction is exercised on an input at the expression level. The
  samples evaluate the semantic fold, and the `decide` on `unitExpr` checks
  tree shape rather than value, so no expression's output word has been computed
  from an input word. `Geb.CobhamFold.foldOutSemV_algMk` characterises one
  expression's output word for every input word, at the algebra rebuilding its
  argument, but characterises it symbolically rather than computing it: the
  readout dispatches on `2 ^ readoutWidthV R` branches, so the characterisation
  is by proof rather than by normalization. What remains outstanding is an
  output word computed from an input word.
```

- [ ] **Step 4: Lint the Markdown**

```bash
markdownlint-cli2 'docs/index.md' 'TODO.md'
bash scripts/check-md-links.sh
doctoc --dryrun --update-only .
```

Expected: all three exit zero. `docs/index.md` and `TODO.md` both carry
doctoc TOCs, and neither edit adds a heading, so the TOC check passes
unchanged.

- [ ] **Step 5: Commit**

```bash
jj commit -m 'doc(cobham-term): index the structure map and amend its obligation'
jj bookmark set feat/cobham-term-mk -r @-
```

---

## Task 8: Verify the branch and remove the spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-08-15-ranked-term-constructor-design.md`
- Delete: `docs/superpowers/plans/2026-08-15-ranked-term-constructor-plan.md`

**Interfaces:**

- Consumes: the whole branch.
- Produces: a branch whose working tree carries no transient artifact, per
  CONTRIBUTING.md § Concern shape.

- [ ] **Step 1: Run the authoritative gate**

`scripts/pre-push.sh` is the authoritative checklist under
CONTRIBUTING.md § Working and docs/rules/ci-and-workflow.md § Pre-push
checklist, and it is a superset of any command listed here.

```bash
bash scripts/pre-push.sh
```

Expected: exit zero. The script exits non-zero on the first failure and names
the step; read the script for what each step runs rather than relying on a
list in this plan, which would drift from it. `lake lint` is where
`GebMeta.detectNonstandardAxiom` runs; a failure there names a declaration
depending on an axiom outside `{propext, Quot.sound}`. To narrow a failure,
re-run the named step alone, then re-run the whole script.

- [ ] **Step 2: Run the mandated review skills**

CLAUDE.md § Phase-driven workflow binds
`superpowers:verification-before-completion` at the pre-commit phase, and
docs/rules/lean-coding.md § Lean 4 skill workflows names `review` for
pre-commit Lean review and `golf` for polishing a proof. Run them on this
branch's Lean diff before the next step.

Do not claim the branch passes without the output of Step 1 in hand. If any
command fails, fix the cause in the task that introduced it and re-run the
whole script, not just the failing step.

- [ ] **Step 3: Remove the spec and the plan**

```bash
rm docs/superpowers/specs/2026-08-15-ranked-term-constructor-design.md
rm docs/superpowers/plans/2026-08-15-ranked-term-constructor-plan.md
```

The destructor branch's spec and plan are not in this branch's working copy
and are unaffected. Keep the parked copies under
`.superpowers/cobham-term-handoff/` until the destructor branch has committed
its own.

- [ ] **Step 4: Re-run the Markdown checks**

```bash
markdownlint-cli2 '**/*.md'
bash scripts/check-md-links.sh
```

Expected: both exit zero. Then re-run the authoritative gate, so the state
that is committed is the state that was gated:

```bash
bash scripts/pre-push.sh
```

Expected: exit zero. Nothing under `docs/` links to either removed
file: `docs/index.md`'s new entries name only Lean modules.

- [ ] **Step 5: Commit**

`scripts/pre-push.sh` runs `check-commit-msg.sh` over
`fork_point(main | @)..@`, which does not yet include the commit this step
creates, so check this one subject by hand first.

```bash
printf '%s\n' 'doc(cobham-term): remove the transient spec and plan' \
  | bash scripts/check-commit-msg.sh
jj commit -m 'doc(cobham-term): remove the transient spec and plan'
jj bookmark set feat/cobham-term-mk -r @-
```

The subject is 52 characters and conforms; the check is here so the last
commit is not the one nothing verified.

- [ ] **Step 6: Hand off**

The branch is ready for the user's line-by-line review. Do not push: no
`jj git push` runs without that review, first-creation pushes included.
Report to the user, in the session rather than in any committed file: which
gate steps were run and what each returned, which of the risks below were
hit, and which repairs named in Tasks 4 to 6 were needed. Before that review
turns into a pull request, `pr-review-toolkit:review-pr` is the remaining
mandated pass.

---

## Risks this plan carries

- `semAt_mkOf` at a symbolic arity rests on a `Nat.rec` over a family of
  expressions (`semAt_flattenOf`). The fallback the spec records is to state
  it at literal arities, as `GebTests`' `leafCountOf` does, which weakens the
  deliverable to the alphabets exhibited. Task 4 Step 4 states the proof in
  the form that elaborates, including the `simp only [semAt_projOf]` the `ih`
  rewrite needs.
- The expressions may not evaluate in budget, which is why no `#guard`
  against an expression's output word is a deliverable and why Task 6's
  statement is symbolic. If a later reader wants a computed output word, it
  is the `TODO.md` item Task 7 amends, not a repair to this branch.
