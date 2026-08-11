# Segment 3 implementation plan: the fold at a carrier with a bit encoding

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Global constraints](#global-constraints)
- [What was compiled before this plan was written](#what-was-compiled-before-this-plan-was-written)
- [Deviations from the design](#deviations-from-the-design)
- [File structure](#file-structure)
- [Task 0: commit the plan and the prototypes](#task-0-commit-the-plan-and-the-prototypes)
- [Task 1: the step and the word it contributes](#task-1-the-step-and-the-word-it-contributes)
- [Task 2: the fold's meaning and its two clauses](#task-2-the-folds-meaning-and-its-two-clauses)
- [Task 3: the length invariant and the expression](#task-3-the-length-invariant-and-the-expression)
- [Task 4: the carrier-level fold](#task-4-the-carrier-level-fold)
- [Task 5: the mirror](#task-5-the-mirror)
- [Task 6: the documentation](#task-6-the-documentation)
- [Task 7: remove the transient design and hand off](#task-7-remove-the-transient-design-and-hand-off)
- [Whole-segment review](#whole-segment-review)
  - [Part A: after task 6, before task 7](#part-a-after-task-6-before-task-7)
  - [Part B: inside task 7, after step 5 and before step 6](#part-b-inside-task-7-after-step-5-and-before-step-6)
  - [After task 7 step 8](#after-task-7-step-8)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

`Geb/Mathlib/Computability/Cobham/Fold.lean`: the catamorphism of a list of
bits at a carrier admitting a `p`-bit encoding, as an expression of Cobham's
class, closing B3 of [TODO.md](../../../TODO.md) § Extensions of the tree
recognizers.

**Architecture.** The fold is the scan combinator of `Cobham/Scan.lean` at a
constant base and two steps, each step a dispatch over the `p` bits of the
state built from the case combinator of `Cobham/Cases.lean`. The carrier
enters only through `enc : α → Fin p → Bool` and `dec : (Fin p → Bool) → α`;
neither `Fintype` nor `FinEnum` appears, and `dec` is unconstrained off the
image of `enc` except in the one theorem that consumes the retraction
hypothesis.

**Tech stack.** Lean 4 (`v4.33.0`), mathlib, `lake`.

**Specification.**
[The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md)
§ Segment 3. Read
[the workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) § Facts
established by building before writing any Lean here.

## Global constraints

Copied from the design § Constraints this design is bound by, and from the
repository rules each task is bound by in full.

- **No `noncomputable`, and `Classical.choice` excluded.** Every declaration
  measures `[propext, Quot.sound]`, which `lake lint` enforces. Every
  declaration of `Geb/Internal/FoldSpike.lean` was measured at that set, as
  were three of the mirror prototype's theorems, one of them at `[propext]`
  alone. Two of the mirror prototype's theorems were not measured there — the
  predecessors of `counterFold_values` and of `length_wordsUpTo_seven` — and
  are first measured by `lake lint -- GebTests` in task 5 step 5. A task that
  changes a proof re-measures.
- **Recursion through recursors.** No `def` calls itself and no `induction`
  tactic appears; every recursion here is an explicit `List.rec`.
- **An unreferenced binder is an error.** `linter.unusedVariables` is an error
  under `weak.warningAsError`. `length_foldSem`'s recursive value is genuinely
  unused and is bound as `_`.
- **`linter.flexible`, `linter.unnecessarySeqFocus` and `linter.style.show`
  are errors.** A bare `simp` that modifies the goal must be terminal;
  `tac1 <;> tac2` where `tac1` leaves one goal fails; a `show` that changes
  the goal must be `change`.
- **Universes are declared.** `universe u` and `variable {α : Type u}`;
  `Type*` appears nowhere in `Geb/`.
- **`native_decide` is forbidden**, carrying a compiler-trust axiom.
- **Line length 100, indentation 2, no tabs**, per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Coding style.
- **Module docstring sections in order and non-vacuous**, and a `/-- … -/`
  docstring on every `def` and every theorem of public interest, per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation.
- **Imports.** `Geb/Mathlib/` may import only `Mathlib.*`,
  `Batteries.*` and `Geb.Mathlib.*`, and the prefix `Geb.Mathlib.` appears
  only on `import` lines. `scripts/lint-imports.sh` enforces this.
- **Commit subjects** are imperative present, no capital, no trailing period,
  under 72 characters where possible, with a type from
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Commit-message convention.
- **`jj` for every state-mutating VCS operation**; no mutating `git`
  subcommand. No push.
- **Build alone.** Two concurrent `lake build` invocations corrupt package
  `.trace` files; the `lean-lsp` tools that run Lean count as a second
  process.

## What was compiled before this plan was written

Every declaration below was compiled at a symbolic `α` and `p` in
`Geb/Internal/FoldSpike.lean`, and every one measured
`[propext, Quot.sound]`. The code in the tasks is transcribed from that
module, not composed here. The fixture was compiled in
`Geb/Internal/FoldSpikeMirror.lean`, a separate module, so that the mirror's
reduction was measured across a module boundary rather than in the module
that declares the definitions.

Measured, and not predicted:

1. **`constAtOf` takes the arity explicitly**, `constAtOf (n : ℕ)
   (u : List Bool) : COf n`. The design writes `constAtOf (List.ofFn (enc
   init))`, which does not elaborate; the calls are `constAtOf 0 …` for the
   base and `constAtOf 1 …` for a branch.
2. **`rw` does not unfold `foldStep`.** `stepWord_foldStep` opens with a
   `change` to the `diagOf (casesOf …)` form before `stepWord_diagOf` applies,
   and needs a second `change` to present the goal as `casesSem` before
   `casesSem_eq` applies.
3. **`scanSem_cons` is not a `rfl`**, so `foldSem ![b :: w]` is not
   definitionally the step applied to `foldSem ![w]` and a `change` does not
   reach it. `foldSem_cons` is stated and proved from `scanSem_cons`, its last
   step `cases b <;> rfl` discharging `scanStepWord`'s `if`.
4. **`Cobham.scanSem_eq_eval` instantiates directly at this base and step**,
   and `Cobham.scanOf` likewise, so `foldSem_eq_eval` and `foldOf` reuse them
   rather than restating them as `rfl` and `⟨fold …, rfl⟩`. Both forms were
   compiled and both measure `[propext, Quot.sound]`; the instantiating form
   is the one `Cobham/RankedTree.lean` uses. `scanSem_eq_eval` is itself a
   `rfl`, unlike `casesSem_eq_eval`, whose transport is opaque.
5. **`#eval` of a fold value fails** with "Could not find native
   implementation of external declaration `Cobham.constAt`" — the cross-module
   IR gap [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Lean 4
   module system records. The mirror asserts by `decide`, which the kernel
   evaluates and which needs no `public meta import`.
6. **The sweep budget is seven.** At 255 words the sweep closes in about
   twelve seconds under `set_option maxRecDepth 100000 in decide`; at 511
   words it reaches the 200000-heartbeat `isDefEq` limit and fails. At 127
   words it closes in about six seconds. The measurement was taken against an
   enumeration declared in the measuring module; the mirror imports
   `wordsUpTo` instead, whose definition is identical, so if the imported
   enumeration proves dearer the repair is to drop the sweep to six rather
   than to raise a limit. Dropping to six means dropping task 5 step 2 with
   it, six being a length `length_wordsUpTo_six` already records, and editing
   three further sites that name the length: the mirror's `## Main statements`
   bullet, its `## Implementation notes`, and `counterFold_sweep`'s own
   docstring. It also means adding the `Cobham/Fold` mirror to
   `length_wordsUpTo_six`'s docstring, which currently names only the
   `Cobham/RankedTree` mirror's sweeps.
7. **`linter.hashCommand` logs at info, not error**, so `#print axioms` is
   available inside a `Geb/` module for measuring a prototype. It remains
   barred from committed library code by review, not by the linter.

The literature question the design § Risks records as open — whether "an
expression of the class computes a finite automaton's encoded state" is
published — was searched with `theoremsearch` (`theorem_search`) and
`arxiv-mcp-server` (`search_papers`) before this plan was written. No source
states it. What the search returns is the surrounding landscape: the
identification of the class with the polynomial-time functions, which
`docs/references.bib` already carries as [Cobham1965]. The containment of the
regular languages in that class is a corollary of it and is not what this
segment delivers; what this segment delivers is a term of the algebra, and no
source exhibits one. **The definitions and statements here are novel, and
`docs/references.bib` gains no key in this segment.**

## Deviations from the design

Stated rather than silently taken, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review of specs and plans.

- **`foldSem_def` is dropped.** The design lists it. It is `rfl`, and
  `foldSem` is `@[expose]`, so a downstream consumer unfolds the definition
  without it; nothing in this segment or in the mirror consumes it. Carrying
  it is a committed byte with no return, against
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. What consumers
  need are `foldSem_nil` and `foldSem_cons`, which the design does not name
  and which this plan adds.
- **`stepWord_foldStep`, `foldSem_nil`, `foldSem_cons` and `length_foldSem`
  are added.** The design names none of them. The first is the step's word
  characterisation, through which both headline statements route; the next two
  are the scan's two clauses at this base and step, which `scanSem_nil` and
  `scanSem_cons` do not directly supply because the design's declarations are
  stated over `foldSem` rather than over the spelled-out `scanSem`; the last
  is the length equality that `length_foldSem_le` weakens, and is what makes
  the retraction hypothesis's absence from the length statement visible.
- **`length_foldSem_le` keeps the design's spelled-out `scanSem` form.** It is
  the exact type `Cobham.scan`'s `hbound` argument asks for, so `fold` passes
  it with no bridging.
- **`foldSem_eq` quantifies over the word inside the statement.** The design
  writes `foldSem_eq (hdec) (w : List Bool)`; this plan writes
  `foldSem_eq (hdec) : ∀ w : List Bool`, which is the form measured. It is a
  choice and not a requirement — `Cobham.scanSem_eq` takes `(w : List Bool)`
  explicitly and is proved by `List.rec … w` — and the two differ in no way a
  caller can observe.
- **`foldSem_eq` recurses through `foldSem_cons`, not through `scanSem_eq`.**
  The design sketches it as a `List.rec` over `w` through `scanSem_eq`. Both
  routes reach the same statement;
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) leaves proof
  strategy free, and routing through the module's own cons clause is what
  keeps the rewrite chain in task 4 a single line.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Computability/Cobham/Fold.lean` | Created. The whole segment's content: the step, the fold's meaning, the expression, and the statements over them. |
| `Geb/Mathlib/Computability/Cobham.lean` | Modified. Gains an import of the new module; `lakefile.toml`'s glob builds the module either way, but without this import it is outside the `Geb` umbrella's closure and so is not linted. |
| `GebTests/Mathlib/Computability/Cobham/Fold.lean` | Created. The mirror: a carrier whose `dec` is not injective off the image of `enc`. |
| `GebTests/Mathlib/Computability/Cobham.lean` | Modified. Gains an import of the mirror. |
| `docs/index.md` | Modified. The entry for the new module. |
| `TODO.md` | Modified. The B3 bullet replaced by a done bullet; the closing paragraph's reference to the design reworded. |
| `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` | Modified. Gains `length_wordsUpTo_seven`, the length this segment's sweep uses. |
| `Geb/Internal/FoldSpike.lean`, `Geb/Internal/FoldSpikeMirror.lean` | Committed in task 0, both deleted in task 5, step 7, in one `chore` commit. Tasks 1 to 5 transcribe from them, and the second imports the first. |
| `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md` | Modified in task 7. Survives the segment: B4 and B5 are still to come and this is the document that describes them. |
| `docs/superpowers/plans/2026-08-10-tree-recognizer-session-handoff.md` | Replaced in task 7, for the next session. |
| `docs/superpowers/specs/2026-08-10-cobham-cases-fold-ranked-design.md` | Deleted in task 7, with every link to it removed in the same commit. |
| `docs/superpowers/plans/2026-08-10-cobham-fold-segment.md` | This plan. Committed in task 0, deleted in task 7. |

---

## Task 0: commit the plan and the prototypes

**Files:**

- Commit: `docs/superpowers/plans/2026-08-10-cobham-fold-segment.md`
- Commit: `Geb/Internal/FoldSpike.lean`, `Geb/Internal/FoldSpikeMirror.lean`

At the point this plan is written, all three files are additions sitting in
the working copy, and no commit contains them.
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape orders the branch
"1. Commits adding the spec and plan… 2. Commits implementing the change…
3. Commits removing the spec and plan", so they are committed before any
implementation commit rather than being swept into the first `feat`. The
previous segment did the same, in `f6cf8de4`
(`chore(cobham): prototype the generic ranked recognizer`) and `8d4e9464`
(`doc(cobham): plan the generic ranked recognizer segment`) — prototype first,
then plan — and removed the prototype in `20a514d0`.

This also makes task 5 step 7's deletion a deletion in the diff rather than
the discarding of a file no commit ever held, and makes the File structure
table's account of the two prototypes true as written.

- [ ] **Step 1: commit the plan**

```bash
jj commit -m "doc(cobham): plan the fold segment" \
  docs/superpowers/plans/2026-08-10-cobham-fold-segment.md
```

- [ ] **Step 2: commit the prototypes**

```bash
jj commit -m "chore(cobham): prototype the fold at a bit-encoded carrier" \
  Geb/Internal/FoldSpike.lean Geb/Internal/FoldSpikeMirror.lean
```

Both prototypes go in one commit: the second imports the first, so a commit
containing only one of them does not build.

- [ ] **Step 3: confirm the working copy is clean**

Run: `jj st`

Expected: no remaining changes. If `jj commit` with paths leaves anything
behind, commit it before starting task 1 — an implementation commit must not
carry planning artifacts.

---

## Task 1: the step and the word it contributes

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/Fold.lean`
- Modify: `Geb/Mathlib/Computability/Cobham.lean`

**Interfaces:**

- Consumes: `Cobham.COf`, `Cobham.diagOf`, `Cobham.casesOf`,
  `Cobham.constAtOf`, `Cobham.bits`, `Cobham.stepWord`,
  `Cobham.stepWord_diagOf`, `Cobham.casesSem`, `Cobham.casesSem_eq`,
  `Cobham.stepWord_constAtOf`, all from
  `Geb.Mathlib.Computability.Cobham.Cases` and its public imports.
- Produces: `Cobham.foldStep (enc : α → Fin p → Bool)
  (dec : (Fin p → Bool) → α) (step : Bool → α → α) (b : Bool) : COf 1`, and
  `Cobham.stepWord_foldStep`, whose statement is
  `stepWord (foldStep enc dec step b) u =
  List.ofFn (enc (step b (dec (bits p u))))`.

The section variables are declared in the order `enc`, `dec`, `init`, `step`;
Lean includes in each declaration exactly those it mentions, so `foldStep`
takes `enc dec step` and not `init`, and every later declaration mentioning
`init` takes all four in that order.

- [ ] **Step 1: create the module with its header, imports and docstring**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases

/-!
# The fold at a carrier with a bit encoding

The catamorphism of a list of bits at a carrier admitting a `p`-bit encoding,
as an instance of the scan combinator. The carrier is arbitrary; its
finiteness enters only through the existence of the encoding, and `dec` is
unconstrained off the image of `enc`.

## Main definitions

* `Cobham.foldStep` — the fold's step, a dispatch on the encoded state.
* `Cobham.foldSem` — the meaning of the scan at the encoded base and the two
  steps.
* `Cobham.fold`, `Cobham.foldOf` — the fold as an expression of `C`, and at
  its declared arity.

## Main statements

* `Cobham.stepWord_foldStep` — the word the step contributes.
* `Cobham.foldSem_nil`, `Cobham.foldSem_cons` — the fold on the empty word and
  on one bit.
* `Cobham.length_foldSem` — every state the fold produces has the encoding's
  width.
* `Cobham.length_foldSem_le` — the growth bound that width gives, in the form
  the scan combinator asks for.
* `Cobham.foldSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression carries.
* `Cobham.foldSem_eq` — the fold computes the carrier-level fold, encoded.

## Implementation notes

Neither the encoding-to-word nor the carrier-level fold is named: they are
`List.ofFn (enc a)` and `w.foldr step init`, spelled at the length a name
would cost. The two sides of `foldSem_eq` inhabit different types before
`List.ofFn ∘ enc` is applied, so the encoding is applied rather than the two
equated.

`foldr` is the fold `Cobham.scanSem_eq` presents the scan as, and the
direction `Cobham.evalRec` recurses in. The statement is over the Lean list on
both sides, so no convention about which end of the word the list's head
denotes enters it.

`length_foldSem` and the bound `length_foldSem_le` that weakens it precede the
retraction hypothesis and do not take it: every state the scan produces is a
`List.ofFn` of an `enc` value — the base by `baseWord_constAtOf`, each step by
`stepWord_constAtOf` — so its length is the encoding's width whatever `dec`
does. Consequently `fold`, `foldOf` and `foldSem_eq_eval` take no retraction
hypothesis either.

`Fintype` and `FinEnum` appear nowhere, which keeps the module clear of the
ordered-algebra and `Finset` instances the axiom rules warn about. The module
takes no decision and carries no `Decidable` instance, so
`DecidableEq (Fin p → Bool)`, which resolves through
`Fintype.decidablePiFintype` and depends on `Classical.choice`, does not
arise; a consumer deciding an equality of states decides it over `List Bool`,
the states already being `List.ofFn` values.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, fold, catamorphism
-/

namespace Cobham

public section

universe u

variable {α : Type u} {p : ℕ} (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (init : α) (step : Bool → α → α)

end

end Cobham
```

The module docstring is written whole here, naming declarations that tasks 2
to 4 introduce. That is deliberate: the docstring describes the module the
segment delivers, and the segment is one pull request whose intermediate
commits are steps rather than separately shippable states. Nothing gates on
the forward reference: the linters check that declarations carry docstrings,
not that every name a docstring mentions already exists.

- [ ] **Step 2: add the import to the source index**

In `Geb/Mathlib/Computability/Cobham.lean`, add
`public import Geb.Mathlib.Computability.Cobham.Fold` in the existing
alphabetical position among the sibling imports. Without it the module is
built by `lakefile.toml`'s glob but is not in the `Geb` umbrella's import
closure, so `lake lint` does not lint it and
`scripts/tests/test-lint-driver.sh` reports it as escaping the linter.

- [ ] **Step 3: run the build to confirm the empty module elaborates**

Run: `lake build Geb.Mathlib.Computability.Cobham.Fold`

Expected: builds. A `variable` block none of whose variables is yet mentioned
is not an error; `linter.unusedVariables` fires on binders of a declaration,
not on an unconsumed `variable` line. If it does error, the repair is to
defer the `variable` line to step 4 rather than to suppress the linter.

- [ ] **Step 4: add the step and its word characterisation**

Inside the `public section`, after the `variable` line:

```lean
/-- The fold's step at a bit: decode the state, apply the carrier-level step,
and spell the result. The dispatch is over the `p` bits of the state, which the
diagonal supplies in both the scrutinee and the argument position. -/
@[expose] def foldStep (b : Bool) : COf 1 :=
  diagOf (casesOf p fun v ↦ constAtOf 1 (List.ofFn (enc (step b (dec v)))))

/-- The step spells the carrier-level step of the state it decodes. -/
theorem stepWord_foldStep (b : Bool) (u : List Bool) :
    stepWord (foldStep enc dec step b) u =
      List.ofFn (enc (step b (dec (bits p u)))) := by
  change stepWord (diagOf (casesOf p fun v ↦
    constAtOf 1 (List.ofFn (enc (step b (dec v)))))) u = _
  rw [stepWord_diagOf]
  change casesSem p (fun v ↦ constAtOf 1 (List.ofFn (enc (step b (dec v)))))
    ![u, u] = _
  rw [casesSem_eq, stepWord_constAtOf]
```

Both `change`s are load-bearing and were established by a failed build. The
first is needed because `rw` is syntactic and will not unfold `foldStep`;
without it `rw [stepWord_diagOf]` fails with "Did not find an occurrence of
the pattern `stepWord (diagOf ?e) ?u`". The second presents the goal as
`casesSem` so that `casesSem_eq` applies.

- [ ] **Step 5: build and confirm**

Run: `lake build Geb.Mathlib.Computability.Cobham.Fold`

Expected: builds with no error and no warning.

- [ ] **Step 6: measure the axioms**

Run: `lake lint`

Expected: passes. `GebMeta.detectNonstandardAxiom` fails the lint if any
declaration depends on an axiom outside `{propext, Quot.sound}`; both
declarations measured that set in the prototype.

- [ ] **Step 7: commit**

```bash
jj commit -m "feat(cobham): dispatch the fold's step on the encoded state"
```

---

## Task 2: the fold's meaning and its two clauses

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Fold.lean`

**Interfaces:**

- Consumes: `Cobham.foldStep` from task 1; `Cobham.Sem` and
  `Cobham.constAtOf` from `Cobham/Basic.lean`; `Cobham.scanSem`,
  `Cobham.stepWord`, `Cobham.scanSem_nil` and `Cobham.scanSem_cons` from
  `Cobham/Scan.lean`; `Cobham.baseWord_constAtOf` from `Cobham/Cases.lean`.
- Produces: `Cobham.foldSem (enc) (dec) (init) (step) : Sem 1`;
  `Cobham.foldSem_nil : foldSem enc dec init step ![[]] =
  List.ofFn (enc init)`; `Cobham.foldSem_cons (b : Bool) (w : List Bool) :
  foldSem enc dec init step ![b :: w] =
  stepWord (foldStep enc dec step b) (foldSem enc dec init step ![w])`.

- [ ] **Step 1: add the meaning and the two clauses**

Appended after `stepWord_foldStep`:

```lean
/-- The fold's meaning: the scan at the encoded base and the two steps, with
the encoding's width as the growth bound. -/
@[expose] def foldSem : Sem 1 :=
  scanSem (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p

/-- The fold on the empty word is the encoded initial value. -/
theorem foldSem_nil : foldSem enc dec init step ![[]] = List.ofFn (enc init) :=
  (scanSem_nil (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p).trans (baseWord_constAtOf _)

/-- One step of the fold: the bit selects the step, which reads the value the
fold of the rest of the word returns. -/
theorem foldSem_cons (b : Bool) (w : List Bool) :
    foldSem enc dec init step ![b :: w] =
      stepWord (foldStep enc dec step b) (foldSem enc dec init step ![w]) :=
  (scanSem_cons (constAtOf 0 (List.ofFn (enc init)))
    (foldStep enc dec step false) (foldStep enc dec step true) p b w).trans
    (by cases b <;> rfl)
```

`foldSem_cons` cannot be a `change` from `scanSem_cons`: that lemma is not a
`rfl`, its last step identifying `fun _ : Fin 1 ↦ r` with `![r]` by `funext`.
The trailing `cases b <;> rfl` reduces `scanStepWord`'s `if` at each literal
bit; `cases b` leaves two goals, so `<;>` does not trip
`linter.unnecessarySeqFocus`.

- [ ] **Step 2: build and confirm**

Run: `lake build Geb.Mathlib.Computability.Cobham.Fold`

Expected: builds with no error and no warning.

- [ ] **Step 3: run the linter**

Run: `lake lint`

Expected: passes, all three declarations at `{propext, Quot.sound}`.

- [ ] **Step 4: commit**

```bash
jj commit -m "feat(cobham): give the fold's meaning as a scan"
```

---

## Task 3: the length invariant and the expression

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Fold.lean`

**Interfaces:**

- Consumes: `Cobham.foldStep`, `Cobham.foldSem`, `Cobham.foldSem_nil`,
  `Cobham.foldSem_cons` and `Cobham.stepWord_foldStep` from tasks 1 and 2;
  `Cobham.scan`, `Cobham.scanOf`, `Cobham.scanSem` and
  `Cobham.scanSem_eq_eval` from `Cobham/Scan.lean`; `Cobham.C`, `Cobham.COf`,
  `Cobham.constAtOf`, `Cobham.transport` and `Cobham.C.eval` from
  `Cobham/Basic.lean`.
- Produces: `Cobham.length_foldSem : ∀ w : List Bool,
  (foldSem enc dec init step ![w]).length = p`;
  `Cobham.length_foldSem_le (w : List Bool)`, stated over the spelled-out
  `scanSem`; `Cobham.fold : C`; `Cobham.foldOf : COf 1`;
  `Cobham.foldSem_eq_eval`.

- [ ] **Step 1: add the length invariant, the expression and the bridge**

Appended after `foldSem_cons`:

```lean
/-- Every state the fold produces has the encoding's width, whatever `dec`
does off the image of `enc`. -/
theorem length_foldSem : ∀ w : List Bool,
    (foldSem enc dec init step ![w]).length = p :=
  List.rec
    (by rw [foldSem_nil, List.length_ofFn])
    (fun b v _ ↦ by
      rw [foldSem_cons, stepWord_foldStep, List.length_ofFn])

/-- The growth bound the scan combinator asks for, tight at the empty word. -/
theorem length_foldSem_le (w : List Bool) :
    (scanSem (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
      (foldStep enc dec step true) p ![w]).length ≤ w.length + p :=
  (length_foldSem enc dec init step w).le.trans (Nat.le_add_left p w.length)

/-- The fold as an expression of `C`. -/
@[expose] def fold : C :=
  scan (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)

/-- `fold` at its declared arity. -/
@[expose] def foldOf : COf 1 :=
  scanOf (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)

/-- The meaning read at the raw tree is the meaning the expression carries. -/
theorem foldSem_eq_eval :
    transport (foldOf enc dec init step).2 (foldOf enc dec init step).1.eval =
      foldSem enc dec init step :=
  scanSem_eq_eval (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)
```

`foldOf` and `foldSem_eq_eval` instantiate `Cobham.scanOf` and
`Cobham.scanSem_eq_eval` rather than restating them as `⟨fold …, rfl⟩` and
`rfl`. Both forms compile and measure the same axioms; the instantiating form
is what `Cobham/RankedTree.lean` uses for the same construction, and
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost asks for the
existing abstraction to be reused rather than re-derived.

The recursive value in `length_foldSem` is bound as `_`: the fold's step
ignores the state's content, so the length at a cons does not depend on the
length at the tail. Naming it would trip `linter.unusedVariables`, which is an
error here.

`length_foldSem_le` is stated over the spelled-out `scanSem` rather than over
`foldSem` because that is the type `Cobham.scan`'s `hbound` argument asks for,
so `fold` passes it directly.

`scanSem_eq_eval` is itself a `rfl`, the scan node's own arity reducing to one
whatever its children are, so its transport disappears by proof irrelevance.
Do not copy `casesSem_eq_eval`'s proof, whose transport is opaque.

- [ ] **Step 2: build and confirm**

Run: `lake build Geb.Mathlib.Computability.Cobham.Fold`

Expected: builds with no error and no warning.

- [ ] **Step 3: run the linter**

Run: `lake lint`

Expected: passes.

- [ ] **Step 4: commit**

```bash
jj commit -m "feat(cobham): give the fold as an expression of the class"
```

---

## Task 4: the carrier-level fold

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Fold.lean`

**Interfaces:**

- Consumes: `Cobham.foldSem_nil`, `Cobham.foldSem_cons`,
  `Cobham.stepWord_foldStep` from tasks 1 and 2; `Cobham.bits_ofFn` from
  `Cobham/Cases.lean`.
- Produces: `Cobham.foldSem_eq (hdec : ∀ a, dec (enc a) = a) :
  ∀ w : List Bool, foldSem enc dec init step ![w] =
  List.ofFn (enc (w.foldr step init))`. This is the module's content and the
  deliverable of B3.

- [ ] **Step 1: add the theorem**

Appended after `foldSem_eq_eval`:

```lean
/-- The fold computes the carrier-level fold of the word, encoded. This is
where the retraction hypothesis enters: the state the scan carries is an
encoded carrier value, so decoding it returns that value. -/
theorem foldSem_eq (hdec : ∀ a, dec (enc a) = a) : ∀ w : List Bool,
    foldSem enc dec init step ![w] = List.ofFn (enc (w.foldr step init)) :=
  List.rec (foldSem_nil enc dec init step)
    (fun b v ih ↦ by
      rw [foldSem_cons, ih, stepWord_foldStep, bits_ofFn, hdec]
      rfl)
```

`hdec` is an explicit binder rather than a section variable: Lean includes a
section variable only where the statement mentions it, so a hypothesis used
only inside a proof would be out of scope. It is the one declaration in the
module that takes it.

The rewrite chain is the proof's whole content. `foldSem_cons` peels the bit;
`ih` replaces the fold of the tail with `List.ofFn (enc (v.foldr step init))`;
`stepWord_foldStep` applies the step to the decoded state;
`bits_ofFn` turns `bits p (List.ofFn (enc a))` back into `enc a`; and `hdec`
turns `dec (enc a)` into `a`. The closing `rfl` discharges
`List.ofFn (enc (step b (v.foldr step init))) =
List.ofFn (enc ((b :: v).foldr step init))`, which `rw` leaves standing
because it closes goals by `rfl` at reducible transparency only.

- [ ] **Step 2: build and confirm**

Run: `lake build Geb.Mathlib.Computability.Cobham.Fold`

Expected: builds with no error and no warning.

- [ ] **Step 3: run the linter**

Run: `lake lint`

Expected: passes.

- [ ] **Step 4: commit**

```bash
jj commit -m "feat(cobham): compute the carrier-level fold"
```

---

## Task 5: the mirror

**Files:**

- Create: `GebTests/Mathlib/Computability/Cobham/Fold.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham.lean`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`
- Delete: `Geb/Internal/FoldSpike.lean`, `Geb/Internal/FoldSpikeMirror.lean`

**Interfaces:**

- Consumes: `Cobham.foldSem` and `Cobham.foldSem_eq` from task 4's module, and
  `wordsUpTo` from `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`, which the
  `RankedTree` mirror already imports the same way. Not every declaration of
  the module, and not transitively either: `foldSem_eq`'s proof reaches
  `foldSem_nil`, `foldSem_cons`, `stepWord_foldStep` and `bits_ofFn`, so what
  the mirror does not reach is `length_foldSem`, `length_foldSem_le`, `fold`,
  `foldOf` and `foldSem_eq_eval` — the expression-of-`C` side. That is
  accepted: those five are exercised by `lake build` and `lake lint`, which
  elaborate and axiom-check them, and the design's § Test mirrors asks this
  mirror only for a carrier whose `dec` is not injective off the image of
  `enc`. `Cobham/RankedTree.lean`'s mirror names `isRankedOf` once for the
  same reason, in a `def` whose docstring says so.
- Produces: nothing other modules consume.

The design asks for "a carrier whose `dec` is not injective off the image of
`enc`, so that the retraction hypothesis is exercised rather than trivially
satisfied". The fixture below is a three-element carrier in two bits: the
fourth bit family `![true, true]` spells no carrier value and `counterDec`
sends it to `2`, the same value as `![false, true]`. `counterDec ∘ counterEnc`
is nonetheless the identity, so the hypothesis holds while injectivity fails.

- [ ] **Step 1: create the mirror**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Mathlib.Data.Tree.Ranked.Basic

import Geb.Mathlib.Computability.Cobham.Fold

/-!
# The fold at a worked carrier

A three-element carrier encoded in two bits, whose decoding is not injective
off the image of the encoding: the fourth bit family spells no carrier value
and decodes to the same value as the third. The retraction hypothesis
`foldSem_eq` takes therefore holds without `dec` being an inverse, which is
what the fixture is chosen to exhibit.

## Main definitions

* `counterEnc`, `counterDec`, `counterStep` — the carrier's encoding, its
  decoding, and the step a bit induces.
* `counterFold` — the fold's value as a function of the word.

## Main statements

* `counterDec_counterEnc` — the decoding is a retraction of the encoding
  without being injective.
* `counterFold_values` — the fold at words whose expected value is written
  out.
* `counterFold_eq` — the fold's agreement with the carrier-level fold, from
  the retraction hypothesis at this decoding.
* `counterFold_sweep` — the same agreement computed in the kernel over every
  word of length at most seven.

## Implementation notes

The assertions reduce in the kernel, by `decide`. `#eval` is not available:
the fold's value calls `Cobham.constAt`, a non-`meta` declaration of another
module of this package, whose IR is not available to meta code across the
boundary, so evaluation fails where elaboration does not.

The sweep length is measured rather than conventional. At length seven the
sweep closes under `set_option maxRecDepth 100000 in decide`; at length eight
it reaches the heartbeat limit. Each step of the fold is a dispatch over two
bits followed by a constant word, and the case tree is a `Nat.rec`, so one
reduction follows a single root-to-leaf path.

## Tags

Cobham, bounded recursion on notation, fold, catamorphism
-/

set_option linter.privateModule false

open Cobham

/-- A three-element carrier encoded in two bits, the family `![true, true]`
spelling no carrier value. -/
def counterEnc : Fin 3 → Fin 2 → Bool :=
  fun a j ↦ ![![false, false], ![true, false], ![false, true]] a j

/-- The decoding, which sends the unreached family `![true, true]` to the same
value as `![false, true]`, so it is not injective off the image of
`counterEnc` while remaining a retraction of it. -/
def counterDec : (Fin 2 → Bool) → Fin 3 :=
  fun v ↦ if v 1 then 2 else if v 0 then 1 else 0

/-- The carrier-level step: a `true` bit advances the counter. -/
def counterStep : Bool → Fin 3 → Fin 3 :=
  fun b a ↦ if b then a + 1 else a

/-- The fold's value at the counter, as a function of the word. -/
def counterFold (w : List Bool) : List Bool :=
  foldSem counterEnc counterDec 0 counterStep ![w]

/-- The decoding is a retraction of the encoding without being injective:
`![false, true]` and `![true, true]` decode alike. -/
theorem counterDec_counterEnc :
    (∀ a, counterDec (counterEnc a) = a) ∧
      counterDec ![false, true] = counterDec ![true, true] :=
  ⟨fun a ↦ match a with | 0 => rfl | 1 => rfl | 2 => rfl, rfl⟩

/-- The fold's value at five words, the counter having advanced once per
`true` bit and wrapped at three. -/
theorem counterFold_values :
    counterFold [] = [false, false] ∧
      counterFold [true] = [true, false] ∧
      counterFold [true, true] = [false, true] ∧
      counterFold [true, true, true] = [false, false] ∧
      counterFold [false, true, false, true] = [false, true] := by decide

/-- The fold agrees with the carrier-level fold at every word, from the
retraction hypothesis at a decoding that is not injective. -/
theorem counterFold_eq (w : List Bool) :
    counterFold w = List.ofFn (counterEnc (w.foldr counterStep 0)) :=
  foldSem_eq counterEnc counterDec 0 counterStep counterDec_counterEnc.1 w

/-- The same agreement read off the reduced values, over every word of length
at most seven. -/
theorem counterFold_sweep :
    (wordsUpTo 7).all (fun w ↦
      counterFold w == List.ofFn (counterEnc (w.foldr counterStep 0))) = true := by
  set_option maxRecDepth 100000 in decide
```

`counterFold_eq` is what makes the fixture answer the design's ask: it applies
`foldSem_eq` at a `dec` that is not injective, so the retraction hypothesis is
discharged from `counterDec_counterEnc.1` rather than from `dec` being an
inverse. `counterFold_sweep` is not redundant beside it: `counterFold_eq` is
the instantiated theorem, while the sweep computes both sides in the kernel
and so exercises the reduction of the expression rather than its proof.

`counterFold` is the `def` value built from the module under test that
`lake shake` infers the import of `Geb.Mathlib.Computability.Cobham.Fold`
from; an assertion inside an anonymous `example` would leave no constant in
the olean and the import would be reported as removable.

- [ ] **Step 2: record the swept length beside the enumeration**

`GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` carries one statement per
length any mirror sweeps — `length_wordsUpTo_five`, `_six` and `_eight` —
each docstring naming the mirror that sweeps it. This segment sweeps seven and
adds the missing one, after `length_wordsUpTo_eight`, that module's
statements being in no particular order already:

```lean
/-- The enumeration the `Cobham/Fold` mirror's sweep holds every word of
length at most seven. -/
theorem length_wordsUpTo_seven : (wordsUpTo 7).length = 255 := by
  set_option maxRecDepth 100000 in decide
```

The `set_option` is needed, as it is for `_six` and `_eight`. That module's
`## Main statements` needs no change: it is prose rather than a list, and
already describes the assertions as giving the length of the enumeration the
other mirrors sweep, which covers a fourth length without naming any.

- [ ] **Step 3: add the import to the test index**

In `GebTests/Mathlib/Computability/Cobham.lean`, add
`import GebTests.Mathlib.Computability.Cobham.Fold` in the existing
alphabetical position. Plain `import`, not `public import`: the test index
uses the plain form throughout, unlike the source index, which uses
`public import` throughout.

- [ ] **Step 4: build the mirror**

Run: `lake build GebTests.Mathlib.Computability.Cobham.Fold`

Expected: builds. Every declaration, docstring and proof of this mirror was
compiled in `Geb/Internal/FoldSpikeMirror.lean`, `counterDec_counterEnc` and
`counterFold_eq` included. What differs from what was compiled there: the
module docstring is new; the enumeration arrives as the imported `wordsUpTo`
rather than as a locally declared copy; two theorems are renamed,
`counterFold_reduces` to `counterFold_values` and `counterFold_sweep_seven` to
`counterFold_sweep`; and four declaration docstrings are rewritten — two that
the prototype posed as questions it was built to answer, and `counterEnc`'s
and `counterDec`'s, which now name the bit family and the retraction. No
proof term differs, and no statement differs beyond the enumeration's name.

`counterDec_counterEnc` is proved by a term-level `match` on `Fin 3` and needs
no tactic. Do not reach for `fin_cases`: it appears nowhere in `Geb/` or
`GebTests/`, and it routes through the `Fintype` and `Finset.univ` machinery
that [docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Constructive-only Lean code warns about, so it would need an axiom
measurement the `match` form does not. The `match`-on-numerals form is the
repository's idiom, as `Cobham/Scan.lean`'s `scan` uses it on `Fin 4`.

- [ ] **Step 5: run the test suite and the test linter**

Run: `lake test` then `lake lint -- GebTests`

Expected: both pass.

- [ ] **Step 6: commit**

```bash
jj commit -m "test(cobham): mirror the fold at a bit-encoded carrier"
```

- [ ] **Step 7: remove the prototypes**

The prototypes are deleted here rather than in task 1 because tasks 1 to 5
transcribe from them: deleting them earlier removes the compiled reference
while it is still being read. Both go in one commit, the second importing the
first, and in a `chore` commit of their own rather than folded into a `feat`.
`20a514d0` is the precedent for the commit type, not for the position: it
removed the previous segment's prototype before that segment's first `feat`.
Here the prototypes are read through task 5, so they are removed after it.

```bash
rm Geb/Internal/FoldSpike.lean Geb/Internal/FoldSpikeMirror.lean
jj commit -m "chore(cobham): remove the fold prototype"
```

`rm` is the whole deletion; `jj` snapshots the working copy at the start of
every command. Then run `lake build` once: nothing imports either prototype,
so the build should be unaffected, and a failure here means something in the
real modules was still resolving against a prototype declaration.

---

## Task 6: the documentation

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

- [ ] **Step 1: add the `docs/index.md` entry**

After the entry for `Geb/Mathlib/Computability/Cobham/RankedTree.lean`, in the
shape the sibling entries use, ending with the dependency list and the
axiom note:

```markdown
- `Geb/Mathlib/Computability/Cobham/Fold.lean` — the catamorphism of a list of
  bits at a carrier admitting a `p`-bit encoding, as an expression of Cobham's
  class. `foldStep` is the case combinator at the `p` bits of the state, its
  branches the constant words spelling the carrier-level step's result, and
  the diagonal supplies the state in both the scrutinee and the argument
  position; `foldSem` is the scan's meaning at that step and at the encoded
  initial value, and `fold` carries the recursion with `Cobham.scan`, its
  bound discharged by `length_foldSem_le`. `foldSem_eq` identifies the value
  with `List.ofFn` of the encoding of `w.foldr step init`, under the
  retraction hypothesis `∀ a, dec (enc a) = a`; `length_foldSem` does not take
  that hypothesis, every state the scan produces being a `List.ofFn` of an
  `enc` value whatever `dec` does off the image of `enc`. The carrier is
  arbitrary and neither `Fintype` nor `FinEnum` appears. Depends on
  `Geb.Mathlib.Computability.Cobham.Cases`. `Classical.choice`-free.
```

The dependency list names the module's direct imports and no others, which is
what every sibling entry does: `Scan.lean` imports only `Basic` and names only
it, `Cases.lean` imports both and names both. `Fold.lean` imports only
`Cases.lean`.

- [ ] **Step 2: record B3 done in `TODO.md`**

Replace the `**B3**, depending on B2:` bullet of § Extensions of the tree
recognizers with a done bullet in the shape the B2 and B6 bullets use:

```markdown
- **B3 is done.** `Geb/Mathlib/Computability/Cobham/Fold.lean` gives the
  catamorphism at a carrier admitting a `p`-bit encoding as an expression of
  `C`: `foldStep` dispatches on the state's bits with the case combinator and
  `fold` carries the recursion with `Cobham.scan`. `foldSem_eq` identifies the
  value with the carrier-level `w.foldr step init`, encoded, under the
  retraction hypothesis. The encoding is not named: it is
  `List.ofFn (enc a)`, and the type distinction survives, `foldSem … ![w]`
  being a `List Bool` and `w.foldr step init` an `α`. See
  <the docs/index.md link, written as the B2 bullet writes it>.
```

Replace that placeholder with the same final sentence the B2 and B6 bullets
carry: the word `See` followed by a Markdown link whose text and target are
both `docs/index.md`. It is described here rather than written out because
`scripts/check-md-links.sh` extracts link targets from fenced code blocks as
well as from prose, and resolves each one relative to the directory of the
file containing it — so a link relative to the repository root written here
would be looked for under `docs/superpowers/plans/` and would fail the check
while the plan is in the tree.

This bullet replaces the sentence the previous text carried, "Its `run_spell`
is stated between a `List Bool` and `List.ofFn` of the carrier's encoding, the
two not being the same type." That sentence names a declaration, `run_spell`,
which exists nowhere in the repository and which this segment does not
introduce; what survives of it is the type distinction, which the replacement
bullet states over the names that do exist. The design and the session handoff
both describe this sentence as a note that the encoding "must be named," which
is not what `TODO.md` says; do not go looking for that phrase, which appears in
`TODO.md` nowhere.

- [ ] **Step 3: reword the sentence naming the design**

In `TODO.md`, the closing paragraph of § Extensions of the tree recognizers —
the one on `BarringtonCorbett1989` and the succinct-tree references, not the
"Deferred:" and "Also deferred:" bullets above it — refers to "the succinct
tree-encoding references the design cites for context." Task 7 removes that
design, so the sentence must stand
without it. Replace the clause naming the design with one naming the works
directly:

```markdown
The same holds for the succinct tree-encoding references
`BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980` and
`BraunmuhlVerbeek1983` — verified but unused, and so added by the branch that
first cites them.
```

- [ ] **Step 4: regenerate the tables of contents and lint the Markdown**

Run:

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
scripts/check-md-links.sh
```

Expected: all three clean.

- [ ] **Step 5: commit**

```bash
jj commit -m "doc(cobham): catalogue the fold at a bit-encoded carrier"
```

---

## Task 7: remove the transient design and hand off

**Files:**

- Delete: `docs/superpowers/specs/2026-08-10-cobham-cases-fold-ranked-design.md`
- Modify: `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md`
- Delete: `docs/superpowers/plans/2026-08-10-cobham-fold-segment.md` (this plan)
- Replace: `docs/superpowers/plans/2026-08-10-tree-recognizer-session-handoff.md`

Segment 3 is the last segment the design specifies, so the design is removed
here, per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape. This
plan is removed with it. The workstream handoff is **not** removed: B4 and B5
are still to come and it is the document that describes them.

- [ ] **Step 1: strip the design's links from the workstream handoff**

`scripts/check-md-links.sh` fails when an internal link's target does not
exist, so every link to the design must go in the same commit that deletes it.
Three documents carry such links, and all three are handled in this task: the
workstream handoff here, the session handoff in step 3, and this plan, which
step 4 deletes. Take the inventory first, so that no site is missed:

```bash
grep -rn 'cobham-cases-fold-ranked-design' docs/
grep -rn -e 'the design' -e 'Design §' docs/superpowers/plans/
```

The second command is not redundant: a prose mention carries no link for the
first to find, and `scripts/check-md-links.sh` sees only `](…)` targets, so a
stale assertion survives every mechanical check. Neither command finds every
site: one mention wraps across a line break, "beyond the three the" ending one
line and "design names" beginning the next, so no single-line pattern matches
it. That site is enumerated explicitly in the last bullet below. Read the
matches rather than counting them.

The workstream handoff carries three Markdown links — in § Read these first,
in § B6 and in § B3 — a fourth site in § B3 that names the design in prose
rather than linking to it, and a fifth in § Facts established by building.
Each is rewritten to carry the content it referred to rather than the
pointer:

- § Read these first: drop the sentence beginning "B6 and B3 are specified,"
  and keep the two sentences that follow it — the one saying B4 and B5 each
  get their own brainstorming phase, spec, plan and adversarial review, and
  the one saying the document is not to be treated as a spec.
- § B6: replace "Built to implementation detail in [the design] § Segment 2,
  which settled the …" with "The `RankedAlphabet.Scan` bit layout is the
  liveness flag, then the incomplete block in a fixed-width slot delimited by
  a sentinel, then the pending count in unary as the tail."
- § B3: replace its opening paragraph, the one beginning
  "`Geb/Mathlib/Computability/Cobham/Fold.lean`. Depends on B2", with a
  statement that B3 is done, pointing at [docs/index.md](../../index.md); the
  branch descriptions in that document are for work not yet started, and B3 no
  longer is. Carry one clause of it forward: that the module is a deliverable
  for later workstreams rather than a dependency of anything here, so having
  no consumer in the repository on landing is its expected condition and not a
  cost to be justified against
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. The design is
  the only other document stating that, and step 4 deletes it.
- § B3's paragraph beginning "The catamorphism at a finite carrier, whose
  step's configurable part carries no restriction of its own": delete it. It
  attributes the construction's conditions to finiteness alone, and the module
  this segment delivers has an arbitrary carrier, an unconstrained `dec` and
  no `Fintype`.
- § B3's paragraph beginning "`Fold.run_spell` relates a `List Bool` to the
  carrier's `p`-bit encoding": delete it. `run_spell` is a declaration that
  exists nowhere in the repository and that this segment does not introduce,
  and its instruction to "name the encoding" is the decision the delivered
  module takes the other way. The type distinction it is about survives in the
  module's own `## Implementation notes`.
- § B3's last paragraph, on rewording `TODO.md`: delete it. Task 6 step 3 has
  done the rewording, so the instruction has no remaining subject.
- § Facts established by building, item 15: it reads "This is a fourth route
  beyond the three the design names". Name the three instead: `omega`
  discharging an `Iff` goal, `DecidableEq (Fin n → Bool)` resolving through
  `Fintype.decidablePiFintype`, and `RankedAlphabet.Scan` deriving no
  `DecidableEq`. This document survives the segment, so it may not be left
  naming a document the segment deletes — the same defect task 6 step 3 fixes
  in `TODO.md`.

Rename the § B3 heading to `B3: the fold (done)`, the form the B2 and B6
headings already carry.

After this step, no paragraph of § B3 asserts anything the segment has
falsified. That matters because the workstream handoff stays in the working
tree for B4 and B5:
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape is what forbids an
active branch presenting superseded decisions as current.

- [ ] **Step 2: update the workstream handoff's status**

In § Where the workstream stands and § What completion means, record B3 as
done and the remaining items as B4 then B5. Add to § Facts established by
building the seven measurements this segment established, listed in
§ What was compiled before this plan was written above, numbered 17 to 23.
Transfer the measured facts only. Strip what is relative to documents that no
longer exist: item 1's reference to what the design writes, and item 6's
contingency naming a task and step of this plan.
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Document only the persistent is
what forbids a persistent document recording which task of a plan produced
something.

In the same document, § What completion means says the open 73-character
subject belongs to a commit of the previous segment. It is `5cfd5ef1`, of the
case-combinator segment; and once this segment lands, a phrase reading "the
previous segment" names this one. Name the commit instead.

That section opens "Each of these cost a failed build: items 1 to 11 during
B1, items 12 to 16 during segment 2." Extend that sentence to cover the new
items, and narrow its claim while doing so: not all seven cost a failed build,
several having been measured rather than hit.

- [ ] **Step 3: replace the session handoff**

Rewrite `2026-08-10-tree-recognizer-session-handoff.md` for the next session:
the per-item table with B3 done, the line's shape with this segment's
bookmark `feat/cobham-fold` as its last row, what this segment delivered, and
B4 as what to pick up next. Name that bookmark rather than giving it a commit
identifier: step 8 sets it, and the identifier does not exist while this step
runs. Re-derive the other identifiers in the diagram from `jj bookmark list`
and `jj log -r main`; all four in the diagram being replaced are stale —
`main` has moved, and each bookmark has advanced since.

B4 has no specification, so the next session's first phase is brainstorming,
not planning — say so explicitly.

Keep the heading § Status of every roadmap item under that name: the
workstream handoff's § Where the workstream stands refers to the per-item
table in the session handoff under that heading, and
`scripts/check-md-links.sh` does not check fragments, so a rename would go
undetected.

This document names the design in ten places, not all of them links: § Read
these first, § Which document owns what (twice, once as "Two handoffs and one
design sit in this tree"), § Status of every roadmap item (its preamble on the
roadmap letters, and the "Design § Segment 2" and "Design § Segment 3" cells
of the table), § What to pick up next (three times, one of them inside a
quoted `TODO.md` sentence), and § Loose ends ("The design document is carried
to segment 3 and removed there"). None may survive the
rewrite. The table cells and the § Status preamble are the ones a rewrite
preserves by default, this step having ordered § Status kept under its name,
so check them explicitly. § Which document owns what describes a three-document
arrangement that this task reduces to two, so that section is rewritten rather
than having its links alone removed.

- [ ] **Step 4: delete the design and this plan**

```bash
rm docs/superpowers/specs/2026-08-10-cobham-cases-fold-ranked-design.md \
  docs/superpowers/plans/2026-08-10-cobham-fold-segment.md
```

As in task 5 step 7, `rm` is the whole operation; `jj` snapshots the working
copy at the start of every command.

- [ ] **Step 5: confirm no link to a deleted file survives**

Run:

```bash
grep -rn 'cobham-cases-fold-ranked-design\|2026-08-10-cobham-fold-segment' docs/
doctoc --update-only .
markdownlint-cli2 '**/*.md'
scripts/check-md-links.sh
```

Expected: the grep matches nothing and so exits non-zero, and the three
checks are clean. The grep
is run here rather than in step 1 because this plan and the design are
themselves among the files carrying such links, and both exist until step 4.

`doctoc` is not optional: steps 1 and 3 rewrite documents whose tables of
contents are doctoc-managed — step 1 renames a heading in the workstream
handoff, step 3 replaces the session handoff — and `scripts/pre-push.sh` runs
`doctoc --dryrun --update-only .` and exits non-zero if any existing table of
contents would change.

- [ ] **Step 6: run the full pre-push checklist**

Run: `scripts/pre-push.sh`

Expected: passes. It runs, among other things, `lake build`, `lake test`,
`lake lint`, `lake lint -- GebTests`, `scripts/lint-imports.sh`,
`lake shake`, the `scripts/tests/*.sh` self-tests, `check-commit-msg.sh`, and
the Markdown, table-of-contents and link checks. The one known open WARN is a
73-character commit subject on `5cfd5ef1`, a commit of the case-combinator
segment rather than of the segment before this one; it is non-blocking and is
not this segment's to fix.

- [ ] **Step 7: commit**

```bash
jj commit -m "doc(cobham): remove the transient design and hand off"
```

- [ ] **Step 8: set the segment's bookmark**

The line carries a bookmark at each segment boundary, so that `jj` pushes each
segment as its own pull request and the segments stay separately submittable
while the commits stay in one chain. The line's existing bookmarks, in order,
are `feat/ranked-tree-recognizers`, `feat/cobham-scanner`, `feat/cobham-cases`
and `feat/cobham-ranked-tree`; this segment's is `feat/cobham-fold`.

```bash
jj bookmark set feat/cobham-fold -r @-
jj bookmark list
```

It is set here, after the segment's final commit, and not earlier. Bookmarks
do not follow new commits in this repository —
`experimental-advance-branches.enabled-branches` is empty — so a bookmark set
before step 7 would omit the commit removing the design and this plan, and
pushing it would ship those transient documents in the branch's working tree,
against [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape. The
precedent is `feat/cobham-ranked-tree`, which sits at the previous segment's
plan-removal commit rather than at its last `feat`.

---

## Whole-segment review

A task-scoped review cannot see a module-scoped defect: in the case-combinator
segment every per-task review came back clean and the whole-segment review
then found two docstrings asserting the opposite of what their proofs did
(`d9b5c5cf`), and a pair of tests that opened with a rewrite replacing the
construction under test (`e2520a5a`).

It runs in three parts, because its subjects become checkable at three
different points. The code and its persistent documentation are final after
task 6. The transient documents are not disposed of until task 7 step 4, and
until then they still describe B3 as unbuilt, which is task 7's own subject
rather than a defect to report. The segment's last commit message and its
bookmark do not exist until task 7 step 8, so the check that reads them, and
the handoff to the user, come after that.

### Part A: after task 6, before task 7

A fix arising here belongs to the segment's implementation, so it is committed
as its own `feat`, `fix` or `doc` commit before task 7 begins — after task 7
step 4 the same fix would land in the commit that removes the design and this
plan, mixing [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape's
stage 2 with its stage 3.

- [ ] Every docstring asserts what its declaration proves. Read the docstring
      against the proof, not against the statement's name.
- [ ] No test opens with a rewrite that replaces the construction under test
      before anything computes.
- [ ] `docs/index.md` and `TODO.md` describe the module as it is, not as this
      plan proposed it.
- [ ] Every declaration measures within `{propext, Quot.sound}`, from
      `lake lint` rather than from inspection. Containment, not equality: a
      declaration needing neither axiom measures fewer.

### Part B: inside task 7, after step 5 and before step 6

These two checks have no subject until the transient documents are gone and
the handoffs rewritten, and a fix arising here is a documentation fix inside
the documentation commit task 7 is already making.

- [ ] No document in the working tree links to a file this segment deleted.
- [ ] No document in the working tree describes this module as unbuilt, names
      a declaration it does not carry, or states a design decision it took the
      other way. Checking the links alone is not enough: a stale assertion
      beside a removed link survives the link check silently.

### After task 7 step 8

- [ ] Run `scripts/pre-push.sh` once more, with the segment's commits and its
      bookmark in place, so that the commit-message check sees them.
- [ ] Hand the diff to the user. Do not push:
      [AGENTS.md](../../../AGENTS.md) § No `jj git push` without user
      line-by-line review binds this segment, first creation included.
