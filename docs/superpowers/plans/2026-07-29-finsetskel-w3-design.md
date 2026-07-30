# W3: the FinSetSkel topos structure other than coequalizers — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** rows a, b, c, d, e, g, h, l and m of `TODO.md`
§ FinSetSkel as an elementary topos — the initial and terminal
objects, binary coproducts and products, finite coproducts,
exponentials, binary equalizers, the subobject classifier, and the
characterisation of monomorphisms — over `FinSetSkel`, with the data
terms exported under the stable names W5 assembles the
`ElementaryTopos FinSetSkel` instance from.

**Architecture:** eleven content modules in dependency order. Two
arithmetic modules rebuilding `Fin`'s product and exponential
encodings choice-free; five choice-free modules stating each row's
construction and the content of its universal property over vectors
and `Fin`; and four wrapper modules packaging those as mathlib
structures. Only the four wrappers reach
`GebMeta.classicalAllowedModules`.

**Tech stack:** Lean 4 (`v4.33.0-rc1`), mathlib pinned at the same
`rev`, `lake`, `jj`.

**The spec is the specification.**
`docs/superpowers/specs/2026-07-29-finsetskel-w3-design.md` records
which routes are choice-free, which are not, and why several
non-obvious choices are forced. Read the section named at the head of
each task before starting that task. Where this plan and the spec
disagree, the spec is authoritative and the disagreement is a defect
in this plan.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [File structure](#file-structure)
- [Namespaces](#namespaces)
- [Verification commands](#verification-commands)
- [Task 1: `Equiv.arrowCongrLeftC` on the shared branch](#task-1-equivarrowcongrleftc-on-the-shared-branch)
- [Task 2: the three choice-free `Fin` operations](#task-2-the-three-choice-free-fin-operations)
- [Task 3: the choice-free product equivalence](#task-3-the-choice-free-product-equivalence)
- [Task 4: the choice-free exponential encoding](#task-4-the-choice-free-exponential-encoding)
- [Task 5: the shapes core — the index correspondence, points, rows a and b](#task-5-the-shapes-core--the-index-correspondence-points-rows-a-and-b)
- [Task 6: row c — binary coproducts, core](#task-6-row-c--binary-coproducts-core)
- [Task 7: row d — binary products, core](#task-7-row-d--binary-products-core)
- [Task 8: the cartesian wrapper](#task-8-the-cartesian-wrapper)
- [Task 9: the coproduct wrapper and finite coproducts](#task-9-the-coproduct-wrapper-and-finite-coproducts)
- [Task 10: row m — monomorphisms are injective vectors](#task-10-row-m--monomorphisms-are-injective-vectors)
- [Task 11: row g's core — the exponential equivalence and its naturality](#task-11-row-gs-core--the-exponential-equivalence-and-its-naturality)
- [Task 12: the whiskering bridge](#task-12-the-whiskering-bridge)
- [Task 13: the monoidal-closed structure](#task-13-the-monoidal-closed-structure)
- [Task 14: row h's data path and its two fold lemmas](#task-14-row-hs-data-path-and-its-two-fold-lemmas)
- [Task 15: row h's universal property](#task-15-row-hs-universal-property)
- [Task 16: the equalizer wrapper](#task-16-the-equalizer-wrapper)
- [Task 17: row l's core — the characteristic vector and the inversion](#task-17-row-ls-core--the-characteristic-vector-and-the-inversion)
- [Task 18: the classifier wrapper](#task-18-the-classifier-wrapper)
- [Task 19: documentation and `TODO.md`](#task-19-documentation-and-todomd)
- [Task 20: remove the spec and the plan](#task-20-remove-the-spec-and-the-plan)
- [Self-review record](#self-review-record)

<!-- END doctoc -->

---

## Global constraints

Every task's requirements implicitly include this section.

- **No `noncomputable` anywhere.** No `native_decide`:
  `GebMeta.detectNonstandardAxiom` forbids `Lean.ofReduceBool`
  everywhere.
- **Choice-free except the four wrappers.** Every declaration outside
  `Shapes/Instances.lean`, `Exponential/Closed.lean`,
  `Equalizer/Limits.lean` and `Classifier/Instance.lean` depends on
  `propext` and `Quot.sound` only. Those four source modules and
  their four `GebTests` parallels are the only names added to
  `GebMeta.classicalAllowedModules`, and no core module is added.
- **Axioms are measured from a monomorphic `def`.** `#print axioms`
  on a polymorphic constant measures the constant, not any
  instantiation: instance and functor arguments are not part of what
  it reports. Every axiom check below therefore fixes the type
  variables and elaborates a `def` at the instances actually used,
  per the spec's § How axioms are measured. A measurement of a
  library constant in isolation never establishes that a declaration
  applying it is clean.
- **Each construction is measured whole.** Measuring its named
  ingredients is not sufficient: the combinator introducing an axiom
  may be one the construction was never described as using.
- **Constraint 9's banned forms are a separate gate.** `Vector.ofFn`,
  `Vector.range`, `Vector.finRange` and the
  `Array.toList_ofFn` / `List.toArray_ofFn` bridges measure clean —
  what is banned is their `@[simp]` lemmas — so `#print axioms` does
  not catch a violation. Grep for the banned names in every task that
  touches a choice-free module:

  ```bash
  grep -n "Vector\.ofFn\b\|Vector\.range\|Vector\.finRange\|toList_ofFn\|toArray_ofFn" <file>
  ```

  Expected: no match. `Vector.ofFnC` is the permitted form.
- **No `induction` tactic, no self-recursive `def`, no
  `termination_by`.** Every recursion is an explicit recursor
  application (`Nat.rec`, `List.rec`), per
  `docs/rules/lean-coding.md` § Recursion and induction through
  recursors. `cases` and `rcases` are permitted for non-recursive
  case analysis.
- **Deciding a proposition quantified over `Fin n`** uses
  `inferInstance`, never `Fintype.decidableForallFintype`, which
  inhabits the same class and depends on `Classical.choice`
  (constraint 9). Equality at `Fin n` is decided through the
  axiom-free `DecidableEq (Fin n)`; W3 needs no `LawfulBEq (Fin n)`
  and supplies none.
- **Module preamble.** Copyright block
  (`Copyright (c) 2026 Terence Rokop. All rights reserved.`, the
  Apache-2.0 line, `Authors: Terence Rokop`), then `module`, then the
  imports, then the `/-! … -/` module docstring, then
  `@[expose] public section`.
- **Import visibility.** Imports whose contents appear in a module's
  own statements are `public import`; source index files use
  `public import`, `GebTests` index files use plain `import`.
- **`autoImplicit = false`.** Every binder is declared. Universe
  variables are declared with `universe`.
- **Line length 100 characters** in `.lean` files; 80 in `.md` prose
  (`MD013`, tables and code blocks exempt).
- **`weak.warningAsError = true`.** A linter warning fails the build.
  In particular `linter.style.show` rejects a goal-changing `show`
  (use `change`), and `dupNamespace` rejects a declaration whose own
  name repeats its enclosing namespace.
- **`simpa … using t` fails when `simp` alone would close the goal.**
  `linter.unnecessarySimpa` reports it, and the bullet above turns
  that into a build failure. This bites wherever the `using` term is a
  library lemma the default simp set already applies — measured at
  this toolchain for both `List.getElem_mem` sites in Tasks 14 and 17.
  The test is the linter's, not a rule about what kind of term `t` may
  be: use `simpa` only when plain `simp` does not close the goal
  without `t`. Try `simp` first and keep whichever form the linter
  accepts.
- **Docstrings are mandatory** for every `def`, `instance`,
  `structure` field and theorem of every module this plan creates,
  and a `/-! … -/` module docstring with the sections
  `docs/rules/lean-coding.md` § Documentation makes mandatory heads
  each file. No development-history references in any docstring, and
  no post-hoc axiom-freeness celebration.
- **No self-prefix leakage.** `Geb.Mathlib.` and `GebTests.Mathlib.`
  appear only in `^import` lines, never in a namespace, a declaration
  body, a docstring or a comment.
- **Every new name is confirmed free under the importing module's own
  import set**, by `#check @Name` in that module, not in a probe. A
  probe sees only its own imports.
- **Every mathlib name a step applies is confirmed by `#check @Name`
  in the consuming module before it is relied on**, per verification
  obligation 5. The signatures recorded in this plan are a starting
  point, not evidence: they were taken at the revision current when
  the plan was written, and a bump between then and execution surfaces
  as an elaboration failure inside a proof rather than at a
  confirmation step. This bullet binds every task; the individual
  "confirm with `#check`" instructions below are reminders at the
  places most likely to bite, not the whole of the obligation.
- **The topos rows are a transcription and their modules cite it.**
  Every module stating a row of the operation table or its universal
  property carries a `## References` section listing `[Freyd1972]`,
  which `docs/references.bib` already holds (added by W2) and which
  `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` already cites.
  That covers `Shapes/Core.lean`, `Shapes/Instances.lean`,
  `Exponential/Core.lean`, `Exponential/Closed.lean`,
  `Equalizer/Core.lean`, `Equalizer/Limits.lean`, `Mono.lean`,
  `Classifier/Core.lean` and `Classifier/Instance.lean`. The two
  arithmetic modules carry none: `Fin m × Fin n ≃ Fin (m * n)` and
  `(Fin m → Fin n) ≃ Fin (n ^ m)` are standard and mathlib states
  both, and a choice-free proof of a classical statement is a change
  of proof, not of theorem. **`docs/references.bib` gains no entry**,
  per the spec's § Transcription and novelty; a task that adds one is
  wrong. Nothing cites a textbook locator for the subobject
  classifier beyond `[Freyd1972]`: the standing obligation on the
  skeleton locator applies, and the default is to add nothing.
- **Test parallels name a `def` value** built from the module under
  test rather than using `example` alone: `lake shake` cannot see an
  import used only inside an `example`, since no constant reaches the
  olean, and reports a false "remove import" with exit 1. Index
  parallels are import-only, and a wrapper module's parallel may be
  created declaration- and import-free when the task supplying its
  first `def` is a later one — an import reached by no constant is
  what `lake shake` reports as removable.
- **A core module's test parallel is also its permanent axiom
  witness.** The named `def` the bullet above requires is monomorphic
  and built from the module, which is exactly what an axiom
  measurement needs, so it doubles as the witness a later task
  re-measures. Scratch witnesses declared *inside* a `Geb/` source
  module are deleted after measuring, per the no-scratch-module rule
  below; the test parallel's named declarations are not. A later task
  told to "re-measure module M's witness" measures the declaration
  named in M's `GebTests` parallel, which is in the tree and which
  that task's own step names. This also puts every core module's
  axiom set under `lake lint -- GebTests` continuously, since a core
  module's test parallel is not allowlisted.
- **VCS is `jj`.** No mutating `git` subcommand; the PreToolUse hook
  at `scripts/hooks/block-mutating-git.sh` blocks them.
- **Commit messages**: `<type>(<scope>): <subject>`, type in
  `feat | fix | doc | style | refactor | test | chore | perf | ci`,
  imperative present tense, no capital, no trailing period, subject
  under 72 characters.
- **This plan and the spec are not edited during execution.** Step
  state is tracked outside the tree — in the orchestrator's task list,
  not by ticking the `- [ ]` boxes in this file. `jj commit` takes the
  whole working copy, so a plan-file diff would land inside whichever
  task's commit came next, messaged `feat(fin): …` or similar. The
  checkbox syntax is for reading, not for writing.
- **Every commit step is preceded by `jj st`**, confirming that the
  modified files are exactly the ones that task's Files block names.
  A stray file in the list means the previous task left something
  uncommitted, or something outside this task's scope was touched;
  stop and report rather than committing it. This is the same
  discipline Task 19 Step 1's ordering exists to enforce, applied to
  every task.
- **The commit idiom is two commands, and the second is not
  optional.** `jj commit -m "…"` describes the *current* working-copy
  commit and opens a new empty one; it does not create a commit
  beside the existing one. So every task ends with

  ```bash
  jj commit -m "<message>"
  jj bookmark set feat/finsetskel-w3 -r @-
  ```

  and the bookmark move is written out in each task's commit step.
  Bookmark auto-advance is contributor-local configuration that
  `CONTRIBUTING.md` § Setup only recommends, so a workspace without
  it would otherwise leave `feat/finsetskel-w3` pointing at the plan
  commit after all twenty tasks, and the branch the user reviews
  would be empty of the work.
- **Never `jj edit` a described commit you intend to add work
  beside.** `jj edit <bookmark>` makes that commit the working copy,
  and the next `jj commit` then overwrites its message and squashes
  the new changes into it, destroying a reviewed commit. Use
  `jj new <bookmark>` to start a child.
- **Where a step says "report", the report goes to the orchestrator,
  not into the tree.** A subagent executing one task cannot reach the
  user and has not read the other tasks. The orchestrator records
  each answer and includes it verbatim in the brief of any task the
  step names.
- **Module import lists below are a starting point**, not
  `lake shake`'s output. The pre-push `lake shake` settles the
  minimal set; adjust to whatever it reports and re-run.
- **No scratch or probe module is left under `Geb/` or `GebTests/`**;
  both are lake-globbed source roots. Use the `lean-lsp` MCP's
  `lean_run_code` for standalone probes.

## File structure

Created, in dependency order:

| File | Responsibility | Layer |
| --- | --- | --- |
| `Geb/Mathlib/Data/Fin/Basic.lean` | `Fin.divNatC`, `Fin.modNatC`, `Fin.pairC` and their three round trips. Core- rather than mathlib-targeted. | choice-free |
| `Geb/Mathlib/Data/Fin.lean` | directory index | — |
| `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean` | `finProdFinEquivC`, `finFunctionFinEquivC`, `Fin.funEncodeC`, `Fin.funDecodeC` | choice-free |
| `Geb/Mathlib/Logic/Equiv/Fin.lean` | directory index | — |
| `…/FinSetSkel/Shapes/Core.lean` | rows a, b, c, d over `Fin` and vectors; `homEquivIdxFun`; `point` | choice-free |
| `…/FinSetSkel/Shapes/Instances.lean` | rows a, b, c, d, e as mathlib cones, the cartesian instance, `isTerminalOne` | wrapper |
| `…/FinSetSkel/Shapes.lean` | directory index | — |
| `…/FinSetSkel/Mono.lean` | row m | choice-free |
| `…/FinSetSkel/Exponential/Core.lean` | row g's carrier-level equivalence and its naturality | choice-free |
| `…/FinSetSkel/Exponential/Closed.lean` | the whiskering bridge, `Closed`, `MonoidalClosed` | wrapper |
| `…/FinSetSkel/Exponential.lean` | directory index | — |
| `…/FinSetSkel/Equalizer/Core.lean` | row h's data path, its two fold lemmas, the universal property | choice-free |
| `…/FinSetSkel/Equalizer/Limits.lean` | `LimitCone (parallelPair f g)` | wrapper |
| `…/FinSetSkel/Equalizer.lean` | directory index | — |
| `…/FinSetSkel/Classifier/Core.lean` | row l's characteristic vector, pullback lift and vector-level uniqueness | choice-free |
| `…/FinSetSkel/Classifier/Instance.lean` | `Subobject.Classifier FinSetSkel` | wrapper |
| `…/FinSetSkel/Classifier.lean` | directory index | — |

`…/` abbreviates `Geb/Mathlib/CategoryTheory/`. A `GebTests/Mathlib/`
parallel mirrors each of the seventeen paths.

Modified:

| File | Change |
| --- | --- |
| `Geb/Mathlib/Logic/Equiv/Basic.lean` | `Equiv.arrowCongrLeftC` (Task 1, on `feat/choice-free-primitives`) |
| `GebTests/Mathlib/Logic/Equiv/Basic.lean` | its round-trip test (Task 1, same branch) |
| `Geb/Mathlib/Data.lean`, `GebTests/Mathlib/Data.lean` | one import each |
| `Geb/Mathlib/Logic/Equiv.lean`, `GebTests/Mathlib/Logic/Equiv.lean` | one import each |
| `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` | five imports each |
| `GebMeta.lean` | eight names appended to `classicalAllowedModules` |
| `docs/index.md` | one entry per new content module (Task 19); separately, Task 1 extends the existing `Logic/Equiv/Basic.lean` entry on `feat/choice-free-primitives` |
| `TODO.md` | amendments 2 through 8 of the spec's § Amendments |

## Namespaces

Fixed here, because a name that moves between tasks is the defect
rounds 3 through 8 of the spec review kept finding.

| Module | Namespace |
| --- | --- |
| `Data/Fin/Basic.lean` | `Fin` |
| `Logic/Equiv/Fin/Basic.lean` | root for the two `Equiv`s, `Fin` for `funEncodeC` / `funDecodeC` |
| `Shapes/Core.lean`, `Shapes/Instances.lean` | `FinSetSkel` |
| `Mono.lean` | `FinSetSkel` |
| `Exponential/Core.lean`, `Exponential/Closed.lean` | `FinSetSkel` |
| `Equalizer/Core.lean` | `FinSetSkel.Equalizer` |
| `Equalizer/Limits.lean` | `FinSetSkel` |
| `Classifier/Core.lean` | `FinSetSkel.Classifier` |
| `Classifier/Instance.lean` | `FinSetSkel` |

The two sub-namespaces track their modules, as W4's
`FinSetSkel.Quotient` does, and keep generic names (`agree`, `lift`,
`chi`) out of `FinSetSkel`, where W4 and W5 also declare.

`FinSetSkel.Classifier` shadows mathlib's `Subobject.Classifier` for
`open`: inside `namespace FinSetSkel`, a bare `Classifier` resolves to
ours. `Classifier/Instance.lean` therefore writes
`Subobject.Classifier FinSetSkel` qualified and does not
`open Subobject`. Resolution of the qualified form is unambiguous —
`FinSetSkel.Subobject.Classifier` does not exist, so the root name is
found.

## Verification commands

Referenced by name from the steps below.

- `lake build` — compiles `Geb` (the default target).
- `lake build GebTests` — compiles the test library.
- `lake test` — runs the test driver.
- `lake lint` — runs `GebMeta.detectNonstandardAxiom` and the
  environment linters over `Geb`; `lake lint -- GebTests` over
  `GebTests`.
- **Axiom check**: the `lean-lsp` MCP's `lean_verify` at the fully
  qualified name, or `#print axioms` through the same MCP, always at
  a monomorphic `def`. `lake env lean` is forbidden by
  `docs/rules/lean-coding.md` § Lake / build workflow, and
  `lake clean` forces a full mathlib rebuild.
- `bash scripts/lint-imports.sh` — the subtree import rules.
- `bash scripts/pre-push.sh` — the full checklist.
- `markdownlint-cli2 '**/*.md'` — before each commit touching
  Markdown.
- `doctoc --update-only .` — regenerates in-place TOCs; run before
  each commit touching a Markdown file that carries doctoc markers
  and whose headings changed.

In a fresh worktree run `lake exe cache get` before the first
`lake build`.

---

## Task 1: `Equiv.arrowCongrLeftC` on the shared branch

Spec sections: § `Equiv`'s domain transport is choice-tainted,
§ Shared declarations.

This task is **not** on `feat/finsetskel-w3`. It completes
`feat/choice-free-primitives`, which currently carries the
constraint-9 amendment alone, and W3 then rebases onto it.

**Files:**

- Modify: `Geb/Mathlib/Logic/Equiv/Basic.lean`
- Modify: `GebTests/Mathlib/Logic/Equiv/Basic.lean`
- Modify: `docs/index.md`

**Interfaces:**

- Consumes: `Equiv`, `funext`, `congrArg`.
- Produces: `Equiv.arrowCongrLeftC.{u, v, w} {α : Sort u}
  {β : Sort v} {γ : Sort w} (e : α ≃ β) : (α → γ) ≃ (β → γ)`.
  Consumed by Tasks 5 (`homEquivIdxFun`) and 11 (row g's first step).

W4 does not consume it: W4's spec § Out of scope records that no
`Equiv` of W4's is an equivalence between arrow types, so the
"consumed by both" ground for placing it here has lapsed. It stays
here anyway — the branch exists for the constraint-9 amendment, which
W4 does depend on, the module is one W4 never touches, and moving the
declaration to W3's branch would change three sections of a
user-approved spec for no gain. Report the discrepancy with the
spec's § Shared declarations to the orchestrator; do not act on it
further.

- [ ] **Step 1: start a child of the shared branch**

```bash
jj st
jj new feat/choice-free-primitives
```

`jj st` **before** `jj new`, not after: after `jj new` the working copy
is empty by construction, so the check would be vacuous. What it
guards against is uncommitted work stranded on the previous
working-copy commit. If it reports modifications, stop and report;
they belong to whatever produced them.

`jj new`, not `jj edit`: the bookmarked commit carries the reviewed
constraint-9 amendment, and editing it would make the Step 6
`jj commit` overwrite its message and squash this task's work into
it. Confirm with `jj log` that the parent is
`doc(elementary-topos): record three choice-taint families in
constraint 9` and with `jj st` that the working copy is empty.

- [ ] **Step 2: add the declaration**

Append to `Geb/Mathlib/Logic/Equiv/Basic.lean`, inside the existing
`@[expose] public section`, after `arrowSumEquivSigma`. The file
already declares `universe u v`; add `w`.

```lean
/-- Transport a function type along an equivalence of its domain,
choice-free (unlike `Equiv.arrowCongr` and the `Equiv.piCongrLeft`
family, each of which depends on `Classical.choice`). The three
sorts are independent, matching the polymorphism of the
`Equiv.arrowCongr` this replaces. -/
def Equiv.arrowCongrLeftC {α : Sort u} {β : Sort v} {γ : Sort w}
    (e : α ≃ β) : (α → γ) ≃ (β → γ) where
  toFun g := g ∘ e.symm
  invFun h := h ∘ e
  left_inv g := funext fun a ↦ congrArg g (e.left_inv a)
  right_inv h := funext fun b ↦ congrArg h (e.right_inv b)
```

Add `arrowCongrLeftC` to the module docstring's
`## Main definitions` list and `arrow, domain transport` to its
`## Tags` line, and widen the docstring's opening summary to mention
the domain transport. The declaration is written with the explicit
`Equiv.` prefix rather than inside a `namespace Equiv` block, the
file having no namespace block.

At least two independent levels are required: the other use,
`homEquivIdxFun` in Task 5, applies it at
`α = ULift.{u} (Fin X.len) : Type u` and `β = Fin X.len : Type 0`.
The third is taken under `docs/rules/lean-coding.md` § Structure and
typeclass patterns.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: check the axioms**

The declaration is universe-polymorphic but takes no instance
argument, so the constant's own measurement is the measurement. Take
it anyway at the fully qualified name.

Expected: `[Quot.sound]`.

- [ ] **Step 4: add the test**

Append to `GebTests/Mathlib/Logic/Equiv/Basic.lean`:

```lean
/-- A non-identity self-equivalence of `Bool`, to transport along. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- A sample function whose domain the transport rewrites. -/
def sampleArrowCongrLeft : Bool → Nat :=
  Equiv.arrowCongrLeftC boolNotEquiv (fun b ↦ if b then 1 else 0)

/-- The domain transport round-trips a sample function pointwise. -/
theorem sampleArrowCongrLeftC_roundtrip (b : Bool) :
    (Equiv.arrowCongrLeftC (γ := Nat) boolNotEquiv).symm
        ((Equiv.arrowCongrLeftC (γ := Nat) boolNotEquiv)
          sampleArrowCongrLeft) b =
      sampleArrowCongrLeft b :=
  congrFun
    ((Equiv.arrowCongrLeftC (γ := Nat) boolNotEquiv).symm_apply_apply
      sampleArrowCongrLeft) b
```

The equivalence is built here rather than taken from mathlib, and it
is deliberately **not** `Equiv.refl Bool`: transporting along the
identity would leave the round-trip theorem exercising only
`symm_apply_apply` at the identity, which is no test of the
declaration. `Bool.not_not` is core's `!!b = b`; `#check` it in the
test module before relying on it.

Run: `lake build GebTests` then `lake test`
Expected: PASS.

- [ ] **Step 5: extend the `docs/index.md` entry**

`Geb/Mathlib/Logic/Equiv/Basic.lean` already has an entry near line
42. Add the domain transport to its description; do not add a second
entry for the same module.

Run: `markdownlint-cli2 '**/*.md'`
Expected: PASS.

- [ ] **Step 6: verify and commit**

Run: `bash scripts/lint-imports.sh`, `lake build`, `lake test`,
`lake lint`, `lake lint -- GebTests`, `bash scripts/pre-push.sh`
Expected: PASS.

```bash
jj commit -m "feat(equiv): add a choice-free domain transport for arrow types"
jj bookmark set feat/choice-free-primitives -r @-
```

The bookmark move is this task's, and it moves
`feat/choice-free-primitives` rather than `feat/finsetskel-w3`: this
commit belongs to the shared branch. Confirm with `jj log` that the
bookmark now names the new commit.

- [ ] **Step 7: rebase W3 onto the shared branch**

```bash
jj rebase -b feat/finsetskel-w3 -d feat/choice-free-primitives
jj new feat/finsetskel-w3
```

`jj new`, not `jj edit`: `feat/finsetskel-w3` names the commit
carrying this plan, and editing it would make Task 2's `jj commit`
overwrite that commit's message and bundle the plan document into
Task 2's change.

Confirm with `jj log` that `feat/finsetskel-w3` is now a descendant
of `feat/choice-free-primitives` and with `lake build` that the tree
compiles. Every later task is on `feat/finsetskel-w3`.

The shared branch remains its own PR candidate. Nothing is pushed
without the user's line-by-line review
(`AGENTS.md` § No `jj git push` without user line-by-line review).

---

## Task 2: the three choice-free `Fin` operations

Spec sections: § A choice-free product equivalence exists, § The
`Nat` division and order API is choice-taint-interleaved, § Module
layout, § Documentation.

**Files:**

- Create: `Geb/Mathlib/Data/Fin/Basic.lean`
- Create: `Geb/Mathlib/Data/Fin.lean`
- Create: `GebTests/Mathlib/Data/Fin/Basic.lean`
- Create: `GebTests/Mathlib/Data/Fin.lean`
- Modify: `Geb/Mathlib/Data.lean`, `GebTests/Mathlib/Data.lean`

**Interfaces:**

- Consumes: `Nat.lt_or_ge`, `Nat.div_mul_le_self`,
  `Nat.lt_of_le_of_lt`, `Nat.mul_le_mul_right`, `Nat.mod_lt`,
  `Nat.eq_zero_or_pos`, `Nat.add_mul`, `Nat.one_mul`, `Nat.add_comm`,
  `Nat.add_mul_div_right`, `Nat.div_eq_of_lt`, `Nat.zero_add`,
  `Nat.add_mul_mod_self_right`, `Nat.mod_eq_of_lt`,
  `Nat.div_add_mod'`, `Fin.ext`, `omega`.
- Produces, in namespace `Fin`: `divNatC`, `modNatC`, `pairC`,
  `divNatC_pairC`, `modNatC_pairC`, `pairC_divNatC_modNatC`. The last
  three carry `@[simp]`. Consumed by Task 3 (`finProdFinEquivC`),
  Task 7 (row d) and Tasks 11 and 12 (row g's naturality and the
  whiskering bridge, which state the pairing on indices directly).

`Nat.div_lt_of_lt_mul` and `Nat.lt_of_mul_lt_mul_left` are
`Classical.choice`-dependent and must not appear; the lemmas listed
above are the `propext`-only or axiom-free neighbours the spec
measured. Neither the name nor the namespace separates the two sets,
so a lemma not on this list is measured before use.

- [ ] **Step 1: create the module with its preamble and docstring**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Choice-free division, remainder and pairing on `Fin`

`Fin.divNat` and `Fin.modNat` are Lean core declarations whose bound
proofs run through `Nat.div_lt_of_lt_mul`, which depends on
`Classical.choice`. The three operations here are their choice-free
counterparts, together with the round trips exhibiting them as a
bijection `Fin m × Fin n ≃ Fin (m * n)`.

`Nat`'s division and order API interleaves choice-dependent lemmas
with choice-free ones under no separating convention of name or
namespace: `Nat.div_lt_of_lt_mul` and `Nat.lt_of_mul_lt_mul_left`
depend on `Classical.choice` while `Nat.div_mul_le_self`,
`Nat.add_mul_div_right` and `Nat.div_add_mod'` do not. The bound
proofs below therefore route through `omega` over hypotheses named
individually, or through case analysis on `Nat.lt_or_ge`, rather than
through whichever lemma states the bound directly.

The upstream target of this module is Lean core rather than mathlib4,
`Fin.divNat` and `Fin.modNat` being core declarations; where such
content belongs is `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

## Main definitions

* `Fin.divNatC`, `Fin.modNatC` — the quotient and remainder of an
  index of `Fin (m * n)`.
* `Fin.pairC` — the index of `Fin (m * n)` with given quotient and
  remainder.

## Main statements

* `Fin.divNatC_pairC`, `Fin.modNatC_pairC`,
  `Fin.pairC_divNatC_modNatC` — the three round trips.

## Tags

fin, division, remainder, pairing, choice-free
-/

@[expose] public section

namespace Fin

end Fin
```

- [ ] **Step 2: confirm the six names are free**

Inside the namespace block, temporarily:

```lean
#check @Fin.divNatC
```

Run: `lake build`
Expected: FAIL, "unknown identifier". A success means the name is
taken under this module's own import set and the plan's naming must
change. Repeat for `modNatC`, `pairC`, `divNatC_pairC`,
`modNatC_pairC`, `pairC_divNatC_modNatC`; delete the `#check`s
afterwards.

- [ ] **Step 3: add the three operations**

Inside the namespace block. This text was elaborated at this
toolchain and measured `[propext, Quot.sound]`.

```lean
/-- The quotient of an index of `Fin (m * n)` by `n`, choice-free
(unlike `Fin.divNat`). -/
def divNatC {m n : ℕ} (i : Fin (m * n)) : Fin m :=
  ⟨i / n, by
    rcases Nat.lt_or_ge ((i : ℕ) / n) m with h | h
    · exact h
    · have h3 : (i : ℕ) / n * n < m * n :=
        Nat.lt_of_le_of_lt (Nat.div_mul_le_self i n) i.isLt
      have h5 : m * n ≤ (i : ℕ) / n * n := Nat.mul_le_mul_right n h
      omega⟩

/-- The remainder of an index of `Fin (m * n)` modulo `n`,
choice-free (unlike `Fin.modNat`). -/
def modNatC {m n : ℕ} (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (by
    have h := i.isLt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · exact hn)⟩

/-- The index of `Fin (m * n)` with quotient `a` and remainder `b`. -/
def pairC {m n : ℕ} (a : Fin m) (b : Fin n) : Fin (m * n) :=
  ⟨a * n + b, by
    have h1 : ((a : ℕ) + 1) * n ≤ m * n := Nat.mul_le_mul_right n a.isLt
    have h2 : ((a : ℕ) + 1) * n = a * n + n := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := b.isLt
    omega⟩
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add the three round trips**

```lean
/-- The quotient of a pairing is its first component. -/
@[simp] theorem divNatC_pairC {m n : ℕ} (a : Fin m) (b : Fin n) :
    divNatC (pairC a b) = a := by
  apply Fin.ext
  change ((a : ℕ) * n + b) / n = (a : ℕ)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _
      (Nat.lt_of_le_of_lt (Nat.zero_le _) b.isLt),
    Nat.div_eq_of_lt b.isLt, Nat.zero_add]

/-- The remainder of a pairing is its second component. -/
@[simp] theorem modNatC_pairC {m n : ℕ} (a : Fin m) (b : Fin n) :
    modNatC (pairC a b) = b := by
  apply Fin.ext
  change ((a : ℕ) * n + b) % n = (b : ℕ)
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]

/-- Pairing an index's quotient with its remainder recovers it. -/
@[simp] theorem pairC_divNatC_modNatC {m n : ℕ} (i : Fin (m * n)) :
    pairC (divNatC i) (modNatC i) = i := by
  apply Fin.ext
  change (i : ℕ) / n * n + (i : ℕ) % n = (i : ℕ)
  exact Nat.div_add_mod' i n
```

`change` rather than `show`: `linter.style.show` rejects the latter
when it changes the goal, and `weak.warningAsError = true` makes that
fail the build. The positivity side condition of
`Nat.add_mul_div_right` is `0 < n`, supplied from `b.isLt` by
`Nat.lt_of_le_of_lt (Nat.zero_le _) b.isLt`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: check the axioms**

The six declarations are polymorphic in `m` and `n` but take no
instance argument, so the constants' own measurements suffice.
Measure each of the six.

Expected: `[propext, Quot.sound]` throughout. `Classical.choice`
means a choice-dependent `Nat` lemma entered; find it by measuring
each lemma the failing proof names.

Then run the banned-form grep of § Global constraints on the module.
Expected: no match.

- [ ] **Step 6: create the two index files**

`Geb/Mathlib/Data/Fin.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Fin.Basic

/-!
# Fin — index
-/
```

`GebTests/Mathlib/Data/Fin.lean` is the same with
`import GebTests.Mathlib.Data.Fin.Basic` (plain `import`, per
§ Global constraints) and the title `# Fin tests — index`.

Add `public import Geb.Mathlib.Data.Fin` to `Geb/Mathlib/Data.lean`
and `import GebTests.Mathlib.Data.Fin` to `GebTests/Mathlib/Data.lean`,
both in alphabetical position (after `Geb.Mathlib.Data.FinEnum`).

- [ ] **Step 7: write the test parallel**

`GebTests/Mathlib/Data/Fin/Basic.lean`, importing
`Geb.Mathlib.Data.Fin.Basic`. Compositional per
`docs/rules/lean-coding.md` § Structure and typeclass patterns:
calculate one value, assert it, reuse it.

```lean
/-- A sample pairing: quotient `2`, remainder `1`, at `3 * 4`. -/
def samplePair : Fin (3 * 4) := Fin.pairC (2 : Fin 3) (1 : Fin 4)

/-- The sample pairing is the index `9`. -/
theorem samplePair_eq : samplePair = (9 : Fin (3 * 4)) := rfl

/-- The sample pairing's quotient is its first component. -/
theorem samplePair_divNatC : Fin.divNatC samplePair = 2 := rfl

/-- The sample pairing's remainder is its second component. -/
theorem samplePair_modNatC : Fin.modNatC samplePair = 1 := rfl

/-- The three operations round-trip at the sample index. -/
theorem samplePair_roundtrip :
    Fin.pairC (Fin.divNatC samplePair) (Fin.modNatC samplePair) =
      samplePair := rfl
```

`2 * 4 + 1 = 9` is the value `samplePair_eq` asserts; the definitions
reduce, so `rfl` closes each.

Run: `lake build GebTests` then `lake test`
Expected: PASS.

- [ ] **Step 8: verify and commit**

Run: `bash scripts/lint-imports.sh`, `lake build`, `lake test`,
`lake lint`, `lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(fin): add choice-free division, remainder and pairing"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 3: the choice-free product equivalence

Spec sections: § A choice-free product equivalence exists, § Module
layout, § Decisions fixed here (2 and 3).

**Files:**

- Create: `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean`
- Create: `Geb/Mathlib/Logic/Equiv/Fin.lean`
- Create: `GebTests/Mathlib/Logic/Equiv/Fin/Basic.lean`
- Create: `GebTests/Mathlib/Logic/Equiv/Fin.lean`
- Modify: `Geb/Mathlib/Logic/Equiv.lean`,
  `GebTests/Mathlib/Logic/Equiv.lean`

`Geb/Mathlib/Logic.lean` already imports `Geb.Mathlib.Logic.Equiv`
and needs no change.

**Interfaces:**

- Consumes: Task 2's six declarations; `Equiv`, `Prod.ext`.
- Produces: `finProdFinEquivC {m n : ℕ} : Fin m × Fin n ≃ Fin (m * n)`,
  at root, mirroring mathlib's root-level `finProdFinEquiv`. Consumed
  by Task 4 (the arity recursion) and Task 11 (row g's chain).

`finProdFinEquivC` is assembled from Task 2's operations rather than
being primitive: decision 3 makes the named operations the
carrier-level `simp` normal form for the product, with the `@[simp]`
lemmas stated over them.

- [ ] **Step 1: create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Choice-free product and exponential encodings of `Fin`

mathlib's `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` and
`finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` both depend on
`Classical.choice`, the first through `Fin.divNat` and the second
through the `Finset.sum` lemmas its round trips run on. The two
equivalences here are their choice-free counterparts.

The exponential is built by recursion on the arity over the product
encoding rather than by base-`n` digit arithmetic: the digit
construction's round trips are `Finset.sum` lemmas, each a separate
choice audit, and mathlib's version of that construction is the one
that depends on `Classical.choice`. The recursion is an explicit
`Nat.rec` at the motive `fun k ↦ (Fin k → Fin y) ≃ Fin (y ^ k)`, per
`docs/rules/lean-coding.md` § Recursion and induction through
recursors.

## Main definitions

* `finProdFinEquivC` — the product encoding.
* `finFunctionFinEquivC` — the exponential encoding.
* `Fin.funEncodeC`, `Fin.funDecodeC` — its two directions under
  names the `simp` lemmas are stated over.

## Main statements

* `Fin.funDecodeC_funEncodeC`, `Fin.funEncodeC_funDecodeC` — the two
  round trips of the exponential encoding.

## Tags

fin, equiv, product, exponential, choice-free
-/

@[expose] public section
```

Confirm `finProdFinEquivC`, `finFunctionFinEquivC`, `Fin.funEncodeC`,
`Fin.funDecodeC`, `Fin.funDecodeC_funEncodeC` and
`Fin.funEncodeC_funDecodeC` are free under this module's own import
set: `#check @finProdFinEquivC` and so on inside the module, expecting
`lake build` to FAIL with "unknown identifier" for each, then delete
the `#check`s. A success means the name is taken and the plan's naming
must change; report that. A probe file cannot substitute, seeing only
its own imports.

- [ ] **Step 2: add the product equivalence**

```lean
/-- The choice-free product encoding, assembled from `Fin.pairC`,
`Fin.divNatC` and `Fin.modNatC` (unlike mathlib's
`finProdFinEquiv`, which depends on `Classical.choice`). -/
def finProdFinEquivC {m n : ℕ} : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := Fin.pairC p.1 p.2
  invFun i := (Fin.divNatC i, Fin.modNatC i)
  left_inv p := Prod.ext (Fin.divNatC_pairC p.1 p.2) (Fin.modNatC_pairC p.1 p.2)
  right_inv i := Fin.pairC_divNatC_modNatC i
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: check the axioms**

Measure `finProdFinEquivC`, and additionally a monomorphic witness,
since the constant is polymorphic:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probePair : Fin (3 * 4) := finProdFinEquivC ((2 : Fin 3), (1 : Fin 4))
```

Expected: `[propext, Quot.sound]` for both. Delete `probePair` after
measuring — Task 3 Step 5's test carries the persistent form.

Then run the banned-form grep on the module. Expected: no match.

- [ ] **Step 4: create the two index files and wire them**

`Geb/Mathlib/Logic/Equiv/Fin.lean` and
`GebTests/Mathlib/Logic/Equiv/Fin.lean`, on the pattern of Task 2
Step 6, titled `# Equiv Fin — index` and
`# Equiv Fin tests — index`. Add
`public import Geb.Mathlib.Logic.Equiv.Fin` to
`Geb/Mathlib/Logic/Equiv.lean` and the plain-`import` parallel to
`GebTests/Mathlib/Logic/Equiv.lean`.

- [ ] **Step 5: write the test and commit**

`GebTests/Mathlib/Logic/Equiv/Fin/Basic.lean`:

```lean
/-- A sample pairing through the product encoding. -/
def sampleProdEncode : Fin (3 * 4) := finProdFinEquivC ((2 : Fin 3), (1 : Fin 4))

/-- The sample pairing is the index `9`. -/
theorem sampleProdEncode_eq : sampleProdEncode = (9 : Fin (3 * 4)) := rfl

/-- The product encoding round-trips at the sample pair. -/
theorem sampleProdEncode_roundtrip :
    finProdFinEquivC.symm sampleProdEncode = ((2 : Fin 3), (1 : Fin 4)) := rfl
```

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(equiv): add a choice-free product encoding of Fin"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 4: the choice-free exponential encoding

Spec sections: § The exponential recursion is choice-free end to end,
§ Row g (the `Logic/Equiv/Fin/Basic.lean` paragraph), § Decisions
fixed here (1 and 3).

**Files:**

- Modify: `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean`
- Modify: `GebTests/Mathlib/Logic/Equiv/Fin/Basic.lean`

**Interfaces:**

- Consumes: `finProdFinEquivC`; `Equiv.equivPUnit`, `finOneEquiv`,
  `finCongr`, `Nat.pow_zero`, `Nat.pow_succ'`, `Fin.consEquiv`,
  `Equiv.prodCongr`, `Equiv.refl`, `Equiv.trans`.
- Produces:
  `finFunctionFinEquivC {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n)`,
  `Fin.funEncodeC {m n : ℕ} (g : Fin n → Fin m) : Fin (m ^ n)`,
  `Fin.funDecodeC {m n : ℕ} (i : Fin (m ^ n)) : Fin n → Fin m`,
  `Fin.funDecodeC_funEncodeC`, `Fin.funEncodeC_funDecodeC`, the last
  two `@[simp]`. Consumed by Task 11 (row g's last step).

The implicit-argument roles match the `finFunctionFinEquiv` this
rebuilds — codomain `m`, domain `n` — rather than the domain-first
reading Task 11's own variable names use. A `C` suffix advertises the
same declaration rebuilt, and a silently swapped implicit order is
what bites at the rename on upstream submission.

- [ ] **Step 1: add the equivalence**

Append to `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean`, after
`finProdFinEquivC`. This text was elaborated at this toolchain and
measured `[propext, Quot.sound]`.

```lean
/-- The choice-free exponential encoding, by recursion on the arity
over `finProdFinEquivC` (unlike mathlib's `finFunctionFinEquiv`,
whose base-`m` digit round trips depend on `Classical.choice`). -/
def finFunctionFinEquivC {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Nat.rec (motive := fun k ↦ (Fin k → Fin m) ≃ Fin (m ^ k))
    (((Equiv.equivPUnit (Fin 0 → Fin m)).trans finOneEquiv.symm).trans
      (finCongr (Nat.pow_zero m).symm))
    (fun k ih ↦
      (((Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin m)).symm.trans
        (Equiv.prodCongr (Equiv.refl (Fin m)) ih)).trans finProdFinEquivC).trans
        (finCongr (Nat.pow_succ' (m := m) (n := k)).symm))
    n
```

Four points, each measured:

- `Equiv.funUnique` cannot serve the base case: `Unique (Fin 0)` does
  not exist, `Fin 0` being empty rather than a singleton. What is a
  singleton is the *function type* `Fin 0 → Fin m`, whose `Unique`
  instance `Equiv.equivPUnit` finds.
- `finCongr (Nat.pow_zero m).symm` closes the base case because
  instance search will not reduce `m ^ 0` to `1` at reducible
  transparency.
- `Equiv.piFinSucc` does not exist at this revision.
  `Fin.consEquiv (α)` states
  `α 0 × ((i : Fin k) → α i.succ) ≃ ((i : Fin (k + 1)) → α i)`, so
  the successor step takes its `symm`.
- `Nat.pow_succ'` is stated `m ^ n.succ = m * m ^ n` with both
  variables named `m` and `n`; the named arguments are
  `(m := m) (n := k)`, not `(b := m)`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: add the two operations and their round trips**

```lean
namespace Fin

/-- Encode a function `Fin n → Fin m` as an index of `Fin (m ^ n)`:
the forward direction of `finFunctionFinEquivC`. -/
def funEncodeC {m n : ℕ} (g : Fin n → Fin m) : Fin (m ^ n) :=
  finFunctionFinEquivC g

/-- Decode an index of `Fin (m ^ n)` as a function `Fin n → Fin m`:
the inverse direction of `finFunctionFinEquivC`. -/
def funDecodeC {m n : ℕ} (i : Fin (m ^ n)) : Fin n → Fin m :=
  finFunctionFinEquivC.symm i

/-- Decoding an encoded function recovers it. -/
@[simp] theorem funDecodeC_funEncodeC {m n : ℕ} (g : Fin n → Fin m) :
    funDecodeC (funEncodeC g) = g :=
  finFunctionFinEquivC.left_inv g

/-- Encoding a decoded index recovers it. -/
@[simp] theorem funEncodeC_funDecodeC {m n : ℕ} (i : Fin (m ^ n)) :
    funEncodeC (funDecodeC i) = i :=
  finFunctionFinEquivC.right_inv i

end Fin
```

No auxiliary equivalence sits beneath `finFunctionFinEquivC`: the
`Nat.rec` produces the equivalence first, and these two are its
`toFun` and `invFun` under names the `@[simp]` lemmas are stated
over, per decision 3.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: check the axioms**

Measure all five declarations, and a monomorphic witness:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeEncode : Fin (3 ^ 2) :=
  Fin.funEncodeC (fun i : Fin 2 ↦ (⟨i.val, by omega⟩ : Fin 3))
```

Expected: `[propext, Quot.sound]` throughout. Delete `probeEncode`
after measuring. Then run the banned-form grep. Expected: no match.

- [ ] **Step 4: extend the test and commit**

Append to `GebTests/Mathlib/Logic/Equiv/Fin/Basic.lean`:

```lean
/-- A sample function encoded through the exponential encoding. -/
def sampleFunEncode : Fin (3 ^ 2) :=
  Fin.funEncodeC (fun i : Fin 2 ↦ (⟨i.val, by omega⟩ : Fin 3))

/-- The sample encoding is the index `1`: the pairing puts the head
digit high, so the function sending `0` to `0` and `1` to `1`
encodes as `0 * 3 + 1`. -/
theorem sampleFunEncode_eq : sampleFunEncode = (1 : Fin (3 ^ 2)) := by decide

/-- The exponential encoding round-trips at the sample function. -/
theorem sampleFunEncode_roundtrip (i : Fin 2) :
    Fin.funDecodeC sampleFunEncode i = (⟨i.val, by omega⟩ : Fin 3) := by
  simp only [sampleFunEncode, Fin.funDecodeC_funEncodeC]
```

`simp only`, not `rw`: `rw` elaborates its arguments as proofs of an
equality or an iff, and `sampleFunEncode` is a `def`, not a proof.

If `decide` is slow or fails to reduce, `rfl` is the alternative;
report which one closed it. Both are kernel reductions of a
`Nat.rec` at a literal, so one of the two closes.

Run: `lake build`, `lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(equiv): add a choice-free exponential encoding of Fin"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 5: the shapes core — the index correspondence, points, rows a and b

Spec sections: § W1's index-function correspondence is not an `Equiv`
and is `ULift`ed, § Rows a and b, § Module layout.

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`
- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`,
  `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`

**Interfaces:**

- Consumes, from W1's `FinSetSkel/Basic.lean`: `FinSetSkel.mk`,
  `FinSetSkel.len`, `Hom.ofVec`, `Hom.toVec`, `hom_ext`, `id_get`,
  `comp_get`, `ofIdxFun`, `toIdxFun`, `ofIdxFun_get`,
  `ofIdxFun_toIdxFun`, `toIdxFun_ofIdxFun`; from
  `Data/Vector/OfFn.lean`: `Vector.ofFnC`, `Vector.get_ofFnC`; from
  Task 1: `Equiv.arrowCongrLeftC`.
- Produces, in namespace `FinSetSkel`: `homEquivIdxFunU`,
  `homEquivIdxFun`, `homEquivIdxFun_apply`,
  `homEquivIdxFun_symm_get`, `point`, `point_get`, `fromZero`,
  `fromZero_uniq`, `toOne`, `toOne_uniq`. `homEquivIdxFun` itself is
  consumed by Task 11 and its two application lemmas by Task 13;
  `point` by Tasks 10 and 18;
  `fromZero`, `fromZero_uniq`, `toOne` and `toOne_uniq` by Tasks 8, 9
  and 18.

Rows c, d and h do **not** consume `homEquivIdxFun`, although the
spec's § W1's index-function correspondence anticipates that they
would: this plan states each of those rows over `f.toVec.get i`, W1's
application-normal form, and proves the universal properties by
`hom_ext` and `comp_get`, which is shorter than transporting a
statement about index functions and needs no equivalence. Row g does
consume it, in both directions, so the deliverable stands and W5's
access to it is unaffected. Do not add the import to Tasks 6, 7, 14
or 15 on the strength of the spec's sentence; `lake shake` at Task 19
would reject it.

`homEquivIdxFun` stays a W3 deliverable rather than moving to
`feat/choice-free-primitives`: W4's spec § Out of scope states that
row i does not use it, every W4 construction and statement being over
`f.toVec.get i` directly. That assumption of the spec's § W1's
index-function correspondence is hereby confirmed, so the fallback
module `FinSetSkel/Hom.lean` on the shared branch is not created.

- [ ] **Step 1: create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Logic.Equiv.Basic

/-!
# The initial and terminal objects, coproducts and products of `FinSetSkel`

The constructions of rows a, b, c and d over `Fin` and vectors,
together with the content of their universal properties, stated in
W1's application-normal form `f.toVec.get i`. The mathlib cones and
`Prop` instances built from them are in `Shapes/Instances.lean`; this
module is choice-free.

W1 exports the correspondence between morphisms and index functions
as the pair `ofIdxFun` / `toIdxFun` over
`ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)`, not as an `Equiv`
and not over bare index functions. `homEquivIdxFun` packages the two
round trips and removes both `ULift`s, so that a universal property
stated over index functions can be transported to one over morphisms.
Its domain transport is `Equiv.arrowCongrLeftC`; mathlib's
`Equiv.arrowCongr` and the `Equiv.piCongrLeft` family all depend on
`Classical.choice`.

## Main definitions

* `FinSetSkel.homEquivIdxFun` — morphisms as index functions.
* `FinSetSkel.point` — the morphism out of the one-element object
  picking a given index.
* `FinSetSkel.fromZero`, `FinSetSkel.toOne` — the canonical
  morphisms out of the empty and into the one-element object.
* `FinSetSkel.coprodObj`, `FinSetSkel.coprodInl`,
  `FinSetSkel.coprodInr`, `FinSetSkel.coprodDesc` — binary
  coproducts.
* `FinSetSkel.prodObj`, `FinSetSkel.prodFst`, `FinSetSkel.prodSnd`,
  `FinSetSkel.prodLift` — binary products.

## Main statements

* `FinSetSkel.fromZero_uniq`, `FinSetSkel.toOne_uniq` — initiality
  and terminality.
* `FinSetSkel.coprodInl_desc`, `FinSetSkel.coprodInr_desc`,
  `FinSetSkel.coprodDesc_uniq` — the coproduct's universal property.
* `FinSetSkel.prodLift_fst`, `FinSetSkel.prodLift_snd`,
  `FinSetSkel.prodLift_uniq` — the product's universal property.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, coproduct, product, terminal, choice-free
-/

@[expose] public section

universe u

namespace FinSetSkel

end FinSetSkel
```

The `## Main definitions` and `## Main statements` lists name Tasks 6
and 7's declarations as well; the module docstring is written once,
in this step, and the later tasks add no sections to it.

Confirm every name Tasks 5, 6 and 7 introduce — the ones the docstring
lists above — is free under this module's own import set, before
writing any of them. The procedure, inside the namespace block:

```lean
#check @FinSetSkel.homEquivIdxFun
```

Run `lake build` and expect FAIL with "unknown identifier". A success
means the name is already taken under these imports and the plan's
naming must change; report that. Repeat for each name and delete the
`#check`s afterwards. A probe file cannot substitute: it sees only its
own imports.

- [ ] **Step 2: add the index-function correspondence**

Inside the namespace block:

```lean
variable {X Y : FinSetSkel.{u}}

/-- Morphisms as lifted index functions: W1's `ofIdxFun` and
`toIdxFun` as an equivalence. -/
def homEquivIdxFunU (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) where
  toFun := toIdxFun
  invFun := ofIdxFun
  left_inv := ofIdxFun_toIdxFun
  right_inv := toIdxFun_ofIdxFun

/-- Morphisms as index functions. -/
def homEquivIdxFun (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (Fin X.len → Fin Y.len) :=
  (homEquivIdxFunU X Y).trans
    ((Equiv.arrowCongrLeftC Equiv.ulift).trans
      (Equiv.piCongrRight fun _ ↦ Equiv.ulift))
```

`Equiv.arrowCongrLeftC Equiv.ulift` is applied at
`α = ULift.{u} (Fin X.len) : Type u`, `β = Fin X.len : Type 0` and
`γ = ULift.{u} (Fin Y.len) : Type u`, which is why the declaration
needs independent `Sort` levels. No `.symm` appears on either
`Equiv.ulift`: `Equiv.ulift : ULift α ≃ α`, and both transports run
in that direction.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: add the two application lemmas**

```lean
/-- The index function of a morphism is its normal-form lookup. -/
@[simp] theorem homEquivIdxFun_apply (f : X ⟶ Y) (i : Fin X.len) :
    homEquivIdxFun X Y f i = f.toVec.get i := rfl

/-- The morphism of an index function looks up by that function. -/
@[simp] theorem homEquivIdxFun_symm_get
    (g : Fin X.len → Fin Y.len) (i : Fin X.len) :
    ((homEquivIdxFun X Y).symm g).toVec.get i = g i := by
  simp [homEquivIdxFun, homEquivIdxFunU, ofIdxFun_get]
```

Both orientations rewrite *toward* W1's normal form `f.toVec.get i`,
so neither disturbs the other workstream's normal form, per
`TODO.md`'s remark that W3's and W4's carrier-level `simp` lemmas
first meet at W5. If `rfl` does not close the first, prove it by
`simp [homEquivIdxFun, homEquivIdxFunU, toIdxFun]` and record which
was needed.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add rows a and b**

```lean
/-- The unique morphism out of the empty object. -/
def fromZero (Y : FinSetSkel.{u}) : mk 0 ⟶ Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ i.elim0)

/-- Any morphism out of the empty object is the canonical one. -/
theorem fromZero_uniq {Y : FinSetSkel.{u}} (f : mk 0 ⟶ Y) :
    f = fromZero Y :=
  hom_ext fun i ↦ i.elim0

/-- The unique morphism into the one-element object. -/
def toOne (X : FinSetSkel.{u}) : X ⟶ mk 1 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- Any morphism into the one-element object is the canonical one. -/
theorem toOne_uniq {X : FinSetSkel.{u}} (f : X ⟶ mk 1) :
    f = toOne X :=
  hom_ext fun _ ↦ Subsingleton.elim _ _

/-- The morphism out of the one-element object picking an index. -/
def point {X : FinSetSkel.{u}} (i : Fin X.len) : mk 1 ⟶ X :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ i)

/-- A point looks up the index it picks. -/
@[simp] theorem point_get {X : FinSetSkel.{u}} (i : Fin X.len)
    (t : Fin (mk 1).len) : (point i).toVec.get t = i :=
  Vector.get_ofFnC _ _
```

`point` is a separate deliverable from `toOne`: row m's forward
direction tests a morphism against two maps *out of* a one-element
object, and no other row supplies those. `Subsingleton (Fin 1)` is
the instance closing `toOne_uniq`; `Fin.elim0` is the eliminator out
of the empty index type.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: check the axioms**

Every declaration is polymorphic in `X`, `Y` and the universe, so
measure a monomorphic witness at the instances actually used as well
as the constants themselves:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probePoint : (mk 1 : FinSetSkel.{0}) ⟶ mk 3 := point (2 : Fin 3)

/-- Monomorphic witness for the axiom measurement. -/
def probeIdxFun : Fin 3 → Fin 3 := homEquivIdxFun (mk 3) (mk 3) (𝟙 (mk 3 : FinSetSkel.{0}))
```

Expected: `[propext, Quot.sound]`. Delete both after measuring. Then
run the banned-form grep. Expected: no match — note that W1's own
`Hom.id` uses `Vector.ofFnC`, so the grep must not match
`Vector.ofFnC`.

- [ ] **Step 6: create the index files and wire them**

`Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes.lean` importing
`Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core` and (from Task 8)
`…Shapes.Instances`; add the `Instances` line in Task 8 rather than
here, so the tree builds now. Title `# Shapes — index`. Its
`GebTests` parallel likewise, with plain `import`.

Add `public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes` to
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, and the plain-`import`
parallel to the `GebTests` file. That file is a W3/W4 conflict point
named in `TODO.md` § Standing obligations; the later sibling rebases.

- [ ] **Step 7: write the test parallel and commit**

`GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`:

```lean
/-- A sample point of the three-element object. -/
def samplePoint : (mk 1 : FinSetSkel.{0}) ⟶ mk 3 := point (2 : Fin 3)

/-- The sample point picks the index it names. -/
theorem samplePoint_get (t : Fin (mk 1 : FinSetSkel.{0}).len) :
    samplePoint.toVec.get t = 2 := point_get _ _

/-- The index-function correspondence round-trips the sample
point. -/
theorem samplePoint_roundtrip :
    (homEquivIdxFun (mk 1) (mk 3)).symm
      (homEquivIdxFun (mk 1) (mk 3) samplePoint) = samplePoint :=
  (homEquivIdxFun (mk 1) (mk 3)).symm_apply_apply samplePoint

/-- Every morphism into the one-element object is the canonical
one. -/
theorem sampleToOne (f : (mk 3 : FinSetSkel.{0}) ⟶ mk 1) : f = toOne (mk 3) :=
  toOne_uniq f
```

The test module opens `FinSetSkel` rather than qualifying each name;
`open FinSetSkel` at the top of the file, after the section, is the
form W1's test parallels use — check
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` and follow it.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the index correspondence, points and units"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 6: row c — binary coproducts, core

Spec section: § Row c.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`

**Interfaces:**

- Consumes: Task 5's declarations; `finSumFinEquiv`, which is
  choice-free at `[propext, Quot.sound]` and usable as it stands;
  `Sum.elim`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`.
- Produces: `coprodObj`, `coprodInl`, `coprodInr`, `coprodDesc`,
  `coprodInl_get`, `coprodInr_get`, `coprodDesc_get`,
  `coprodInl_desc`, `coprodInr_desc`, `coprodDesc_uniq`. Consumed by
  Task 9.

- [ ] **Step 1: add the object and the two injections**

```lean
/-- The binary coproduct object: lengths add. -/
def coprodObj (X Y : FinSetSkel.{u}) : FinSetSkel.{u} := mk (X.len + Y.len)

/-- The left injection into the binary coproduct. -/
def coprodInl (X Y : FinSetSkel.{u}) : X ⟶ coprodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ finSumFinEquiv (Sum.inl i))

/-- The right injection into the binary coproduct. -/
def coprodInr (X Y : FinSetSkel.{u}) : Y ⟶ coprodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ finSumFinEquiv (Sum.inr i))

/-- The left injection acts by the left summand embedding. -/
@[simp] theorem coprodInl_get (X Y : FinSetSkel.{u}) (i : Fin X.len) :
    (coprodInl X Y).toVec.get i = finSumFinEquiv (Sum.inl i) :=
  Vector.get_ofFnC _ _

/-- The right injection acts by the right summand embedding. -/
@[simp] theorem coprodInr_get (X Y : FinSetSkel.{u}) (i : Fin Y.len) :
    (coprodInr X Y).toVec.get i = finSumFinEquiv (Sum.inr i) :=
  Vector.get_ofFnC _ _
```

`finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)`; confirm the direction
with `#check @finSumFinEquiv` before relying on it, per verification
obligation 5.

Its implicit `{m n}` are solved by unifying `Fin (?m + ?n)` against
`Fin (coprodObj X Y).len`, which needs the plain `def coprodObj` to
delta-unfold. If the elaborator does not see through it, ascribe the
index type as `Fin (X.len + Y.len)` and report the divergence to the
orchestrator — the same hedge Task 7 carries for `prodObj`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: add the descent morphism**

```lean
/-- The morphism out of a binary coproduct determined by its two
components. -/
def coprodDesc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprodObj X Y ⟶ Z :=
  Hom.ofVec (Vector.ofFnC fun i ↦
    Sum.elim (fun a ↦ f.toVec.get a) (fun b ↦ g.toVec.get b)
      (finSumFinEquiv.symm i))

/-- The descent morphism acts by case analysis on the summand. -/
@[simp] theorem coprodDesc_get {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (i : Fin (coprodObj X Y).len) :
    (coprodDesc f g).toVec.get i =
      Sum.elim (fun a ↦ f.toVec.get a) (fun b ↦ g.toVec.get b)
        (finSumFinEquiv.symm i) :=
  Vector.get_ofFnC _ _
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: state the three universal-property lemmas unproved**

```lean
/-- Descent restricted along the left injection is its left
component. -/
@[simp] theorem coprodInl_desc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) : coprodInl X Y ≫ coprodDesc f g = f := _

/-- Descent restricted along the right injection is its right
component. -/
@[simp] theorem coprodInr_desc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) : coprodInr X Y ≫ coprodDesc f g = g := _

/-- A morphism agreeing with both components on the injections is
the descent morphism. -/
theorem coprodDesc_uniq {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (m : coprodObj X Y ⟶ Z)
    (hl : coprodInl X Y ≫ m = f) (hr : coprodInr X Y ≫ m = g) :
    m = coprodDesc f g := _
```

Run: `lake build`
Expected: FAIL, three "don't know how to synthesize placeholder"
errors. Underscores expose the goals, per
`docs/rules/lean-coding.md` § Proof guidelines; `sorry` is not used
here, no tool requiring it being in play.

- [ ] **Step 4: prove the two factorisations**

```lean
  hom_ext fun i ↦ by
    rw [comp_get, coprodInl_get, coprodDesc_get, Equiv.symm_apply_apply,
      Sum.elim_inl]
```

and the same with `coprodInr_get` and `Sum.elim_inr` for the right
factorisation. `Sum.elim_inl` is not optional: after
`Equiv.symm_apply_apply` the goal is `Sum.elim … (Sum.inl i) = …`, and
`rw`'s trailing `rfl` runs at reducible transparency, at which
`Sum.elim` does not unfold.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: prove uniqueness**

```lean
  hom_ext fun i ↦ by
    rcases hs : finSumFinEquiv.symm i with a | b
    · have : i = finSumFinEquiv (Sum.inl a) := by
        rw [← hs, Equiv.apply_symm_apply]
      subst this
      rw [coprodDesc_get, Equiv.symm_apply_apply, Sum.elim_inl, ← hl, comp_get,
        coprodInl_get]
    · have : i = finSumFinEquiv (Sum.inr b) := by
        rw [← hs, Equiv.apply_symm_apply]
      subst this
      rw [coprodDesc_get, Equiv.symm_apply_apply, Sum.elim_inr, ← hr, comp_get,
        coprodInr_get]
```

The `Sum.elim_inl` / `Sum.elim_inr` step must come **before** the
`← hl` / `← hr` rewrite. Without it `f` is still under the binder
`fun a ↦ f.toVec.get a`, so after `← hl` the subsequent `comp_get`
would have to abstract `(coprodInl X Y ≫ m).toVec.get a` with `a` a
bound variable, which `kabstract` cannot do; the rewrite fails with
"motive is not type correct".

`rcases` is case analysis on a `Sum`, not a recursion, so it is
permitted. If `subst` refuses because `i` is not a local hypothesis
in the right form, replace it with `rw [this]` and adjust the
rewrite chain; report which was needed to the orchestrator.

Run: `lake build`
Expected: PASS.

- [ ] **Step 6: check the axioms, test and commit**

Measure all ten new declarations — the object, the two injections,
the descent morphism, the three `_get` lemmas and the three
universal-property theorems — and a monomorphic witness:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeDesc : coprodObj (mk 2) (mk 3) ⟶ (mk 3 : FinSetSkel.{0}) :=
  coprodDesc (Hom.ofVec (Vector.ofFnC fun _ ↦ 0)) (𝟙 (mk 3))
```

Expected: `[propext, Quot.sound]`. Delete the witness; run the
banned-form grep.

Append to the test parallel a computed coproduct: the descent of two
sample morphisms, one `rfl` assertion of its vector, and the
factorisation at a sample index. The shape is a named `def` value
built from the module under test, then `theorem`s asserting its
computed values by `rfl` — per § Global constraints, which explains
why an `example` alone would fail `lake shake`.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS. `lint-imports.sh` is the gate for the
no-self-prefix-leakage constraint, and this task adds ten declarations
to an upstream-eligible module.

```bash
jj commit -m "feat(finsetskel): add binary coproducts over vectors"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 7: row d — binary products, core

Spec section: § Row d.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`

**Interfaces:**

- Consumes: Task 2's `Fin.divNatC`, `Fin.modNatC`, `Fin.pairC` and
  their three `@[simp]` round trips. Add
  `public import Geb.Mathlib.Data.Fin.Basic` to the module.
- Produces: `prodObj`, `prodFst`, `prodSnd`, `prodLift`,
  `prodFst_get`, `prodSnd_get`, `prodLift_get`, `prodLift_fst`,
  `prodLift_snd`, `prodLift_uniq`. Consumed by Tasks 8 and 12.

`Shapes/Core.lean` imports `Data/Fin/Basic.lean` and **not**
`Logic/Equiv/Fin/Basic.lean`: row d's projections are the three
operations, not `finProdFinEquivC`, and an import for a declaration
nothing in the module consumes fails `lake shake`.

- [ ] **Step 1: add the object, projections and lift**

```lean
/-- The binary product object: lengths multiply. -/
def prodObj (X Y : FinSetSkel.{u}) : FinSetSkel.{u} := mk (X.len * Y.len)

/-- The first projection of the binary product. -/
def prodFst (X Y : FinSetSkel.{u}) : prodObj X Y ⟶ X :=
  Hom.ofVec (Vector.ofFnC Fin.divNatC)

/-- The second projection of the binary product. -/
def prodSnd (X Y : FinSetSkel.{u}) : prodObj X Y ⟶ Y :=
  Hom.ofVec (Vector.ofFnC Fin.modNatC)

/-- The morphism into a binary product determined by its two
components. -/
def prodLift {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ prodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun t ↦ Fin.pairC (f.toVec.get t) (g.toVec.get t))

/-- The first projection acts by the quotient. -/
@[simp] theorem prodFst_get (X Y : FinSetSkel.{u})
    (i : Fin (prodObj X Y).len) :
    (prodFst X Y).toVec.get i = Fin.divNatC i := Vector.get_ofFnC _ _

/-- The second projection acts by the remainder. -/
@[simp] theorem prodSnd_get (X Y : FinSetSkel.{u})
    (i : Fin (prodObj X Y).len) :
    (prodSnd X Y).toVec.get i = Fin.modNatC i := Vector.get_ofFnC _ _

/-- The lift acts by pairing its components' lookups. -/
@[simp] theorem prodLift_get {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) (t : Fin Z.len) :
    (prodLift f g).toVec.get t =
      Fin.pairC (f.toVec.get t) (g.toVec.get t) := Vector.get_ofFnC _ _
```

`Fin.divNatC` at `Fin (prodObj X Y).len` is at `m := X.len`,
`n := Y.len`, `(prodObj X Y).len` reducing to `X.len * Y.len` by
`rfl`. If the elaborator does not see through `prodObj`, ascribe the
argument type; report if so.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: state the three universal-property lemmas unproved**

```lean
/-- The lift followed by the first projection is its first
component. -/
@[simp] theorem prodLift_fst {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) : prodLift f g ≫ prodFst X Y = f := _

/-- The lift followed by the second projection is its second
component. -/
@[simp] theorem prodLift_snd {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) : prodLift f g ≫ prodSnd X Y = g := _

/-- A morphism agreeing with both components on the projections is
the lift. -/
theorem prodLift_uniq {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) (m : Z ⟶ prodObj X Y)
    (hf : m ≫ prodFst X Y = f) (hg : m ≫ prodSnd X Y = g) :
    m = prodLift f g := _
```

Run: `lake build`
Expected: FAIL, three placeholder errors.

- [ ] **Step 3: prove all three**

```lean
  hom_ext fun t ↦ by
    rw [comp_get, prodLift_get, prodFst_get, Fin.divNatC_pairC]
```

for the first, `Fin.modNatC_pairC` for the second, and for
uniqueness:

```lean
  hom_ext fun t ↦ by
    rw [prodLift_get, ← hf, ← hg, comp_get, comp_get, prodFst_get,
      prodSnd_get, Fin.pairC_divNatC_modNatC]
```

Each factorisation is discharged by exactly one of the three
`@[simp]` round trips of Task 2, which is why they are the
carrier-level normal form.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: check the axioms, test and commit**

Measure the seven new declarations plus a monomorphic witness:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeLift : (mk 5 : FinSetSkel.{0}) ⟶ prodObj (mk 2) (mk 3) :=
  prodLift (Hom.ofVec (Vector.ofFnC fun _ ↦ 0))
    (Hom.ofVec (Vector.ofFnC fun _ ↦ 1))
```

Expected: `[propext, Quot.sound]`. Delete the witness; run the
banned-form grep.

Append to the test parallel a computed product: a lift of two sample
morphisms with its vector asserted by `rfl`, and both factorisations
at a sample index.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add binary products over vectors"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 8: the cartesian wrapper

Spec sections: § The cartesian structure already supplies three
`Prop` classes, § Rows a and b (the wrapper paragraph), § Row d (the
wrapper paragraph), § Exported names, § Decisions fixed here (10).

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean`
- Modify: `GebMeta.lean`,
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes.lean` and its
  `GebTests` parallel

**Interfaces:**

- Consumes: Tasks 5 and 7; `LimitCone`, `asEmptyCone`,
  `Functor.empty`, `IsTerminal.ofUniqueHom`, `BinaryFan.mk`,
  `BinaryFan.IsLimit.mk`, `Limits.pair`,
  `CartesianMonoidalCategory.ofChosenFiniteProducts`,
  `SemiCartesianMonoidalCategory.isTerminalTensorUnit`.
- Produces: `FinSetSkel.terminalCone`,
  `FinSetSkel.binaryProductCone`,
  `FinSetSkel.cartesianMonoidalCategory` (a global `instance`),
  `FinSetSkel.isTerminalOne`. Consumed by Task 12 (`⊗`, `◁`, the
  whiskering lemmas), Task 13 (`cartesianMonoidalCategory`, through
  `⊗` and `MonoidalClosed FinSetSkel`), Task 18 (`isTerminalOne`),
  and by W5's `cartesian` field. Task 9 extends this module without
  consuming anything of this task's.

`cartesianMonoidalCategory` is a global `instance`, not W2's
`@[instance_reducible] def` plus `attribute [local instance]`. Three
things depend on it: the priority-100
`instance : HasFiniteProducts C` of
`Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean` fires, so rows
f and j need no registration; `X ⊗ Z` elaborates in Task 12; and W2's
`closed` field is well-typed only over this exact term. W2's opposite
convention applies to accessors *from* `[ElementaryTopos C]`, where
two routes to data need not agree; here there is one term and it is
the definition. **W3 declares no second
`CartesianMonoidalCategory FinSetSkel`.**

- [ ] **Step 1: allowlist the two module names first**

Append to `classicalAllowedModules` in `GebMeta.lean`:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
```

First, so that the first `lake lint` after the module exists reports
real findings rather than the expected `Classical.choice`.
`CartesianMonoidalCategory` and `ofChosenFiniteProducts` both depend
on it, so every declaration in this module does.

- [ ] **Step 2: create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The cartesian and coproduct structure of `FinSetSkel`

The mathlib packaging of `Shapes/Core.lean`'s rows a, b, c and d: the
chosen cones, the `CartesianMonoidalCategory` instance built from
them, and the `Prop` instances a later workstream consumes.
`CartesianMonoidalCategory` depends on `Classical.choice`, so this
module is allowlisted and the constructions it packages are not.

`CartesianMonoidalCategory.ofChosenFiniteProducts` takes a terminal
cone and a family of binary product cones and supplies the
associator, the unitors and the coherence conditions, so no
monoidal law is proved here. Its instance registers
`HasFiniteProducts`, `HasTerminal` and `HasBinaryProducts` at
priority 100, so none of the three is registered separately.

## Main definitions

* `FinSetSkel.terminalCone`, `FinSetSkel.binaryProductCone`,
  `FinSetSkel.initialCocone`, `FinSetSkel.binaryCoproductCocone` —
  the chosen cones.
* `FinSetSkel.cartesianMonoidalCategory` — the cartesian structure.
* `FinSetSkel.isTerminalOne` — the one-element object is terminal.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, cartesian, coproduct, topos
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace FinSetSkel

end FinSetSkel
```

The docstring names Task 9's declarations too; it is written once.

- [ ] **Step 3: add the terminal cone and the product cones**

```lean
/-- The chosen terminal cone: the one-element object. -/
def terminalCone : LimitCone (Functor.empty.{0} FinSetSkel.{u}) where
  cone := asEmptyCone (mk 1)
  isLimit := IsTerminal.ofUniqueHom (fun X ↦ toOne X) (fun _ f ↦ toOne_uniq f)

/-- The chosen binary product cone. -/
def binaryProductCone (X Y : FinSetSkel.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (prodFst X Y) (prodSnd X Y)
  isLimit :=
    BinaryFan.IsLimit.mk _ (fun f g ↦ prodLift f g)
      (fun f g ↦ prodLift_fst f g) (fun f g ↦ prodLift_snd f g)
      (fun f g m hf hg ↦ prodLift_uniq f g m hf hg)
```

Both cones are pinned at universe `0`: `ofChosenFiniteProducts` binds
only the category's two universe parameters, so `Functor.empty`'s
level is literally `0` there. `IsTerminal X` is `IsLimit
(asEmptyCone X)` by definition, which is why the `isLimit` field
accepts an `IsTerminal`.

Confirm the argument order of `BinaryFan.IsLimit.mk` with `#check`
**before** writing the code above — the `uniq` argument takes `m`
after the two components.

`BinaryFan.IsLimit.mk`'s `fac` and `uniq` arguments are stated over
`s.fst` and `s.snd`, which for `BinaryFan.mk (prodFst X Y)
(prodSnd X Y)` reduce through `Discrete.natTrans` and
`WalkingPair.casesOn`. Supplying `prodLift_fst`, `prodLift_snd` and
`prodLift_uniq` directly relies on that reduction, so check it rather
than assume it:

```lean
example (X Y : FinSetSkel.{u}) :
    (BinaryFan.mk (prodFst X Y) (prodSnd X Y)).fst = prodFst X Y := rfl

example (X Y : FinSetSkel.{u}) :
    (BinaryFan.mk (prodFst X Y) (prodSnd X Y)).snd = prodSnd X Y := rfl
```

Task 12 Step 3's check of the monoidal `fst`/`snd` presupposes this
one, so a failure here is diagnosed before that task rather than
inside it.

Run: `lake build`
Expected: PASS — with the two `example`s still present, so this step's
gate covers them and not only the two cones. Delete the two `example`s
and the `#check` once it passes; § Global constraints requires the
`#check` to run in this module rather than in a probe, so it is here
until then and not after.

- [ ] **Step 4: add the cartesian instance**

```lean
/-- The cartesian monoidal structure, from the chosen terminal cone
and the chosen binary product cones. -/
instance cartesianMonoidalCategory :
    CartesianMonoidalCategory FinSetSkel.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone
    binaryProductCone
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: confirm the unit is the one-element object, then
name `isTerminalOne`**

```lean
example : (𝟙_ FinSetSkel.{u}) = mk 1 := rfl

/-- The one-element object is terminal. -/
def isTerminalOne : IsTerminal (mk 1 : FinSetSkel.{u}) :=
  SemiCartesianMonoidalCategory.isTerminalTensorUnit
```

`ofChosenFiniteProducts` sets `tensorUnit := 𝒯.cone.pt`, which is
`mk 1` on the nose, so the ascription typechecks by definitional
unfolding and no parallel terminality proof is built, per
`docs/rules/lean-coding.md` § Higher-order constructions. Delete the
`example` after the build below passes — it is a check, not a
deliverable.

If the `example` fails, the two objects are not definitionally equal
and the fallback is `isTerminalOne := terminalCone.isLimit`, whose
type is the same by the definition of `IsTerminal`. Report which route
was taken to the orchestrator: Task 18 builds `Ω₀` on this, and
constraint 6's identification depends on it.

Also confirm the name resolves:
`#check @SemiCartesianMonoidalCategory.isTerminalTensorUnit`. The
spec names it `CartesianMonoidalCategory.isTerminalTensorUnit`; the
declaration lives on the semi-cartesian parent and is reached through
either spelling.

Run: `lake build`
Expected: PASS — with the `example` and the `#check` still present, so
this step's gate covers them. Delete both once it passes; § Global
constraints puts the `#check` in this module rather than in a probe,
which is why it is here until then.

- [ ] **Step 6: check the axioms**

Measure `terminalCone`, `binaryProductCone`,
`cartesianMonoidalCategory` and `isTerminalOne`.

Expected: `[propext, Classical.choice, Quot.sound]` — this module is
the allowlisted wrapper and the taint is
`CartesianMonoidalCategory`'s. What must **not** happen is a
`Classical.choice` in `Shapes/Core.lean`. Confirm the cartesian
instance's arrival changed nothing there by re-measuring that
module's permanent witness — `samplePoint`, the named `def` in
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean`.
Expected: `[propext, Quot.sound]`. If it now carries
`Classical.choice`, a `simp` in the core has started reaching the new
instance; stop and report.

- [ ] **Step 7: wire the index files and commit**

Add the `Shapes.Instances` import line to
`Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes.lean` and its
`GebTests` parallel. Create
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean`
now, with its preamble and module docstring, **no declaration and no
import of the module under test**: the `GebTests` index file imports
it, so it must exist for the test library to build, but an import
reached by no constant is what `lake shake` reports as removable.
Task 9 adds the import together with its first `def`. `lake shake`
does not run until Task 19, so either order builds; this one keeps the
tree shake-clean at every commit.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS. The `GebTests` half of the set is what exercises the
stub and the index line this step wrote; without it a mistyped import
commits green and surfaces inside Task 9.

```bash
jj commit -m "feat(finsetskel): add the cartesian monoidal structure"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 9: the coproduct wrapper and finite coproducts

Spec sections: § Row c (the wrapper paragraph), § Row e, § The
cartesian structure already supplies three `Prop` classes.

**Files:**

- Modify:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean`
- Modify:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean`
  (created as a declaration-free stub in Task 8 Step 7)

**Interfaces:**

- Consumes: Tasks 5 and 6; `ColimitCocone`, `asEmptyCocone`,
  `IsInitial.ofUniqueHom`, `IsInitial.hasInitial`, `BinaryCofan.mk`,
  `BinaryCofan.IsColimit.mk`, `hasBinaryCoproducts_of_hasColimit_pair`,
  `hasFiniteCoproducts_of_has_binary_and_initial`.
- Produces: `FinSetSkel.initialCocone`,
  `FinSetSkel.binaryCoproductCocone`, and the instances
  `HasInitial FinSetSkel`, `HasColimit (pair X Y)`,
  `HasBinaryCoproducts FinSetSkel`, `HasFiniteCoproducts FinSetSkel`.
  The two cocones are consumed by W5's `initialCocone` and
  `binaryCoproductCocone` fields.

`hasFiniteCoproducts_of_has_binary_and_initial` is
`CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial`, not
under `Limits`; confirm with `#check` before use. `HasEqualizers`,
`HasTerminal`, `HasBinaryProducts`, `HasFiniteProducts` and
`HasFiniteLimits` are **not** registered: the first has no consumer
in the interval and the rest come from the cartesian instance. Only
`HasFiniteCoproducts` is registered on constraint 5's instruction,
being one of row k's two hypotheses and so consumed by W5.

- [ ] **Step 1: add the initial cocone and the coproduct cocones**

```lean
/-- The chosen initial cocone: the empty object. -/
def initialCocone : ColimitCocone (Functor.empty.{0} FinSetSkel.{u}) where
  cocone := asEmptyCocone (mk 0)
  isColimit :=
    IsInitial.ofUniqueHom (fun Y ↦ fromZero Y) (fun _ f ↦ fromZero_uniq f)

/-- The chosen binary coproduct cocone. -/
def binaryCoproductCocone (X Y : FinSetSkel.{u}) :
    ColimitCocone (pair X Y) where
  cocone := BinaryCofan.mk (coprodInl X Y) (coprodInr X Y)
  isColimit :=
    BinaryCofan.IsColimit.mk _ (fun f g ↦ coprodDesc f g)
      (fun f g ↦ coprodInl_desc f g) (fun f g ↦ coprodInr_desc f g)
      (fun f g m hl hr ↦ coprodDesc_uniq f g m hl hr)
```

Confirm `IsInitial.ofUniqueHom`'s argument order with `#check`; if it
does not exist at this revision, `IsColimit` for the empty diagram is
built from `IsInitial.ofUnique` or directly, and the `uniq` field
takes the cocone morphism.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: register the three `Prop` classes and the pair-colimit
instance they route through**

```lean
/-- `FinSetSkel` has an initial object. -/
instance hasInitial : HasInitial FinSetSkel.{u} :=
  IsInitial.hasInitial initialCocone.isColimit

/-- `FinSetSkel` has colimits of pairs. -/
instance hasColimit_pair {X Y : FinSetSkel.{u}} : HasColimit (pair X Y) :=
  ⟨⟨binaryCoproductCocone X Y⟩⟩

/-- `FinSetSkel` has binary coproducts. -/
instance hasBinaryCoproducts : HasBinaryCoproducts FinSetSkel.{u} :=
  hasBinaryCoproducts_of_hasColimit_pair FinSetSkel.{u}

/-- `FinSetSkel` has finite coproducts, which row k consumes. -/
instance hasFiniteCoproducts : HasFiniteCoproducts FinSetSkel.{u} :=
  hasFiniteCoproducts_of_has_binary_and_initial
```

`IsInitial.hasInitial` takes the `IsInitial`, and
`initialCocone.isColimit` has that type by the definition of
`IsInitial`. `HasColimit (pair X Y)` is the hypothesis
`hasBinaryCoproducts_of_hasColimit_pair` quantifies over.

The two constructors are written with the category argument spelled
differently — explicitly for `hasBinaryCoproducts_of_hasColimit_pair`
and bare for `hasFiniteCoproducts_of_has_binary_and_initial` —
because they bind it differently upstream. `#check` both and use
whichever spelling each one's signature requires; at most one of the
two forms above is right for either.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: check the axioms**

All four instances are named above — `hasInitial`, `hasColimit_pair`,
`hasBinaryCoproducts`, `hasFiniteCoproducts` — precisely so that this
step has something to measure: an anonymous `instance` has no
qualified name to give `lean_verify`.

The six declarations are `universe u`-polymorphic, and § Global
constraints forbids reading a polymorphic measurement as an
instantiation's, so measure them at monomorphic witnesses. Append,
measure, delete:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeInitialCocone : ColimitCocone (Functor.empty.{0} FinSetSkel.{0}) :=
  initialCocone

/-- Monomorphic witness for the axiom measurement. -/
def probeCoprodCocone : ColimitCocone (pair (mk 2 : FinSetSkel.{0}) (mk 3)) :=
  binaryCoproductCocone _ _
```

The four `Prop` instances need no probe of their own: Step 4's
`sampleInstances` resolves all of them at `FinSetSkel.{0}` in one
`theorem`, so measure that after Step 4 and take it as their
monomorphic witness.

Expected: axioms **contained in**
`{propext, Classical.choice, Quot.sound}`, this being the allowlisted
wrapper — `Classical.choice` is permitted but not required, and
`probeInitialCocone` may measure `[propext, Quot.sound]`. A tighter
set is not a discrepancy; a wider one is.

- [ ] **Step 4: write the test parallel**

`GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean` is
the declaration- and import-free stub Task 8 Step 7 created, so this
step adds its imports as well as its content:

```lean
import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances
```

and, after the `@[expose] public section`,
`open CategoryTheory Limits MonoidalCategory` — `⊗` is scoped notation
and does not resolve without the last of those. The content covers the
resolution of each registered `Prop` instance and the cartesian
structure of Task 8:

```lean
/-- The registered instances resolve. -/
theorem sampleInstances :
    HasInitial FinSetSkel.{0} ∧ HasBinaryCoproducts FinSetSkel.{0} ∧
      HasFiniteCoproducts FinSetSkel.{0} ∧ HasFiniteProducts FinSetSkel.{0} ∧
      HasTerminal FinSetSkel.{0} ∧ HasBinaryProducts FinSetSkel.{0} :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

/-- The tensor product of two objects has the product's length. -/
theorem sampleTensorObj :
    ((mk 2 : FinSetSkel.{0}) ⊗ mk 3) = mk 6 := rfl
```

These classes are all `Prop`-valued — `HasLimitsOfShape` and
`HasColimitsOfShape` are `class … : Prop`, and the six here are
abbreviations of them — so the conjunction is `∧` and the
declaration is a `theorem`. A `Prod` would not elaborate, `Prod`
taking `Type` arguments; and a `theorem` still puts a constant in the
olean, so `lake shake` sees the import.

The `HasFiniteProducts`, `HasTerminal` and `HasBinaryProducts`
components are the point of the test: they are not registered here,
and their resolution is what makes rows f and j redundant.

`sampleTensorObj` asserts `(mk 2 ⊗ mk 3) = mk 6`, which holds by `rfl`
only because Task 8 built the monoidal structure from row d's chosen
cones, so `⊗` unfolds to `prodObj` and thence to `mk (2 * 3)`. If
`rfl` fails, weaken the assertion to `(mk 2 ⊗ mk 3).len = 6` and try
`rfl` again; do **not** reach for `decide`, which would want a
`DecidableEq FinSetSkel` this plan never supplies. If that also fails,
report to the orchestrator and drop the assertion — the instance
resolutions above are the test's substance and stand without it. If
`sampleTensorObj` fails to close by `rfl`, `2 * 3` is not reducing to
`6` under `prodObj`; use `by decide` or `by simp [prodObj]` and
report.

Run: `lake build GebTests`, `lake test`, `lake lint -- GebTests`
Expected: PASS.

- [ ] **Step 5: commit**

Run: `bash scripts/lint-imports.sh`, `lake build`, `lake test`,
`lake lint`, `lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the coproduct cocones and finite coproducts"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 10: row m — monomorphisms are injective vectors

Spec sections: § Row m, § Row m is the adapter between `Mono` and the
inversion, § Every route through `incl` is choice-tainted.

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Mono.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Mono.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` and its
  `GebTests` parallel

**Interfaces:**

- Consumes: Task 5's `point`, `point_get`, `hom_ext`, `comp_get`;
  `CategoryTheory.Mono`, `Mono.right_cancellation`,
  `Function.Injective`.
- Produces:
  `FinSetSkel.mono_iff_injective {X Y : FinSetSkel.{u}} {f : X ⟶ Y} :
  Mono f ↔ Function.Injective f.toVec.get`. Consumed by Tasks 17
  and 18.

The route through `FinSetSkel.incl` and
`ConcreteCategory.mono_iff_injective_of_preservesPullback` is not
taken: `incl` itself measures
`[propext, Classical.choice, Quot.sound]`, so every route through it
is tainted whatever lemma is applied, and the spec places row m in
the choice-free layer. `Functor.mono_map_iff_mono` depending on no
axioms does not change this — it is a polymorphic constant whose
functor argument carries the taint. This module is **not**
allowlisted.

- [ ] **Step 1: create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core

/-!
# Monomorphisms of `FinSetSkel`

A morphism is a monomorphism exactly when its vector is injective.
`CategoryTheory.Mono` and `CategoryTheory.Category` are both
axiom-free, so the statement belongs in the choice-free layer, and
the proof is direct over vectors: the forward direction tests a
morphism against two points, and the reverse is `hom_ext`.

This is the hypothesis `Vector.invOfInjective` takes, so the row is a
prerequisite of the subobject classifier rather than a free-standing
characterisation.

## Main statements

* `FinSetSkel.mono_iff_injective` — monomorphisms are the morphisms
  with injective vectors.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, monomorphism, injective
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

end FinSetSkel
```

- [ ] **Step 2: state the theorem unproved**

```lean
/-- A morphism is a monomorphism exactly when its vector is
injective. -/
theorem mono_iff_injective {X Y : FinSetSkel.{u}} {f : X ⟶ Y} :
    Mono f ↔ Function.Injective f.toVec.get := _
```

Run: `lake build`
Expected: FAIL, one placeholder error showing the goal.

- [ ] **Step 3: prove it**

```lean
  constructor
  · intro hm i j hij
    have h : point i ≫ f = point j ≫ f :=
      hom_ext fun t ↦ by rw [comp_get, comp_get, point_get, point_get, hij]
    have hp : (point i : mk 1 ⟶ X) = point j := (cancel_mono f).mp h
    have := congrArg (fun m ↦ (m : mk 1 ⟶ X).toVec.get 0) hp
    simpa only [point_get] using this
  · intro hinj
    constructor
    intro Z g h hgh
    exact hom_ext fun t ↦ hinj (by
      have := congrArg (fun m ↦ (m : Z ⟶ Y).toVec.get t) hgh
      simpa only [comp_get] using this)
```

`cancel_mono` is mathlib's `f ≫ g = h ≫ g ↔ f = h` under `[Mono g]`;
if its exact form differs, use `hm.right_cancellation` directly. The
index `0 : Fin (mk 1).len` is the unique index of the one-element
object. Prove one direction at a time and re-check the goal between
them, per `docs/rules/lean-coding.md` § Proof guidelines.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: check the axioms, test, wire and commit**

Measure `mono_iff_injective` and a monomorphic witness:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeMonoHom : (mk 2 : FinSetSkel.{0}) ⟶ mk 3 :=
  Hom.ofVec (Vector.ofFnC fun i : Fin 2 ↦ (⟨i.val, by omega⟩ : Fin 3))

/-- Monomorphic witness for the axiom measurement. -/
theorem probeMono : Mono probeMonoHom ↔ Function.Injective probeMonoHom.toVec.get :=
  mono_iff_injective
```

The witness is a `theorem`, its statement being an `Iff`, and its
type carries no `_`: an underscore in a written type is the
placeholder `docs/rules/lean-coding.md` § sorry, admit, and
underscores treats as an unfilled hole. Expected:
`[propext, Quot.sound]`. Delete both afterwards, then run the
banned-form grep.

The test parallel names a sample injective morphism and applies
`mono_iff_injective` to obtain `Mono` for it. State the injectivity
hypothesis in the decidable form
`∀ i j : Fin 2, v.get i = v.get j → i = j`, close that by `decide`
over the axiom-free `DecidableEq (Fin n)`, and feed it to
`mono_iff_injective` through `Function.Injective`'s definition.
Do **not** write `by decide` against `Function.Injective f.toVec.get`
directly: `Function.Injective` is a non-reducible `def`, so instance
search never reaches a quantifier instance, and if it did the route
would be `Fintype.decidableForallFintype`, which constraint 9 bans
and which this test module is not allowlisted for.

Add the module to the two `FinSetSkel.lean` index files.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): characterise monomorphisms as injective vectors"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 11: row g's core — the exponential equivalence and its naturality

Spec sections: § Row g (the `Exponential/Core.lean` paragraphs),
§ `Equiv`'s domain transport is choice-tainted.

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean`
- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`
- Modify: the two `FinSetSkel.lean` index files

**Interfaces:**

- Consumes: Tasks 1, 2, 3, 4, 5; `Equiv.curry`, `Equiv.piComm`,
  `Equiv.piCongrRight`.
- Produces, in namespace `FinSetSkel`: `expEquivIdx`,
  `expEquivIdx_apply`, `expEquivIdx_naturality`, `expEquivHom`.
  Consumed by Task 13.

**This module exports exactly those four names** and mentions no
monoidal vocabulary: `⊗` and `◁` elaborate through the
choice-tainted `CartesianMonoidalCategory` instance and would take
the module out of the choice-free layer. `expEquivIdx_apply` is the
one addition to the spec's list of three, being the unfolding lemma
both the naturality proof and Task 13 rewrite with; it is not an
intermediate equivalence, which the spec rules out.

- [ ] **Step 1: create the module**

Imports: `Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core`,
`Geb.Mathlib.Logic.Equiv.Fin.Basic`,
`Geb.Mathlib.Logic.Equiv.Basic`, `Geb.Mathlib.Data.Fin.Basic`.
Module docstring:

```lean
/-!
# The exponential of `FinSetSkel`, over carriers

The exponential object of `Fin m` into `Fin y` is `Fin (y ^ m)`, and
the adjunction's hom-level equivalence is the chain

`(Fin (m * z) → Fin y) ≃ (Fin m × Fin z → Fin y) ≃
 (Fin m → Fin z → Fin y) ≃ (Fin z → Fin m → Fin y) ≃
 (Fin z → Fin (y ^ m))`

stated here over the raw carrier and the explicit projections of the
binary product, never over `⊗` or `◁`: those elaborate through the
`CartesianMonoidalCategory` instance, which depends on
`Classical.choice`. The monoidal restatement is in
`Exponential/Closed.lean`.

Two steps are not the obvious spelling. The domain transport is
`Equiv.arrowCongrLeftC`, mathlib's `Equiv.arrowCongr` and
`Equiv.piCongrLeft` family all depending on `Classical.choice`. The
swap is required because the adjunction `tensorLeft X ⊣ ihom X`
varies in the parameter `Z`, so the result must be a function of
`Fin z`, while `X ⊗ Z` places `X` first and `Equiv.curry` therefore
produces `Fin m` outermost. It is a consequence of which factor the
adjunction is taken in, not of which digit `Fin.pairC` makes high.

## Main definitions

* `FinSetSkel.expEquivIdx` — the hom-level equivalence over index
  functions.
* `FinSetSkel.expEquivHom` — the same over morphisms.

## Main statements

* `FinSetSkel.expEquivIdx_naturality` — naturality in the
  parameter, the whole mathematical content of the exponential's
  universal property.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, exponential, closed, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

end FinSetSkel
```

- [ ] **Step 2: add the equivalence and its unfolding lemma**

```lean
/-- The exponential's hom-level equivalence, over index functions:
the exponent object has length `m`, the parameter object length `z`
and the target length `y`. -/
def expEquivIdx (m z y : ℕ) : (Fin (m * z) → Fin y) ≃ (Fin z → Fin (y ^ m)) :=
  ((((Equiv.arrowCongrLeftC (γ := Fin y) (finProdFinEquivC (m := m) (n := z)).symm).trans
      (Equiv.curry (Fin m) (Fin z) (Fin y))).trans
      (Equiv.piComm fun _ : Fin m ↦ fun _ : Fin z ↦ Fin y)).trans
    (Equiv.piCongrRight fun _ ↦ finFunctionFinEquivC)

/-- The exponential's equivalence encodes, for each parameter index,
the function obtained by fixing it. -/
theorem expEquivIdx_apply (m z y : ℕ) (g : Fin (m * z) → Fin y)
    (t : Fin z) :
    expEquivIdx m z y g t = Fin.funEncodeC (fun a ↦ g (Fin.pairC a t)) := rfl
```

The chain was elaborated at this toolchain in exactly this
association and measured `[propext, Quot.sound]` over the two
encodings.

Mind the letters: `finFunctionFinEquivC {m n}` reads codomain-first,
so the `finFunctionFinEquivC` at the end of this chain is
instantiated at codomain `Fin (y ^ m)`'s exponent — that is, at its
own `m := y` and `n := m` — while `expEquivIdx m z y` reads
exponent, parameter, target. The two conventions collide on the
letter `m`, deliberately: the encoding keeps the roles of the
`finFunctionFinEquiv` it rebuilds, per Task 4's Interfaces.

If `rfl` does not close `expEquivIdx_apply`, unfold with
`simp only [expEquivIdx, Equiv.trans_apply, Equiv.arrowCongrLeftC,
Equiv.curry, Equiv.piComm, Equiv.piCongrRight, Fin.funEncodeC]`,
expecting to need `Equiv.coe_fn_mk` alongside them: those names are
`def`s, so unfolding them exposes a coerced `Equiv.mk` application
rather than a reduced term. Report what was needed to the
orchestrator — the lemma is the interface both later proofs use, so it
is worth the unfolding once here.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: state and prove naturality**

```lean
/-- Naturality of the exponential's equivalence in the parameter,
where `φ` is the index function of a morphism into the parameter
object. -/
theorem expEquivIdx_naturality (m z' z y : ℕ) (φ : Fin z' → Fin z)
    (g : Fin (m * z) → Fin y) :
    expEquivIdx m z' y
        (fun i ↦ g (Fin.pairC (Fin.divNatC i) (φ (Fin.modNatC i)))) =
      expEquivIdx m z y g ∘ φ := by
  funext t
  simp only [expEquivIdx_apply, Function.comp_apply, Fin.divNatC_pairC,
    Fin.modNatC_pairC]
```

At `t`, the left side encodes
`fun a ↦ g (pairC (divNatC (pairC a t)) (φ (modNatC (pairC a t))))`
and the two round trips of Task 2 reduce it to
`fun a ↦ g (pairC a (φ t))`, which is what the right side encodes.
This is the whole mathematical content of the exponential's universal
property, and it is stated here rather than in the wrapper: a
naturality equation stated over `◁` would put the content in an
allowlisted module.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add the morphism-level equivalence**

```lean
/-- The exponential's hom-level equivalence, over morphisms. -/
def expEquivHom (m z y : ℕ) :
    ((mk (m * z) : FinSetSkel.{u}) ⟶ mk y) ≃ ((mk z : FinSetSkel.{u}) ⟶ mk (y ^ m)) :=
  (homEquivIdxFun (mk (m * z)) (mk y)).trans
    ((expEquivIdx m z y).trans (homEquivIdxFun (mk z) (mk (y ^ m))).symm)
```

The object `mk (m * z)` is named directly; no `⊗` appears. There is
no hom-level naturality statement here: Task 13 derives that form
from `expEquivIdx_naturality` through the whiskering bridge, so an
intermediate would be stated twice and used once.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: check the axioms, test, wire and commit**

Measure the four declarations and a monomorphic witness:

Append to `Exponential/Core.lean`, measure, then delete:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeExp : Fin 2 → Fin (3 ^ 2) := expEquivIdx 2 2 3 (fun _ ↦ 0)
```

Expected: `[propext, Quot.sound]`. A `Classical.choice` here means
`Equiv.arrowCongr` or a `piCongrLeft` entered in place of
`Equiv.arrowCongrLeftC`. Delete the witness; run the banned-form grep.

`probeExp` is measured in the source module even though the permanent
witness below covers the same declarations transitively: it isolates
`expEquivIdx` from `homEquivIdxFun`, so a `Classical.choice` is
attributed to the chain rather than to the correspondence, and it is
measured under this module's own imports rather than the test
parallel's.

The test parallel encodes a sample two-argument function and asserts
the encoded value by `rfl` or `decide`, then applies
`expEquivIdx_naturality` at a sample `φ`. That parallel —
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean` —
also carries this module's **permanent** axiom witness, which Task 12
re-measures by name and which is therefore not deleted:

```lean
/-- Permanent monomorphic witness for this module's axiom set. -/
def sampleExpEquivHom : (mk 2 : FinSetSkel.{0}) ⟶ mk (3 ^ 2) :=
  expEquivHom 2 2 3 (Hom.ofVec (Vector.ofFnC fun _ ↦ 0))
```

It is built from `expEquivHom`, not from `expEquivIdx`: only
`expEquivHom` mentions `FinSetSkel` at all, and it is the declaration
that could acquire `Classical.choice` — through `homEquivIdxFun` and
whatever instance a later import brings — so it is the one worth
watching. Measuring it covers `expEquivIdx` and `homEquivIdxFun`
transitively, since it is their composite. A `def`, not a `theorem`:
a theorem would measure its proof's axioms rather than the data's.

Create the two `Exponential.lean` index files, importing `Core` now
and `Closed` in Task 12, and add them to the two `FinSetSkel.lean`
index files.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the exponential equivalence over carriers"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 12: the whiskering bridge

Spec section: § Row g (wrapper piece 1), which sizes this as the
largest single proof obligation in W3 and gives it its own task.

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Closed.lean`
- Modify: `GebMeta.lean`,
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`

**Interfaces:**

- Consumes: Task 7 (`prodFst`, `prodSnd`, `prodLift`, `prodFst_get`,
  `prodSnd_get`, `prodLift_get`, `prodLift_uniq`), Task 8
  (`cartesianMonoidalCategory`, without which `⊗` and `◁` do not
  elaborate), Task 11 (nothing directly — the import is for the module
  this one extends); `CartesianMonoidalCategory.whiskerLeft_fst`,
  `CartesianMonoidalCategory.whiskerLeft_snd`,
  `MonoidalCategory.whiskerLeft`, and W1's `comp_get` and `hom_ext`.
- Produces: `FinSetSkel.whiskerLeft_get`. Consumed by Task 13.

- [ ] **Step 1: allowlist both module names**

Append to `classicalAllowedModules` in `GebMeta.lean`:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
```

Both now, although Task 13 is where the `GebTests` module is created:
`classicalAllowedModules` is a `NameSet` the linter matches
declarations against, so a name with no module is inert, and Task 13
runs `lake lint -- GebTests` over a test module that resolves
`MonoidalClosed FinSetSkel` and is therefore `Classical.choice`-
tainted. Leaving that name to Task 13 would mean a task whose Files
list says `GebMeta.lean` but whose steps never edit it, and its
executor has not read this task.

- [ ] **Step 2: create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Core
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances

/-!
# `FinSetSkel` is monoidal closed

The monoidal packaging of `Exponential/Core.lean`. `Closed X` has
exactly the two fields `rightAdj` and `adj`, and `MonoidalClosed C`
exactly the one field `closed`, so `Adjunction.rightAdjointOfEquiv`
and `Adjunction.adjunctionOfEquivRight` supply the functor, the unit,
the counit and the triangle identities, and none is constructed by
hand.

`X ⊗ Z` is the object of length `X.len * Z.len` on the nose, the
monoidal structure having come from
`CartesianMonoidalCategory.ofChosenFiniteProducts` fed with the
chosen binary product cones, so restating the equivalence at
`X ⊗ Z ⟶ Y` transports along a definitional equality rather than a
comparison isomorphism.

The whiskering bridge is what connects the carrier-level naturality
of `Exponential/Core.lean` to `F.map f`: left whiskering acts on
indices by pairing the first component with the whiskered morphism's
action on the second. It is stated here rather than in the core
because `◁` elaborates through the `CartesianMonoidalCategory`
instance, which depends on `Classical.choice`.

## Main definitions

* `FinSetSkel.expHomEquiv` — the exponential's hom-level
  equivalence, in the form the adjunction consumes.
* `FinSetSkel.monoidalClosed` — the monoidal closed structure.

## Main statements

* `FinSetSkel.whiskerLeft_get` — the action of left whiskering on
  indices.
* `FinSetSkel.expHomEquiv_naturality` — naturality of that
  equivalence in the parameter.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, exponential, monoidal closed
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace FinSetSkel

end FinSetSkel
```

The docstring is written whole here, so Task 13 adds no section to
it: the three declarations it names besides `whiskerLeft_get` —
`expHomEquiv`, `expHomEquiv_naturality` and `monoidalClosed` — arrive
in that task. The commit closing this task therefore ships a docstring
naming constants the module does not yet contain, which nothing lints
and which Task 13 completes. `Exponential/Closed.lean` depends on `Shapes/Instances.lean`
and not only on `Exponential/Core.lean`, because the cartesian
instance its statements mention is declared there.

`Mathlib.CategoryTheory.Monoidal.Closed.Basic` is **not** imported
here: nothing in this task mentions `Closed` or `MonoidalClosed`, and
`lake shake` at Task 19 would reject the import. Task 13 adds it when
it adds the declarations that need it, and does not additionally
import `Mathlib.CategoryTheory.Adjunction.Basic`, which
`Monoidal/Closed/Basic.lean` already brings.

- [ ] **Step 3: confirm the projections are the chosen ones**

```lean
example (X Y : FinSetSkel.{u}) :
    (SemiCartesianMonoidalCategory.fst X Y) = prodFst X Y := rfl

example (X Y : FinSetSkel.{u}) :
    (SemiCartesianMonoidalCategory.snd X Y) = prodSnd X Y := rfl
```

`ofChosenFiniteProducts` sets `fst` and `snd` from the chosen cone,
which is `BinaryFan.mk (prodFst X Y) (prodSnd X Y)`, so both should
be `rfl`. If either fails, the bridge below must rewrite with the
cartesian structure's own lemma relating them instead; report which.
Delete the two `example`s once they pass.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: state the bridge unproved**

```lean
/-- Left whiskering acts on indices by pairing the first component
with the whiskered morphism's action on the second. -/
theorem whiskerLeft_get (X : FinSetSkel.{u}) {Y Z : FinSetSkel.{u}}
    (f : Y ⟶ Z) (i : Fin (X ⊗ Y).len) :
    (X ◁ f).toVec.get i =
      Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i)) := _
```

`(X ⊗ Y).len` reduces to `X.len * Y.len`, so `Fin.divNatC i : Fin
X.len` and `Fin.modNatC i : Fin Y.len` typecheck without ascription.
Confirm that before proceeding; if they do not, ascribe `i`'s type as
`Fin (prodObj X Y).len` and report the divergence to the orchestrator.

Run: `lake build`
Expected: FAIL, one placeholder error.

- [ ] **Step 5: prove it**

The route: identify `X ◁ f` as the lift of the two composites, then
read off its indices.

```lean
  have h : (X ◁ f) = prodLift (prodFst X Y) (prodSnd X Y ≫ f) :=
    prodLift_uniq _ _ _
      (CartesianMonoidalCategory.whiskerLeft_fst X f)
      (CartesianMonoidalCategory.whiskerLeft_snd X f)
  rw [h, prodLift_get, comp_get, prodFst_get, prodSnd_get]
```

`rw` matches at `instances` transparency, and the goal's index has
type `Fin (X ⊗ Y).len` where `prodLift_get` and the two projection
lemmas are stated at `Fin (prodObj X Y).len`; the two agree only
through the cartesian instance and `ofChosenFiniteProducts`. If the
chain reports no occurrence of a pattern, insert
`change (prodLift (prodFst X Y) (prodSnd X Y ≫ f)).toVec.get i = _`
after `rw [h]`, or state `whiskerLeft_get` over
`Fin (prodObj X Y).len` from the start and let Step 4's statement
change with it. This is Step 4's elaboration hedge one layer down.

`whiskerLeft_fst X f : X ◁ f ≫ fst X Z = fst X Y` and
`whiskerLeft_snd X f : X ◁ f ≫ snd X Z = snd X Y ≫ f`; with Step 3's
two `rfl`s those are exactly `prodLift_uniq`'s two hypotheses. This
lemma is what connects the core's `φ`-shaped equation to mathlib's
`F.map f`.

If `prodLift_uniq` will not accept the whiskering lemmas because
`fst`/`snd` do not display as `prodFst`/`prodSnd`, insert `change`
steps converting each hypothesis, or state two bridging lemmas
`fst_eq_prodFst` and `snd_eq_prodSnd` by `rfl` and rewrite with them.
Prove one hypothesis at a time and re-check the goal, per
`docs/rules/lean-coding.md` § Proof guidelines.

Run: `lake build`
Expected: PASS.

- [ ] **Step 6: check the axioms and commit**

Measure `whiskerLeft_get`. Expected:
`[propext, Classical.choice, Quot.sound]` — the whiskering is the
cartesian structure's, and this is the allowlisted wrapper. Confirm
that `Exponential/Core.lean` is unchanged by re-measuring its
permanent witness `sampleExpEquivHom`, in
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean`.
Expected: `[propext, Quot.sound]`.

Add `public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed`
to `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`, which
Task 11 Step 5 created carrying `Core` alone. The `GebTests` index
gains its parallel line in Task 13, with the test module it names.

This task writes no test: the module's `GebTests` parallel is created
in Task 13, which tests both tasks' declarations together.

Run: `bash scripts/lint-imports.sh`, `lake build`, `lake lint`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): bridge left whiskering to the pairing on indices"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 13: the monoidal-closed structure

Spec section: § Row g (wrapper pieces 2 and 3), § Exported names.

**Files:**

- Modify:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Closed.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential/Closed.lean`
- Modify:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`
- Conditionally modify:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean`, only
  on the Step 1 fallback below

`GebMeta.lean` needs no edit here: Task 12 Step 1 appended both
`Exponential.Closed` names, this module's and its `GebTests`
parallel's.

**Interfaces:**

- Consumes: Tasks 8 (`cartesianMonoidalCategory`, without which
  neither `⊗` nor `MonoidalClosed FinSetSkel` elaborates), 5
  (`homEquivIdxFun_apply : homEquivIdxFun X Y f i = f.toVec.get i` and
  `homEquivIdxFun_symm_get :
  ((homEquivIdxFun X Y).symm g).toVec.get i = g i`), 11
  (`expEquivIdx_naturality`, whose statement Task 11 gives) and 12
  (`whiskerLeft_get : (X ◁ f).toVec.get i =
  Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i))`, together
  with W1's `comp_get : (f ≫ g).toVec.get i =
  g.toVec.get (f.toVec.get i)` — these two fix the shape `harg` must
  produce);
  `Adjunction.rightAdjointOfEquiv`,
  `Adjunction.adjunctionOfEquivRight`, `Closed`, `MonoidalClosed`,
  `MonoidalCategory.tensorLeft`.
- Produces: `FinSetSkel.expHomEquiv`,
  `FinSetSkel.expHomEquiv_naturality` and
  `FinSetSkel.monoidalClosed`, which is W5's `closed` field. No
  separate `FinSetSkel.closed` — see Step 4.

W2's `closed` field has type
`@MonoidalClosed C _ cartesian.toMonoidalCategory`, so it is
well-typed only when W5's `cartesian` is the same term W3 stated its
`MonoidalClosed` over. `monoidalClosed` is therefore stated with
`cartesianMonoidalCategory` in scope as the only
`CartesianMonoidalCategory FinSetSkel` instance, which Task 8
guarantees. This is the single place where two routes to the same
data would fail to typecheck rather than merely diverge.

- [ ] **Step 1: add the import, then restate the equivalence at
`X ⊗ Z ⟶ Y`**

Add `public import Mathlib.CategoryTheory.Monoidal.Closed.Basic` to
`Exponential/Closed.lean`, which Task 12 left out because nothing in
that task mentioned `Closed` or `MonoidalClosed`.

```lean
/-- The exponential's hom-level equivalence, in the form
`adjunctionOfEquivRight` consumes. -/
def expHomEquiv (X : FinSetSkel.{u}) (Z Y : FinSetSkel.{u}) :
    ((tensorLeft X).obj Z ⟶ Y) ≃ (Z ⟶ mk (Y.len ^ X.len)) :=
  expEquivHom X.len Z.len Y.len
```

`(tensorLeft X).obj Z` is `X ⊗ Z`, which is `mk (X.len * Z.len)` on
the nose, and `Y` is `mk Y.len` on the nose by the eta rule for the
one-field structure.

**If the ascription is not accepted, stop and report.** Do not insert
a cast or a comparison isomorphism — that would contradict the spec's
§ Row g, which states the transport is along a definitional equality.
And do not restate `expEquivHom` over objects instead of lengths:
every later step of this task is written against the length-indexed
form (`expEquivHom X.len Z.len Y.len` here, `harg` and
`expEquivIdx_naturality X.len Z'.len Z.len Y.len …` in Step 3), that
module is Task 11's and already committed, and an executor who took
the edit would then be following a recipe that no longer typechecks.
Leave the work uncommitted and report to the orchestrator; the
restatement, if it is needed, is a change to Task 11 and to this
task's Step 3 together, and belongs to whoever holds both.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: state the naturality `adjunctionOfEquivRight`
requires, unproved**

```lean
/-- Naturality of the exponential's equivalence, in the form
`Adjunction.adjunctionOfEquivRight` consumes. -/
theorem expHomEquiv_naturality (X : FinSetSkel.{u})
    (Z' Z Y : FinSetSkel.{u}) (f : Z' ⟶ Z) (g : (tensorLeft X).obj Z ⟶ Y) :
    expHomEquiv X Z' Y ((tensorLeft X).map f ≫ g) =
      f ≫ expHomEquiv X Z Y g := _
```

Run: `lake build`
Expected: FAIL, one placeholder error.

- [ ] **Step 3: prove it from the core equation through the bridge**

Route, in three moves:

1. The left side's *argument* is rewritten into the `φ`-shaped
   function of `expEquivIdx_naturality`, with `φ := f.toVec.get`.
   `(tensorLeft X).map f` must first become `X ◁ f`, or
   `whiskerLeft_get` cannot fire: `tensorLeft` is
   `abbrev tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X`, so
   the term is `((curriedTensor C).obj X).map f`, which is not
   syntactically `X ◁ f`, and `simp only` will not unfold a
   `Functor.map` projection on its own. `curriedTensor` is `@[simps]`,
   so `curriedTensor_obj_map` is the bridge; `comp_get` and
   `whiskerLeft_get` then finish the argument.
2. `ext t` reduces the two morphisms to index lookups at each
   `t : Fin Z'.len`, and the correspondence lemmas move both sides
   through `homEquivIdxFun`.
3. `expEquivIdx_naturality X.len Z'.len Z.len Y.len f.toVec.get …`,
   read at `t`, closes it.

Move 1 comes first, not second, and that ordering is the point.

The proof, in two stages. A single `simp only` cannot do it, for a
reason worth stating: after `ext t` the term
`homEquivIdxFun … ((tensorLeft X).map f ≫ g)` sits **unapplied**, as
`expEquivIdx`'s function argument, and `homEquivIdxFun_apply`,
`comp_get` and `whiskerLeft_get` are all applied-form equations.
`simp only` will not eta-expand a function occurrence to make such a
lemma fire. So the argument is bridged under a `funext` first, where
both sides *are* applied:

```lean
  have harg :
      homEquivIdxFun (mk (X.len * Z'.len)) (mk Y.len) ((tensorLeft X).map f ≫ g)
        = fun i ↦ (homEquivIdxFun (mk (X.len * Z.len)) (mk Y.len) g)
            (Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i))) := by
    funext i
    simp only [homEquivIdxFun_apply, curriedTensor_obj_map, comp_get,
      whiskerLeft_get]
  ext t
  simp only [expHomEquiv, expEquivHom, Equiv.trans_apply,
    homEquivIdxFun_symm_get, comp_get, harg]
  exact congrFun (expEquivIdx_naturality X.len Z'.len Z.len Y.len f.toVec.get
    (homEquivIdxFun (mk (X.len * Z.len)) (mk Y.len) g)) t
```

Four entries of the second set are there for reasons that are not
obvious. `expHomEquiv` and `expEquivHom` are plain `def`s with no
`@[simp]` unfolding lemma, so without them nothing opens the term up;
`simp only` uses their equation lemmas. `Equiv.trans_apply` is needed
because `expEquivHom` is a nested `Equiv.trans`, which
`homEquivIdxFun_symm_get` does not match; it is `@[simp]` in mathlib,
but `simp only` does not load the default set. And `harg` is the
bridge above. If the goal displays the coerced form instead,
`Equiv.coe_trans` and `Function.comp_apply` are the alternates; and if
`harg` does not fire at all, the goal is presenting the objects as
`(tensorLeft X).obj Z'` — re-add `curriedTensor_obj_obj` to this outer
set. Its absence is deliberate, that equation being unnecessary once
the two `def`s unfold, but a silent no-progress is the failure mode
worth pre-empting.

`curriedTensor_obj_map` belongs to the **inner** set only. Keeping it
out of the outer one is what leaves `(tensorLeft X).map f ≫ g`
verbatim in the outer goal, so that `harg`'s left-hand side still
matches it; rewriting it there first would break the match.

Do **not** try to close the residue by `rfl` or by adding
`expEquivIdx_apply` to the first set: `(X ◁ f ≫ g).toVec.get i` is not
definitionally `g.toVec.get (Fin.pairC …)` — `whiskerLeft_get` is
Task 12's theorem, proved through `prodLift_uniq` — and routing
around `expEquivIdx_naturality` would leave Task 11's stated
deliverable with no consumer.

`whiskerLeft_get` and `expEquivIdx_naturality` carry no `@[simp]`, so
they are named explicitly here and a bare `simp` will not find them.
Expect the goal to need re-checking between moves; if the recipe
stalls, factor an intermediate lemma per
`docs/rules/lean-coding.md` § Proof guidelines, stating the left
side's rewritten form, and prove the two halves separately.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add `Closed` and `MonoidalClosed`**

```lean
/-- `FinSetSkel` is monoidal closed: the exponential of the object of
length `X.len` into the object of length `Y.len` is the object of
length `Y.len ^ X.len`. -/
instance monoidalClosed : MonoidalClosed FinSetSkel.{u} where
  closed X :=
    { rightAdj :=
        Adjunction.rightAdjointOfEquiv (expHomEquiv X) (expHomEquiv_naturality X)
      adj :=
        Adjunction.adjunctionOfEquivRight (expHomEquiv X)
          (expHomEquiv_naturality X) }
```

`adj`'s two arguments are named rather than left as `_ _`. They are
recoverable by unification against `rightAdj` one line above, but
naming them costs nothing and localises any future breakage.

One declaration, not two. A separate `instance closed (X) : Closed X`
alongside this one would give instance search two routes to
`Closed X`, since `MonoidalClosed.closed` is itself
`@[instance_reducible, instance 100]` with default
`by infer_instance`; constraint 9's rule against leaving two
inhabitants of one class to search applies, and here the cheaper fix
is to declare only the one the spec's § Exported names names.

`Adjunction.rightAdjointOfEquiv` takes the object map implicitly
through `G_obj`; the object map here is
`fun Y ↦ mk (Y.len ^ X.len)`, which the type of `expHomEquiv` fixes.
Confirm the field names of `Closed` (`rightAdj`, `adj`) and of
`MonoidalClosed` (`closed`) with `#check` before writing them.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: confirm W5's field type accepts this term**

This is the one place the plan identifies where two routes to the
same data would fail to typecheck rather than merely diverge, so it
gets a probe rather than an assertion:

```lean
example : @MonoidalClosed FinSetSkel.{u} _
    (FinSetSkel.cartesianMonoidalCategory.{u}).toMonoidalCategory :=
  monoidalClosed
```

That is W2's `closed` field type with W5's `cartesian` filled by this
workstream's instance. The instance path Lean finds for
`MonoidalCategory FinSetSkel` runs
`CartesianMonoidalCategory → SemiCartesianMonoidalCategory →
MonoidalCategory`, two `extends` hops, while W2's field names the
one-hop `cartesian.toMonoidalCategory`; if those do not coincide, the
failure belongs here rather than in W5. Delete the `example` once it
passes. If it fails, stop: leave the work uncommitted and report to
the orchestrator, since the divergence is between W2's field type and
this instance and is not this task's to resolve.

Run: `lake build`
Expected: PASS.

- [ ] **Step 6: check the axioms, test and commit**

Measure `expHomEquiv`, `expHomEquiv_naturality` and
`monoidalClosed`. Expected: axioms **contained in**
`{propext, Classical.choice, Quot.sound}` — the allowlisted wrapper
permits `Classical.choice` without requiring it, and `expHomEquiv` is
`expEquivHom` at the lengths, whose core is choice-free, so it may
measure `[propext, Quot.sound]`. A tighter set is not a discrepancy;
a wider one is.

The test parallel resolves `MonoidalClosed FinSetSkel.{0}` by
`inferInstance` into a named `def`, and asserts the exponential
object's length: `((ihom (mk 2 : FinSetSkel.{0})).obj (mk 3)) = mk 9`
by `rfl` if `ihom` reduces, otherwise state the equality through
`Closed.rightAdj`. Report which form was used.

Add `import GebTests.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed`
to `GebTests/Mathlib/CategoryTheory/FinSetSkel/Exponential.lean`,
which Task 11 Step 5 created carrying `Core` alone. Without that line
the test module is imported by nothing and `lake test` passes without
running it — a silent coverage hole rather than a build error.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the monoidal closed structure"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 14: row h's data path and its two fold lemmas

Spec section: § Row h. The spec sizes the fold-correctness lemma with
Task 12's whiskering bridge, and this task is the pair's second half.

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean`
- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`

The source index is created here, not deferred: `lake lint` audits
only what a root import reaches, so leaving this module unwired for a
commit would mean committing it unaudited by the axiom linter. The
two `GebTests` files are Task 15's, that side having nothing to import
until its test module exists.

**Interfaces:**

- Consumes: W1's morphism API; `List.finRange`, `List.filter`,
  `List.mem_filter`, `List.mem_finRange`, `List.nodup_finRange`,
  `List.Nodup.filter`, `List.zipIdx`, `List.foldl`,
  `Vector.replicate`, `Vector.set`, `Vector.get`, `Vector.ofFnC`.
- Produces, in namespace `FinSetSkel.Equalizer`: `agreePred`,
  `agree`, `agree_nodup`, `mem_agree_iff`, `obj`, `injVec`, `ι`,
  `injVec_get_mem`, `scatter`, `scatter_nil`, `scatter_cons`,
  `get_scatter_of_not_mem`, `get_scatter_mem`, `invVec`,
  `invVec_lt`. Consumed by Tasks 15 and 16 — Task 16's cone applies
  `Equalizer.ι` and, through `LimitCone (parallelPair f g)`,
  `Equalizer.obj`.

The namespace is `FinSetSkel.Equalizer`, tracking the module, so that
`agree`, `obj` and `ι` do not sit in `FinSetSkel`, where W4 and W5
also declare.

This row does **not** consume W1's `Fin.compressEquiv`, and the
module imports neither it nor
`Geb/Mathlib/Data/List/NodupEquivFin.lean`: that equivalence's
`toFun` is `l.get i` and its `invFun` is `l.idxOf ↑x`, linear in the
index and in the list length, so routing the injection through it
costs `Θ(k²)` with the equivalence shared and
`Θ(k · X.len + k²)` without, and the lift through its `invFun` costs
`Θ(Z.len · k)`. The construction below is linear in `X.len` for the
injection and the inverse, and `Θ(Z.len)` for the lift. `TODO.md`
§ FinSetSkel as an elementary topos chooses root `Vector` over
`List.Vector` on exactly this ground; a quadratic equalizer would
contradict that premise inside the same group.

- [ ] **Step 1: create the module**

Imports: `Geb.Mathlib.CategoryTheory.FinSetSkel.Basic`,
`Geb.Mathlib.Data.Vector.OfFn`, `Mathlib.Data.List.FinRange`.
`Shapes/Core.lean` is **not** imported: row h states nothing over
index functions, and an unused import fails `lake shake`. Confirm
that at Task 19's `lake shake` and add the import only if it reports
one missing.

Module docstring, carrying the two persistent decisions § Documentation
requires of this module:

```lean
/-!
# Binary equalizers of `FinSetSkel`

The equalizer of `f g : X ⟶ Y` is the sub-object on the indices at
which they agree: the list `(List.finRange X.len).filter p` for the
decidable predicate `p i = decide (f.toVec.get i = g.toVec.get i)`,
and the object of its length.

The inverse of the injection is built as a vector of `ℕ`, not of
`Fin k`: `Vector (Fin k) X.len` is uninhabited whenever `k = 0` and
`X.len > 0`, and that case is reachable — any `f g : mk 3 ⟶ mk 2`
differing at every index gives `k = 0`. `Vector.replicate` needs an
inhabitant, and `0 : ℕ` is one where no `Fin k` is. The `Fin k` is
built at the lift site, where the agreement of the index is
available and the bound lemma applies.

The agreement list and the inverse vector are bound outside anything
function-valued. A definition whose result is a function re-runs a
`let` above its lambda on every application of the partially applied
function, while the same `let` in a definition returning a value runs
once; the constraint is invisible in the source, and a refactor
lifting the vector construction into a function-returning helper
would break it silently.

## Main definitions

* `FinSetSkel.Equalizer.agree` — the indices at which a parallel
  pair agrees.
* `FinSetSkel.Equalizer.obj`, `FinSetSkel.Equalizer.ι` — the
  equalizer object and its injection.
* `FinSetSkel.Equalizer.scatter` — the one-pass inverse fold.
* `FinSetSkel.Equalizer.lift` — the factorisation.

## Main statements

* `FinSetSkel.Equalizer.get_scatter_mem`,
  `FinSetSkel.Equalizer.get_scatter_of_not_mem` — the fold's
  correctness.
* `FinSetSkel.Equalizer.ι_comp`, `FinSetSkel.Equalizer.lift_ι`,
  `FinSetSkel.Equalizer.lift_uniq` — the universal property.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, equalizer, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel.Equalizer

end FinSetSkel.Equalizer
```

The docstring is written whole here, including the `## Main statements`
entries for `ι_comp`, `lift_ι` and `lift_uniq`, which arrive in
Task 15. That task adds no section to it. The commit closing this task
therefore ships a docstring naming constants the module does not yet
contain, which nothing lints.

- [ ] **Step 2: add the predicate, the agreement list and the object**

```lean
variable {X Y : FinSetSkel.{u}}

/-- The predicate deciding where a parallel pair agrees. -/
def agreePred (f g : X ⟶ Y) (i : Fin X.len) : Bool :=
  decide (f.toVec.get i = g.toVec.get i)

/-- The indices at which a parallel pair agrees, in order. -/
def agree (f g : X ⟶ Y) : List (Fin X.len) :=
  (List.finRange X.len).filter (agreePred f g)

/-- The agreement list has no repetitions. -/
theorem agree_nodup (f g : X ⟶ Y) : (agree f g).Nodup :=
  (List.nodup_finRange X.len).filter _

/-- Membership in the agreement list is agreement. -/
theorem mem_agree_iff (f g : X ⟶ Y) (j : Fin X.len) :
    j ∈ agree f g ↔ agreePred f g j = true := by
  simp [agree, List.mem_filter, List.mem_finRange]

/-- The equalizer object: the length of the agreement list. -/
def obj (f g : X ⟶ Y) : FinSetSkel.{u} := mk (agree f g).length
```

`decide` over the axiom-free `DecidableEq (Fin n)`;
`Fintype.decidableForallFintype` is not reached, no quantifier being
decided here. `List.Nodup.filter`'s argument order and
`List.mem_finRange`'s exact form are the two to confirm with
`#check`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: add the injection**

```lean
/-- The injection vector, the agreement list as a vector. -/
def injVec (f g : X ⟶ Y) : Vector (Fin X.len) (obj f g).len :=
  ⟨(agree f g).toArray, by simp [obj]⟩

/-- The injection morphism. -/
def ι (f g : X ⟶ Y) : obj f g ⟶ X := Hom.ofVec (injVec f g)

/-- Every entry of the injection is an agreeing index. -/
theorem injVec_get_mem (f g : X ⟶ Y) (i : Fin (obj f g).len) :
    (injVec f g).get i ∈ agree f g := by
  simp [injVec, Vector.get_eq_getElem]
```

The injection is built from the list directly, not by
`Vector.ofFnC` over an index lookup: `List.toArray` is the one-pass
form. This was measured monomorphically at `[propext]`.

`simp`, not `simpa … using List.getElem_mem _`. The bridge out of the
vector — `Vector.getElem_mk` then `List.getElem_toArray`, both
`@[simp]` — and `List.getElem_mem` itself are all in the default simp
set, so `simp` closes the goal alone, and supplying the `using` term
then trips `linter.unnecessarySimpa`, which
`weak.warningAsError = true` turns into a build failure. Measured at
this toolchain on this shape: `simp [Vector.get_eq_getElem]` closes it
with no diagnostics and the `simpa` form fails the linter; `injVec` is
in the simp set above because the goal must first unfold to the
underlying list. Note
that `Vector.getElem_toArray` is *not* the applicable lemma — it goes
from a `Vector`'s array back to the `Vector`, where `injVec f g` is a
`Vector.mk` over a *`List`*'s array.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add the scatter fold and its unfolding lemmas**

```lean
/-- One pass writing each list entry's position into a vector,
generalised over the starting vector and the starting counter. -/
def scatter {n : ℕ} (L : List (Fin n)) (c : ℕ) (v : Vector ℕ n) :
    Vector ℕ n :=
  (L.zipIdx c).foldl (fun w (j, k) ↦ w.set j.val k j.isLt) v

/-- The empty pass changes nothing. -/
@[simp] theorem scatter_nil {n : ℕ} (c : ℕ) (v : Vector ℕ n) :
    scatter [] c v = v := rfl

/-- One step of the pass writes the head's position and continues on
the tail with the counter advanced. -/
theorem scatter_cons {n : ℕ} (j : Fin n) (L : List (Fin n)) (c : ℕ)
    (v : Vector ℕ n) :
    scatter (j :: L) c v = scatter L (c + 1) (v.set j.val c j.isLt) := by
  simp [scatter, List.zipIdx_cons]
```

`j.isLt` discharges the `Vector.set` bound `j.val < n` directly, and
is the same term `scatter_cons` writes below. This text was measured
with `(by omega)` in that position, which also works — `omega` reads
`Fin` bounds — and the two are equal by proof irrelevance; the direct
term is preferred, being cheaper and immune to a change in omega's
preprocessing. `List.zipIdx_cons` states
`(a :: as).zipIdx n = (a, n) :: as.zipIdx (n + 1)`; confirm the name
and the `+ 1` convention with `#check`. If `zipIdx` counts the other
way at this revision, the whole design of the counter changes:
**stop**, leave the work uncommitted, and report to the orchestrator.
Do not improvise a replacement convention — Steps 5, 6 and 7's lemmas
are all written against this one.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: state the two fold lemmas unproved**

```lean
/-- The pass leaves untouched every index the list does not
mention. -/
theorem get_scatter_of_not_mem {n : ℕ} (L : List (Fin n)) (j : Fin n)
    (hj : j ∉ L) (c : ℕ) (v : Vector ℕ n) :
    (scatter L c v).get j = v.get j := _

/-- The pass writes each listed index's position, offset by the
starting counter. -/
theorem get_scatter_mem {n : ℕ} (L : List (Fin n)) (hnd : L.Nodup)
    (c : ℕ) (v : Vector ℕ n) (j : Fin n) (k : ℕ)
    (h : (j, k) ∈ L.zipIdx c) : (scatter L c v).get j = k := _
```

Both are generalised over the starting vector and the starting
counter, and the second carries the `Nodup` hypothesis. Both
generalisations are forced, not stylistic. `List.rec` decomposes
head-first, so a motive pinned to `Vector.replicate X.len 0` and to
absolute positions is not a valid one: the recursive call speaks of
the tail, renumbered from the advanced counter, over whatever vector
the head's `set` produced. And the invariant is false without
duplicate-freeness — `Vector.set` lets a later occurrence overwrite
an earlier one.

Run: `lake build`
Expected: FAIL, two placeholder errors.

- [ ] **Step 6: prove them by explicit `List.rec`**

The `induction` tactic is forbidden
(`docs/rules/lean-coding.md` § Recursion and induction through
recursors). The shape is

```lean
  L.rec (motive := fun L ↦ ∀ (c : ℕ) (v : Vector ℕ n), j ∉ L →
      (scatter L c v).get j = v.get j)
    (fun _ _ _ ↦ rfl)
    (fun a L ih c v hj ↦ by
      rw [scatter_cons, ih (c + 1) _ (fun hm ↦ hj (List.mem_cons_of_mem a hm))]
      simp only [Vector.get_eq_getElem]
      exact Vector.getElem_set_ne a.isLt j.isLt
        (fun he ↦ hj (Fin.ext he ▸ List.mem_cons_self ..)))
    c v hj
```

Two spellings matter here. Root `Vector` has `getElem_set_ne` and
`getElem_set_self`, **not** `get_set_ne` and `get_set_self` — the
`get_` forms exist only for `List.Vector` — so the step goes through
W1's `rfl` bridge `Vector.get_eq_getElem`, and the disequality
`getElem_set_ne` takes is between the two `Nat` indices, which is why
`Fin.ext` lifts it. The whole of this proof, `scatter`, `scatter_nil` and `scatter_cons`
included, was elaborated verbatim at this toolchain: the `▸` resolves
because the expected type is `False`, and
`Vector.getElem_set_ne`'s signature is
`(hi : i < n) (hj : j < n) (h : i ≠ j)`. `List.mem_cons_self`'s
binders have moved between explicit and implicit across recent core
releases, so `#check` it in the module before relying on the `..`.

for the first, with the hypotheses moved into the motive so that the
recursion may re-instantiate them, and analogously for the second,
whose motive is
`fun L ↦ L.Nodup → ∀ c v k, (j, k) ∈ L.zipIdx c →
(scatter L c v).get j = k` and whose cons case splits on whether the
head is `j`:

- head is `j`: then `k = c`, the tail pass leaves the written entry
  alone by `get_scatter_of_not_mem`, and `Vector.getElem_set_self`
  finishes. Deriving `k = c` is the branch's one non-mechanical step.
  `List.zipIdx_cons` splits the membership into `(j, k) = (j, c)` and
  `(j, k) ∈ L.zipIdx (c + 1)`; the second is killed by `Nodup`, which
  gives `j ∉ L`, once `j ∈ L` is extracted from membership **at
  counter `c + 1`**. Step 7's `List.mk_mem_zipIdx_iff_getElem?` is the
  `c = 0` specialisation and does not serve here. Core's
  `List.fst_mem_of_mem_zipIdx` does, at any counter:

  ```lean
  theorem List.fst_mem_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat}
      (h : x ∈ zipIdx l k) : x.1 ∈ l
  ```

  applied at `x := (j, k)`, whose `.1` is `j` by `rfl`. Confirm with
  `#check` and use it; no lemma of W3's own is needed here.
- head is not `j`: the membership passes to the tail and `ih`
  applies, `Vector.getElem_set_ne` discharging the write.

`Vector.getElem_set_self` and `Vector.getElem_set_ne` are the two
names to confirm, through `Vector.get_eq_getElem` as above. Prove the
first lemma completely before starting the second: it is a hypothesis
of the second's head case.

Run: `lake build`
Expected: PASS.

- [ ] **Step 7: add the inverse vector and the bound lemma**

```lean
/-- The inverse of the injection, as positions in the agreement
list; entries at non-agreeing indices are unconstrained. -/
def invVec (f g : X ⟶ Y) : Vector ℕ X.len :=
  scatter (agree f g) 0 (Vector.replicate X.len 0)

/-- At an agreeing index the inverse is a position in the agreement
list. -/
theorem invVec_lt (f g : X ⟶ Y) (j : Fin X.len)
    (hj : agreePred f g j = true) : (invVec f g).get j < (obj f g).len := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem ((mem_agree_iff f g j).mpr hj)
  have hlen : (obj f g).len = (agree f g).length := rfl
  have : (invVec f g).get j = k :=
    get_scatter_mem _ (agree_nodup f g) 0 _ j k
      ((List.mk_mem_zipIdx_iff_getElem?).mpr (by
        rw [List.getElem?_eq_getElem hk, hget]))
  omega
```

Two things this step needs and does not get for free. `omega`
atomises `(obj f g).len` and `(agree f g).length` separately — it
will not delta-unfold `obj` — so `hlen` must be in context before it
runs. And the `getElem?` side goal is closed by
`rw [List.getElem?_eq_getElem hk, hget]`, not by `simp [hget]`:
`hget` is about `l[k]` and the goal about `l[k]?`, and simp's
discharger will not use `hk` to fire the conditional
`List.getElem?_eq_getElem`. Measured at this toolchain —
`simp [hget]` reports "made no progress" on exactly this shape.

The bridge from `(agree f g)[k] = j` to
`(j, k) ∈ (agree f g).zipIdx 0` is core's
`List.mk_mem_zipIdx_iff_getElem?`, stated through `getElem?` rather
than `getElem`, which is why the side goal needs the `rw` above.
`#check` it and adjust to whatever its actual form needs. Note it is
the `c = 0` specialisation — exactly this call site, but
`get_scatter_mem` is stated for general `c`, so a later consumer at
nonzero `c` needs `List.mk_add_mem_zipIdx_iff_getElem?` instead. If
it is absent at this revision, prove the bridge as a named lemma by
`List.rec` in the shape of Step 6 and add it to this module's
exports.

Run: `lake build`
Expected: PASS.

- [ ] **Step 8: check the axioms, wire the source index and commit**

Measure every declaration, plus monomorphic witnesses at
`FinSetSkel.{0}`:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeInj : Vector (Fin 5)
    (obj (Hom.ofVec (Vector.ofFnC fun _ : Fin 5 ↦ (0 : Fin 2)))
      (Hom.ofVec (Vector.ofFnC fun i : Fin 5 ↦ (⟨i.val % 2, by omega⟩ : Fin 2)))).len :=
  injVec _ _

/-- Monomorphic witness for the axiom measurement. -/
def probeInv : Vector ℕ 5 :=
  invVec (Hom.ofVec (Vector.ofFnC fun _ : Fin 5 ↦ (0 : Fin 2)))
    (Hom.ofVec (Vector.ofFnC fun i : Fin 5 ↦ (⟨i.val % 2, by omega⟩ : Fin 2)))
```

Expected: `[propext]` for the injection, `[propext, Quot.sound]` for
the inverse — the shapes measured whole at this toolchain. Delete
both after measuring, then run the banned-form grep: `Vector.replicate`
and `Vector.set` are permitted, `Vector.ofFn` and `Vector.finRange`
are not, and `List.finRange` is a different declaration and is
permitted.

Then wire the source side, without which `lake lint` cannot audit
this module at all: create
`Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer.lean` carrying
`public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Core`,
on the pattern of Task 2 Step 6, and add
`public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer` to
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean`. Task 16 adds the
`Limits` line to the same index; Task 15 creates the two `GebTests`
files.

Run: `bash scripts/lint-imports.sh`, `lake build`, `lake lint`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the equalizer's data path and fold lemmas"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 15: row h's universal property

Spec section: § Row h, § Verification obligations (9).

**Files:**

- Modify:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`

**Interfaces:**

- Consumes: Task 14.
- Produces, in namespace `FinSetSkel.Equalizer`: `ι_comp`,
  `injVec_get_invVec`, `lift`, `lift_ι`, `lift_uniq`. Consumed by
  Task 16. A helper factored out of
  `lift_uniq` (`injVec_injective`) or out of `invVec_lt` is a further
  export of the module if it is stated at all; see Steps 2 and 4.

- [ ] **Step 1: prove the equalising equation**

```lean
/-- The injection equalises the pair. -/
theorem ι_comp (f g : X ⟶ Y) : ι f g ≫ f = ι f g ≫ g :=
  hom_ext fun i ↦ by
    have h := (mem_agree_iff f g _).mp (injVec_get_mem f g i)
    simpa [ι, agreePred] using of_decide_eq_true h
```

`of_decide_eq_true` converts the `Bool` agreement back to the
equality; the `simpa` must also rewrite `(ι f g).toVec.get i` to
`(injVec f g).get i` through `Hom.toVec_ofVec`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: prove that the inverse inverts the injection**

```lean
/-- At an agreeing index, the injection recovers the index from its
position. -/
theorem injVec_get_invVec (f g : X ⟶ Y) (j : Fin X.len)
    (hj : agreePred f g j = true) :
    (injVec f g).get ⟨(invVec f g).get j, invVec_lt f g j hj⟩ = j := _
```

Route: `List.getElem_of_mem` gives `k` and `(agree f g)[k] = j`, the
computation inside `invVec_lt` gives `(invVec f g).get j = k`, and
`injVec`'s entries are the list's by `Vector.getElem_mk` and
`List.getElem_toArray`, both `@[simp]`. Factor
the `(invVec f g).get j = k` step out of `invVec_lt` into its own
named lemma if proving it twice — once there, once here — becomes
awkward; that lemma is then a further export of Task 14, and if it is
stated it is added to `Equalizer/Core.lean`'s `## Main statements`,
which Task 14 wrote.

Run: `lake build`
Expected: PASS once the routes above are written; before them, FAIL
with one placeholder error per `_`.

- [ ] **Step 3: add the lift**

```lean
/-- The factorisation of a morphism equalising the pair. -/
def lift (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) : Z ⟶ obj f g :=
  let inv := invVec f g
  Hom.ofVec (Vector.ofFnC fun t ↦
    ⟨inv.get (h.toVec.get t), invVec_lt f g _ (by
      simp only [agreePred, decide_eq_true_eq]
      simpa using congrArg (fun m ↦ (m : Z ⟶ Y).toVec.get t) w)⟩)
```

The `let` is above the lambda and `lift` returns a value, so the
inverse pass runs once per `lift` application rather than once per
index. The agreement of `h.toVec.get t` comes from `w` through
`comp_get`.

`Vector.ofFnC`, never `Vector.ofFn`: the two differ only in their
lemmas, so a construction using the banned form still measures clean
and fails `lake lint` only once a `simp` meets it.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: prove the factorisation and its uniqueness**

```lean
/-- The lift followed by the injection is the original morphism. -/
@[simp] theorem lift_ι (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) : lift f g h w ≫ ι f g = h := _

/-- Any morphism factoring through the injection is the lift. -/
theorem lift_uniq (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) (m : Z ⟶ obj f g) (hm : m ≫ ι f g = h) :
    m = lift f g h w := _
```

`lift_ι` is `hom_ext` at `t` followed by `injVec_get_invVec`.
`lift_uniq` needs the injection's injectivity: two positions with the
same entry are equal, from `agree_nodup` through
`List.Nodup.getElem_inj_iff` or `List.nodup_iff_injective_get` — the
same step W1 takes in `Vector.invOfInjective`, whose proof is the
model to follow. State the injectivity as a named lemma
`injVec_injective` if the proof of `lift_uniq` needs it twice; if
stated, add it to `Equalizer/Core.lean`'s `## Main statements`, which
Task 14 wrote.

Run: `lake build`
Expected: PASS once the routes above are written; before them, FAIL
with one placeholder error per `_`.

- [ ] **Step 5: check the axioms**

Measure the five declarations this task adds, and the lift at a
monomorphic witness — `lift` is the one that computes, and the one
whose bound proof reaches into the `Nat` API:

```lean
/-- Monomorphic witness for the axiom measurement. -/
def probeLiftHom : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- Monomorphic witness for the axiom measurement. -/
def probeLift : (mk 5 : FinSetSkel.{0}) ⟶ obj probeLiftHom probeLiftHom :=
  lift probeLiftHom probeLiftHom (𝟙 (mk 5)) rfl
```

Expected: `[propext, Quot.sound]`. Delete both at the end of Step 6,
whose grep confirms their removal — Step 6's own snippet is
self-contained and uses neither. Run the banned-form grep now: `lift`
is the declaration most likely to reach for `Vector.ofFn` by habit.

- [ ] **Step 6: measure let-sharing, subject against control**

Verification obligation 9 wants the let-sharing property established
by measurement rather than by reading the source, because it is a
property of the code generator. This step does that in one
`lean_run_code` snippet, **touching no file in the repository**.

The snippet carries two definitions of the same shape as `lift`, one
value-returning and one function-returning, over a traced stand-in for
the inverse pass, and evaluates both:

```lean
import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic

structure Box where v : List Nat

/-- Stand-in for the inverse pass, traced. -/
def scatterish (n : Nat) : List Nat :=
  dbgTrace "PASS RAN" fun _ ↦ List.replicate n 7

/-- Subject: `lift`'s shape — `let` after all binders, returns a value. -/
def liftVal (n : Nat) : Box :=
  let inv := scatterish n
  ⟨(List.range 5).map (fun t ↦ inv.getD t 0)⟩

/-- Control: the same `let` in a function-returning definition. -/
def liftFun (n : Nat) : Nat → Nat :=
  let inv := scatterish n
  fun t ↦ inv.getD t 0

#eval (liftVal 5).v
#eval (List.range 5).map (liftFun 5)
```

Run it through the `lean-lsp` MCP's `lean_run_code`; `dbgTrace` output
from `#eval` is captured into the message log as an `info` diagnostic,
so it comes back in the result, and the two `#eval`s return separate
diagnostics so the counts are attributable.

The import is `FinSetSkel.Basic`, a module W3 never edits — **not**
`Equalizer.Core`, which Steps 1 through 5 have just modified and which
Step 5 deliberately leaves two probe declarations in. The snippet
defines everything it measures, so it needs nothing from either; what
it must not do is make the measurement fail because the module under
edit does not build.

Expected: **one** `PASS RAN` from the first `#eval` and **five** from
the second. Each `#eval` also returns
`` `#`-commands, such as '#eval', are not allowed in 'Mathlib' `` at
`info` severity; that is the repo's `linter.hashCommand` and is
expected, not instrument breakage. This whole snippet elaborates with
zero errors and zero warnings at this toolchain.

The control is the point of the step. One trace from the subject alone
is equally consistent with sharing and with the measurement having
collapsed — the term folded at elaboration, the value cached, the
trace firing for an unrelated reason — so a run that does not also
produce the five is a **broken instrument, not a pass**. Report it as
such and proceed; do not record a sharing result from a run whose
control did not fire.

- **1 and 5**: the property holds at this toolchain. `lift` is
  value-returning with its `let` after every binder, so it is in the
  sharing shape, and Task 14's module docstring records the property.
- **1 and 1**, or **5 and 5**: the code generator no longer
  distinguishes the two shapes. Report it — Task 14's docstring
  asserts the distinction and would need rewriting, which is not this
  task's to do.

This step adds nothing to `Equalizer/Core.lean`, so it has nothing to
revert. What does still need removing is Step 5's, not this step's:
delete the two witnesses (`probeLiftHom`, `probeLift`) before Step 7
commits, and confirm with

```bash
grep -n "probeLift\|dbgTrace\|#eval" \
  Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean
```

expecting no match: a probe left in an upstream-eligible module builds
cleanly, measures clean and passes `lint-imports.sh`, so nothing else
catches it (verification obligation 8).

This replaces an earlier design that edited the module — adding a
traced copy of the inverse pass, redirecting `lift` at it, adding an
in-module `#eval`, building, then reverting all three. That measured a
redirected `lift` rather than the deliverable, so it measured a copy
either way, and it cost three edits to an upstream-eligible
choice-free module plus a build and a revert for the same evidence.

**Row g's `Fin.funDecodeC` gets no separate check**, and that is a
departure from the spec's obligation 9, which names it as the other
candidate. It returns `Fin n → Fin m`, so re-running per application
is its *expected* behaviour; the plan's own conclusion is that this is
harmless, nothing in W3 applying a partially applied `funDecodeC` in a
loop; and the control above already establishes the general property
at exactly that shape. A measurement whose outcome is predicted, whose
finding is pre-declared harmless, and which has no consumer, is cost
without return. Report the departure with the finished plan.

- [ ] **Step 7: write the test parallel and commit**

Create
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean`. It
computes an equalizer at a concrete pair: two morphisms
`mk 5 ⟶ mk 2` agreeing at three indices, the object's length
asserted to be `3` by `rfl` or `decide`, the injection's vector
asserted, and `lift_ι` exercised at a sample morphism. Name the
equalizer's injection **`sampleEqualizerInj`**: it is this module's
permanent axiom witness, which Task 16 re-measures by that name, so it
must be a monomorphic `def` at `FinSetSkel.{0}` and must not be
deleted.

Create `GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer.lean`
importing this task's test module, and add it to
`GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`. The source side was
wired in Task 14; only the `GebTests` half is deferred here, that
index having had nothing to import until now.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the equalizer's universal property"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 16: the equalizer wrapper

Spec section: § Row h (the wrapper paragraph).

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean`
- Modify: `GebMeta.lean`, the two `Equalizer.lean` index files

**Interfaces:**

- Consumes: Tasks 14 and 15; `LimitCone`, `Fork.ofι`,
  `Fork.IsLimit.mk`, `parallelPair`, `Fork.condition`, `Fork.ι`.
- Produces:
  `FinSetSkel.equalizerCone {X Y : FinSetSkel.{u}} (f g : X ⟶ Y) :
  LimitCone (parallelPair f g)`, W5's `equalizerCone` field.

`Equalizer/Limits.lean` depends on `Equalizer/Core.lean` only:
`LimitCone (parallelPair f g)` mentions no cartesian or monoidal
structure, and an unused import of `Shapes/Instances.lean` would fail
`lake shake`.

`HasEqualizers` is **not** registered: nothing in W3 consumes it,
constraint 5 names only `HasFiniteCoproducts` and `HasCoequalizers`
as later-workstream consumers, and W2 derives it generically from the
class. Rows a and c's `HasInitial` and `HasBinaryCoproducts` are
registered in Task 9 because they are the hypotheses of
`hasFiniteCoproducts_of_has_binary_and_initial`, which row e applies.

- [ ] **Step 1: allowlist, then create the module**

Append to `classicalAllowedModules` in `GebMeta.lean` first:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
```

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Core
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The equalizer cone of `FinSetSkel`

The mathlib packaging of `Equalizer/Core.lean`: the agreement
sub-object, its injection and its factorisation as a
`LimitCone (parallelPair f g)`. `LimitCone` and `parallelPair` depend
on `Classical.choice`, so this module is allowlisted and the
construction it packages is not.

`HasEqualizers` is not registered: nothing in this workstream
consumes it, and it is one of the `Prop` classes derived once from
`ElementaryTopos`.

## Main definitions

* `FinSetSkel.equalizerCone` — the chosen equalizer cone.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, equalizer, limit cone
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- The chosen equalizer cone. -/
def equalizerCone {X Y : FinSetSkel.{u}} (f g : X ⟶ Y) :
    LimitCone (parallelPair f g) where
  cone := Fork.ofι (Equalizer.ι f g) (Equalizer.ι_comp f g)
  isLimit :=
    Fork.IsLimit.mk _ (fun s ↦ Equalizer.lift f g s.ι s.condition)
      (fun s ↦ Equalizer.lift_ι f g s.ι s.condition)
      (fun s m hm ↦ Equalizer.lift_uniq f g s.ι s.condition m hm)

end FinSetSkel
```

The module qualifies `Equalizer.` rather than opening it: inside
`namespace FinSetSkel`, `open Equalizer` would draw the sub-namespace
in and a bare `ι` or `lift` would then read ambiguously against
mathlib's `Limits` names. `Fork.condition` is `s.ι ≫ f = s.ι ≫ g`,
which is exactly `lift`'s hypothesis; confirm the direction with
`#check`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: check the axioms, test, wire and commit**

Create
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean`
first, so that this step has a monomorphic witness to measure:

```lean
/-- A sample morphism, constant at index `0`. -/
def sampleF : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- Permanent monomorphic witness for this module's axiom set. -/
def sampleEqualizerCone : LimitCone (parallelPair sampleF sampleF) :=
  equalizerCone sampleF sampleF

/-- The equalizer of a morphism with itself is its whole domain. -/
theorem sampleEqualizerCone_pt : sampleEqualizerCone.cone.pt = mk 5 := by
  rfl
```

The pair is `sampleF` against itself, so every index agrees and the
cone's point is `mk 5`; if the `rfl` does not close, `decide` on the
lengths is the fallback, and report which was needed. Then measure
`equalizerCone` and `sampleEqualizerCone`. Expected:
`[propext, Classical.choice, Quot.sound]` — `LimitCone` and
`parallelPair` bring the taint, which is why the module is
allowlisted. Confirm `Equalizer/Core.lean` is unchanged by
re-measuring its permanent witness `sampleEqualizerInj`, in
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean`.
Expected: `[propext, Quot.sound]`.

Create
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean`; it
names the cone at a concrete pair and asserts its point's length.

Add `public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits`
to `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer.lean`, and the
plain-`import` parallel for the test module to its `GebTests`
counterpart; Task 14 created the source index and Task 15 Step 7 the
`GebTests` one, both carrying `Core` alone.
Without these lines neither module is reachable from a root import,
so `lake build` still compiles them through lake's glob while
`lake lint` never audits them — green, and unchecked.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): package the equalizer as a limit cone"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 17: row l's core — the characteristic vector and the inversion

Spec sections: § Row l, § The classifier consumes the W1 inversion,
§ `truth` is index 1.

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Core.lean`
- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier.lean` and
  its `GebTests` parallel
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Classifier/Core.lean`
- Modify: the two `FinSetSkel.lean` index files

**Interfaces:**

- Consumes: Task 10's `mono_iff_injective`; Task 5's `Hom.ofVec`,
  `hom_ext`, `comp_get` (W1's, re-exported through `Mono.lean`); W1's
  `Vector.invOfInjective` from
  `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`; `Vector.replicate`,
  `Vector.set`, `Vector.ofFnC`, `Vector.get_eq_getElem`,
  `Vector.getElem_replicate`, `Equiv.apply_symm_apply`,
  `List.getElem_mem`.
- Produces, in namespace `FinSetSkel.Classifier`: `scatterOne`,
  `get_scatterOne_eq_one`, `get_scatterOne_eq_one_of`,
  `get_scatterOne_of_mem`, `chiVec`,
  `chiVec_get_eq_one_iff`, `chi`, `chi_get`, `invOfInjective_apply`,
  `pullbackLift`, `pullbackLift_comp`, `pullbackLift_uniq`,
  `chi_comp_eq`, `chi_uniq`. Consumed by Task 18.

`Classifier/Core.lean` has its own module rather than sitting in
`Mono.lean`, whose subject is row m. Whether it imports
`Shapes/Core.lean` is settled by `lake shake` at Task 19: row l's
core states nothing over index functions, but Task 18 needs `point`,
and `point` lives in `Shapes/Core.lean`.

`χ` is scattered rather than written as
`Vector.ofFnC (fun j ↦ if m.toVec.toList.contains j then 1 else 0)`:
the latter rebuilds and scans the list per index, costing
`Θ(X.len · U.len)`. `χ` is a data field of `Subobject.Classifier`,
not a `Prop`, so it computes and W5 exposes it, and row h's
complexity discipline applies to it identically. Scattering also
avoids `List.contains` and with it any `LawfulBEq (Fin n)` search,
whose instance is choice-tainted.

- [ ] **Step 1: create the module**

Imports: `Geb.Mathlib.CategoryTheory.FinSetSkel.Mono`,
`Geb.Mathlib.Data.Vector.NodupEquivFin`,
`Geb.Mathlib.Data.Vector.OfFn`.

Module docstring, carrying the orientation decision § Documentation
requires of this module:

```lean
/-!
# The subobject classifier of `FinSetSkel`, over vectors

The classifying object is the object of length 2 and the
characteristic morphism of a monomorphism sends the members of its
image to `1` and everything else to `0`. `truth` picks the index `1`
in `Classifier/Instance.lean`; the two modules fix the orientation
jointly and each states it.

The orientation follows mathlib's own: `finTwoEquiv` is
`fun i ↦ i == 1`, and `Presheaf.truth` and `Sheaf.truth`, the two
classifier instances mathlib builds, both pick the maximal sieve.
With `truth = 1` the characteristic morphism is the indicator of
membership and every bridge to `Bool`, `decide` or `Prop` is
`finTwoEquiv` composed with nothing; with `truth = 0` each such
bridge carries a negation and the normal forms on the two sides stop
matching.

The characteristic vector is scattered in one pass over a
`Vector.replicate`, not written index-by-index over a membership
test, which would rebuild and rescan the image per index.

## Main definitions

* `FinSetSkel.Classifier.chi` — the characteristic morphism.
* `FinSetSkel.Classifier.pullbackLift` — the factorisation through a
  monomorphism of a morphism whose image it contains.

## Main statements

* `FinSetSkel.Classifier.get_scatterOne_eq_one`,
  `FinSetSkel.Classifier.get_scatterOne_eq_one_of` — the pass writes
  `1` at the listed indices and nowhere else.
* `FinSetSkel.Classifier.chiVec_get_eq_one_iff` — the characteristic
  vector is the indicator of the image.
* `FinSetSkel.Classifier.chi_uniq` — a morphism with the same
  indicator is the characteristic morphism.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, subobject classifier, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel.Classifier

end FinSetSkel.Classifier
```

- [ ] **Step 2: add the scatter and its three lemmas**

```lean
/-- One pass writing `1` at each listed index, generalised over the
starting vector. -/
def scatterOne {n : ℕ} (L : List (Fin n)) (v : Vector (Fin 2) n) :
    Vector (Fin 2) n :=
  L.foldl (fun w j ↦ w.set j.val 1 j.isLt) v

/-- The pass writes `1` only at listed indices. -/
theorem get_scatterOne_eq_one {n : ℕ} (L : List (Fin n)) (j : Fin n)
    (v : Vector (Fin 2) n) (h : (scatterOne L v).get j = 1) :
    j ∈ L ∨ v.get j = 1 := _

/-- The pass writes `1` at every listed index, and preserves a `1`
already present. -/
theorem get_scatterOne_eq_one_of {n : ℕ} (L : List (Fin n))
    (j : Fin n) (v : Vector (Fin 2) n) (h : j ∈ L ∨ v.get j = 1) :
    (scatterOne L v).get j = 1 := _

/-- The pass writes `1` at every listed index. -/
theorem get_scatterOne_of_mem {n : ℕ} (L : List (Fin n)) (j : Fin n)
    (hj : j ∈ L) (v : Vector (Fin 2) n) : (scatterOne L v).get j = 1 :=
  get_scatterOne_eq_one_of L j v (Or.inl hj)
```

The first two by explicit `List.rec` — the `induction` tactic is
forbidden by § Global constraints — with the starting vector and the
hypothesis inside the motive, so the recursion may re-instantiate
them. The third is a corollary. The skeleton, for the first:

```lean
  L.rec (motive := fun L ↦ ∀ (v : Vector (Fin 2) n),
      (scatterOne L v).get j = 1 → j ∈ L ∨ v.get j = 1)
    (fun v h ↦ Or.inr h)
    (fun a L ih v h ↦ _)
    v h
```

and for the second the same shape at the motive
`fun L ↦ ∀ (v : Vector (Fin 2) n), j ∈ L ∨ v.get j = 1 →
(scatterOne L v).get j = 1` — but **not** the same base case. There the
base goal is `∀ v, j ∈ [] ∨ v.get j = 1 → (scatterOne [] v).get j = 1`,
whose conclusion reduces to `v.get j = 1` by `List.foldl`'s iota rule,
and which `Or.inr h` does not inhabit; it is

```lean
    (fun v h ↦ h.resolve_left List.not_mem_nil)
```

`List.not_mem_nil` has its argument implicit at this revision, so none
is passed, and `Or.resolve_left : a ∨ b → ¬a → b`. Direction one's
`fun v h ↦ Or.inr h` is right because `scatterOne [] v` reduces to `v`
by `List.foldl`'s iota rule. Each cons case rewrites by `scatterOne`'s
cons identity — `scatterOne (a :: L) v = scatterOne L (v.set a.val 1
a.isLt)`, which holds by `List.foldl_cons` — and then splits as
described below.

Both directions split on `a.val = j.val` through the axiom-free
`Nat.decEq`, never on list membership: where equal,
`Vector.getElem_set_self` supplies the right disjunct for the
inductive hypothesis; where not, `Vector.getElem_set_ne` transports
the hypothesis through the write.

The second is stated in this strengthened form because
`get_scatterOne_of_mem` is **not** provable directly by `List.rec`.
Its cons case splits `j ∈ a :: L` by `List.mem_cons`, and the branch
`j = a` leaves the goal
`(scatterOne L (v.set a.val 1 _)).get j = 1` with no `j ∈ L` in hand,
so the inductive hypothesis does not apply. Task 14's corresponding
lemma escapes that branch through its `Nodup` hypothesis, which gives
it `j ∉ L`; this one has no `Nodup` (see below) and would have to
decide `j ∈ L` instead, reaching `List.instDecidableMemOfLawfulBEq`
and with it the choice-tainted `LawfulBEq (Fin n)`. Carrying `v.get j
= 1` as an alternative disjunct closes the branch with no decision at
all.

That pair is what keeps this module choice-free, and it is not
optional. Without them `chiVec_get_eq_one_iff` would be proved by
`by_contra` or by `decide` on `j ∈ m.toVec.toList`, and the only
`Decidable (a ∈ as)` for lists in Lean core is
`instance [BEq α] [LawfulBEq α] …`, which routes through the
`LawfulBEq (Fin n)` the spec's § `LawfulBEq` at `Fin n` measured at
`[propext, Classical.choice, Quot.sound]`. Which instance search
returns depends on the module's import set, so the route is not
reliably clean and constraint 9's own rule applies: where two routes
inhabit one class and only one is choice-free, name the term rather
than leave search to pick. Stating the third lemma removes the class
from the proof altogether, which is cheaper than pinning an instance
W3 has decided not to supply (decision 7).

This lemma pair carries **no counter and no `Nodup` hypothesis**,
where row h's carries both. Verification obligation 4 asks for "the
generalised form § Row h describes, over an arbitrary starting vector
and counter and under a `Nodup` hypothesis"; the reading taken here
is § Row l's "in the shape row h's takes", generalised over the
starting vector alone. The counter does not exist in this
construction — the value written is the constant `1`, not a
position — and duplicate-freeness is not needed, `Vector.set`
overwriting `1` with `1` being harmless. Adding either would be dead
weight against `CONTRIBUTING.md` § Code is cost. Three independent
adversarial reviewers examined this reading and judged the
mathematics sound — with duplicates present, both statements still
hold, because `Vector.set` overwriting `1` with `1` changes nothing
and there is no position to renumber. This reading was reported to the
user with the finished plan and stands; **implement the three lemmas
as stated**. Reopening it — adding a counter and a `Nodup`
hypothesis — is not this task's to decide.

Run: `lake build`
Expected: PASS after the proofs; FAIL with two placeholder errors
before them.

- [ ] **Step 3: add the characteristic vector and morphism**

```lean
variable {U X : FinSetSkel.{u}}

/-- The characteristic vector of a monomorphism: `1` on its image,
`0` elsewhere. -/
def chiVec (m : U ⟶ X) : Vector (Fin 2) X.len :=
  scatterOne m.toVec.toList (Vector.replicate X.len 0)

/-- The characteristic morphism of a monomorphism. -/
def chi (m : U ⟶ X) : X ⟶ mk 2 := Hom.ofVec (chiVec m)

/-- The characteristic morphism looks up the characteristic
vector. -/
@[simp] theorem chi_get (m : U ⟶ X) (j : Fin X.len) :
    (chi m).toVec.get j = (chiVec m).get j := rfl

/-- The characteristic vector is the indicator of the image. -/
theorem chiVec_get_eq_one_iff (m : U ⟶ X) (j : Fin X.len) :
    (chiVec m).get j = 1 ↔ j ∈ m.toVec.toList := by
  constructor
  · intro h
    refine (get_scatterOne_eq_one _ _ _ h).resolve_right ?_
    simp only [Vector.get_eq_getElem, Vector.getElem_replicate]
    decide
  · intro hj
    exact get_scatterOne_of_mem _ _ hj _
```

Both applications of the fold lemmas must unify
`(scatterOne ?L ?v).get ?j` against `(chiVec m).get j`, which unfolds
the non-reducible `def chiVec` at default transparency. That should
succeed; if either stalls, `simp only [chiVec]` first.

Neither direction decides membership, so neither reaches
`Decidable (· ∈ ·)` and its `LawfulBEq (Fin n)`. The `decide` that
remains closes `(0 : Fin 2) ≠ 1` over the axiom-free
`instDecidableEqFin`, on a closed term with no quantifier, so
`Fintype.decidableForallFintype` is not reached either.

`Vector.get_replicate` does not exist for root `Vector` — the only
`get_replicate` in mathlib is `List.Vector`'s. Core supplies
`Vector.getElem_replicate`, reached through W1's `rfl` bridge
`Vector.get_eq_getElem`, as Task 14 Step 6 also does for the `set`
lemmas.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add the inversion's application lemma and the lift**

```lean
/-- The inversion of an injective vector recovers the vector's
lookup. -/
theorem invOfInjective_apply {n k : ℕ} (v : Vector (Fin n) k)
    (h : Function.Injective v.get) (i : Fin k) :
    ((Vector.invOfInjective v h) i).val = v.get i := _

/-- The factorisation through a monomorphism of a morphism whose
image it contains. -/
def pullbackLift (m : U ⟶ X) (hm : Function.Injective m.toVec.get)
    {Z : FinSetSkel.{u}} (z : Z ⟶ X)
    (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) : Z ⟶ U :=
  let e := Vector.invOfInjective m.toVec hm
  Hom.ofVec (Vector.ofFnC fun t ↦ e.symm ⟨z.toVec.get t, hz t⟩)

/-- The factorisation composes back to the original morphism. -/
theorem pullbackLift_comp (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) :
    pullbackLift m hm z hz ≫ m = z := _

/-- The factorisation through a monomorphism is unique. -/
theorem pullbackLift_uniq (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList)
    (n : Z ⟶ U) (hn : n ≫ m = z) : n = pullbackLift m hm z hz := _
```

`Vector.invOfInjective v h : Fin k ≃ {j : Fin n // j ∈ v.toList}`, so
`e.symm` takes a member of the image to its index. W1 exports the
equivalence without an application lemma, so `invOfInjective_apply`
is proved here: `invOfInjective` is
`(finCongr _).trans (List.Nodup.getEquivC _ _)` and `getEquivC`'s
`toFun` is `l.get i`, so `rfl` or a short `simp` over
`Vector.get_eq_getElem` and `Vector.getElem_toList` should close it.
If it proves generally useful it can move to
`Geb/Mathlib/Data/Vector/NodupEquivFin.lean` later; nothing else in
W3 uses it, so it stays here.

`pullbackLift_comp` is `hom_ext` at `t`, then `comp_get`, then
`invOfInjective_apply` at `e.symm ⟨…⟩` composed with
`Equiv.apply_symm_apply`. `pullbackLift_uniq` is `hom_ext` plus
`hm`'s injectivity applied to `hn` read at `t`.

The lift is not subject to row h's complexity discipline, and the
reason is not that its type is `Prop`: nothing reaches it from an
exposed data field of `Subobject.Classifier`. `χ` is such a field and
the lift is not, being used only inside Task 18's `IsPullback` proof,
where `Nonempty (IsLimit …)` erases it. `Vector.invOfInjective`'s
`invFun` is `l.idxOf`, linear per call, so were it reachable it would
face the same objection as the rejected `χ`.

Run: `lake build`
Expected: PASS once the routes above are written; before them, FAIL
with one placeholder error per `_`.

- [ ] **Step 5: add the square's commutation and vector-level
uniqueness**

```lean
/-- The characteristic morphism is `1` on the image. -/
theorem chi_comp_eq (m : U ⟶ X) (i : Fin U.len) :
    (chi m).toVec.get (m.toVec.get i) = 1 :=
  (chiVec_get_eq_one_iff m _).mpr (by
    simp [Vector.get_eq_getElem])

/-- A morphism whose fibre over `1` is the image is the
characteristic morphism. -/
theorem chi_uniq (m : U ⟶ X) (χ' : X ⟶ mk 2)
    (h : ∀ j, χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList) :
    χ' = chi m := _
```

`chi_comp_eq`'s side goal is `m.toVec.get i ∈ m.toVec.toList`, which
`simp [Vector.get_eq_getElem]` closes alone; a
`simpa … using List.getElem_mem _` there fails
`linter.unnecessarySimpa`, measured at this toolchain. See § Global
constraints on that linter.

`chi_uniq` is `hom_ext` at `j` followed by a case split on the
*value*, not on membership:

```lean
  hom_ext fun j ↦ by
    rw [chi_get]
    by_cases hj : χ'.toVec.get j = 1
    · rw [hj]
      exact ((chiVec_get_eq_one_iff m j).mpr ((h j).mp hj)).symm
    · have h1 : (chiVec m).get j ≠ 1 :=
        fun hc ↦ hj ((h j).mpr ((chiVec_get_eq_one_iff m j).mp hc))
      -- neither is `1`, so in `Fin 2` both are `0`
      have h2 : (χ'.toVec.get j).val ≠ 1 := fun hc ↦ hj (Fin.val_injective hc)
      have h3 : ((chiVec m).get j).val ≠ 1 := fun hc ↦ h1 (Fin.val_injective hc)
      have h4 : (χ'.toVec.get j).val < 2 := (χ'.toVec.get j).isLt
      have h5 : ((chiVec m).get j).val < 2 := ((chiVec m).get j).isLt
      exact Fin.val_injective (by omega)
```

`by_cases` on `χ'.toVec.get j = 1` is decided by the axiom-free
`instDecidableEqFin` — a real instance outranks the low-priority
`Classical.propDecidable` — so no `LawfulBEq (Fin n)` is reached and
nothing classical enters. Step 6's `#print axioms` is the backstop for
that claim, which is read-verified rather than elaborated.

Two things make `omega` able to finish, and **both** are needed.
First, the disequalities are lifted to `Fin.val` against the `ℕ`
literal, which `h2` and `h3` do (`hc : x.val = 1` is accepted where
`x.val = (1 : Fin 2).val` is expected, `(1 : Fin 2).val` reducing to
`1` by whnf). Second, the two bounds are **ascribed `< 2`** rather
than left as bare `isLt`: `χ' : X ⟶ mk 2`, so `(χ'.toVec.get j).isLt`
reads `… < (mk 2).len`, and `omega` does not reduce that
projection-of-constructor — it takes it as an atom, leaving
`a ≠ 1 ∧ a < c` for unknown `c`, which does not give `a = 0`. This was
probed at this toolchain: without the ascriptions `omega` fails with a
counterexample naming `↑{ len := 2 }.len` as an atom. The ascriptions
typecheck because `(mk 2).len` is defeq to `2` at default
transparency.
`Fin.val_injective` — `Mathlib/Data/Fin/Basic.lean`, reached here
transitively through the category-theory imports — is used rather than
`Fin.val_eq_val`, whose two arguments are explicit and which therefore
needs `(Fin.val_eq_val _ _).mp` in term position. If it is reported
unknown, that is a missing import, not a rename.
`Fin.val_eq_of_lt` does **not** exist; do not reach for it.

That the wrapper can supply `h` from `IsPullback` is Task 18's
obligation; this statement is the choice-free half of the spec's
split of `uniq`.

Run: `lake build`
Expected: PASS once the routes above are written; before them, FAIL
with one placeholder error per `_`.

- [ ] **Step 6: check the axioms, test, wire and commit**

Measure every declaration plus a monomorphic witness at
`FinSetSkel.{0}` — a sample `m : mk 2 ⟶ mk 4` with entries `1` and
`3`, whose `chiVec` is `[0, 1, 0, 1]`, the value measured whole at
this toolchain at `[propext, Quot.sound]`.

Expected: `[propext, Quot.sound]` throughout. A `Classical.choice`
here would most likely come from a decidability instance for list
membership, which is why Step 2 states a third fold lemma rather than
deciding anything; if one appears, find it by measuring each lemma the
failing proof names. Then run the banned-form grep.

The test parallel names that `m` **`sampleMono`** and its
characteristic vector **`sampleChiVec`**, asserts
`sampleChiVec = ⟨#[0, 1, 0, 1], rfl⟩` by `rfl` or `decide`, and
exercises `pullbackLift_comp` at a sample `z`. `sampleChiVec` is this
module's permanent axiom witness, which Task 18 re-measures by that
name, so it must be a monomorphic `def` at `FinSetSkel.{0}` and must
not be deleted.

Create the two `Classifier.lean` index files, each carrying its
`Core` line only — Task 18 adds the `Instance` line to both:

- `Geb/…/FinSetSkel/Classifier.lean`:
  `public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Core`
- `GebTests/…/FinSetSkel/Classifier.lean`:
  `import GebTests.Mathlib.CategoryTheory.FinSetSkel.Classifier.Core`

Then add the corresponding `Classifier` line to each of the two
`FinSetSkel.lean` index files, `public import` on the source side and
plain `import` on the `GebTests` side.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the characteristic vector and its inversion"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 18: the classifier wrapper

Spec sections: § Row l (the wrapper paragraph), § The classifier
consumes the W1 inversion, § Exported names.

**Files:**

- Create:
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Instance.lean`
- Create:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Classifier/Instance.lean`
- Modify: `GebMeta.lean`, the two `Classifier.lean` index files

**Interfaces:**

- Consumes: Tasks 5, 8, 10, 17;
  `Subobject.Classifier.mkOfTerminalΩ₀`, `IsPullback`,
  `IsPullback.of_isLimit'`, `PullbackCone.isLimitAux`,
  `IsPullback.lift`, `IsTerminal.from`.
- Produces: `FinSetSkel.truth`, `FinSetSkel.chi_iff_of_isPullback`,
  `FinSetSkel.classifier`. `classifier` is W5's `classifier` field.

`mkOfTerminalΩ₀` takes `Ω₀`, its terminality, `Ω`, `truth`, the
family `χ`, the pullback property and the uniqueness property, in
that order; confirm with `#check` before use.

- [ ] **Step 1: allowlist and create the module**

Append to `classicalAllowedModules` in `GebMeta.lean` first:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
```

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Core
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs

/-!
# The subobject classifier of `FinSetSkel`

The mathlib packaging of `Classifier/Core.lean`. The classifying
object is the object of length 2, `Ω₀` is the one-element object of
row b, and `truth` picks the index `1`; the characteristic morphism
sends the members of a monomorphism's image to `1`. This module and
`Classifier/Core.lean` fix that orientation jointly and each states
it.

The derivation of the vector-level hypothesis of
`Classifier.chi_uniq` from `IsPullback` lives here rather than in the
core, and it is content rather than packaging: it uses the pullback's
universal property and cannot be stated choice-free.

`Ω₀` is row b's terminal object, so the classifier's `Ω₀` and the
cartesian unit are the same object and their comparison is an
isomorphism between an object and itself.

## Main definitions

* `FinSetSkel.truth` — the truth morphism.
* `FinSetSkel.classifier` — the subobject classifier.

## Main statements

* `FinSetSkel.chi_iff_of_isPullback` — the fibre of a classifying
  morphism over `1` is the image of the monomorphism it classifies.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, subobject classifier, topos
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- The truth morphism: the point of the classifying object at
index `1`. -/
def truth : (mk 1 : FinSetSkel.{u}) ⟶ mk 2 := point 1

end FinSetSkel
```

Import `Mathlib.CategoryTheory.Subobject.Classifier.Defs` and **not**
`Mathlib.CategoryTheory.Topos.Classifier`, as § Interfaces above
says: the latter is deprecated at this revision, and
`weak.warningAsError = true` turns its warning into a build failure.

The module docstring records that constraint 6 is discharged by
construction:
`Ω₀` is row b's terminal object, so the classifier's `Ω₀` and the
cartesian unit are the same object and the comparison
`ElementaryTopos.tensorUnitIsoΩ₀` is an isomorphism between an object
and itself. W3 does not state that lemma —
`ElementaryTopos.tensorUnitIsoΩ₀` takes `[ElementaryTopos C]`, an
instance that does not exist until W5 — and it is a propositional
rather than a definitional equality, W2's comparison being
`IsTerminal.uniqueUpToIso`.

- [ ] **Step 2: derive the vector-level hypothesis from `IsPullback`**

```lean
/-- The fibre of a classifying morphism over `1` is the image of the
monomorphism it classifies. -/
theorem chi_iff_of_isPullback {U X : FinSetSkel.{u}} (m : U ⟶ X)
    (χ' : X ⟶ mk 2)
    (hp : IsPullback m (isTerminalOne.from U) χ' truth) (j : Fin X.len) :
    χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList := _
```

This is the deliverable the spec calls a named piece of the wrapper
rather than packaging: it mentions `IsPullback` and cannot be stated
choice-free.

Route:

- (←) from the square's commutation `hp.w : m ≫ χ' = _ ≫ truth`,
  read at the index `i` with `m.toVec.get i = j`, both sides being
  the constant `1`. Extracting that `i` from `j ∈ m.toVec.toList`
  is `List.getElem_of_mem` (or `List.mem_iff_getElem`) through
  `Vector.get_eq_getElem` — the traffic runs the opposite way from
  the (→) direction's `List.getElem_mem`.
- (→) from the universal property. Given `χ'.toVec.get j = 1`, the
  square `point j ≫ χ' = toOne (mk 1) ≫ truth` commutes — both are
  the constant-`1` morphism `mk 1 ⟶ mk 2`, by `hom_ext` — so
  `hp.lift` gives `l : mk 1 ⟶ U` with `l ≫ m = point j`; reading
  that at the unique index of `mk 1` gives
  `m.toVec.get (l.toVec.get 0) = j`, hence membership through
  `List.getElem_mem` and `Vector.get_eq_getElem`.

Confirm `IsPullback.lift`'s signature and the name of the
commutation field (`hp.w` or `hp.toCommSq.w`) with `#check` before
writing either direction. Prove the two directions as separate
`have`s and assemble, per
`docs/rules/lean-coding.md` § Proof guidelines.

Run: `lake build`
Expected: PASS once the routes above are written; before them, FAIL
with one placeholder error per `_`.

- [ ] **Step 3: build the classifier**

```lean
/-- The subobject classifier of `FinSetSkel`. -/
def classifier : Subobject.Classifier FinSetSkel.{u} :=
  Subobject.Classifier.mkOfTerminalΩ₀ (mk 1) isTerminalOne (mk 2) truth
    (fun m ↦ Classifier.chi m)
    (fun m ↦ _)
    (fun m _ χ' hp ↦ Classifier.chi_uniq m χ' (chi_iff_of_isPullback m χ' hp))
```

The `_` in the `uniq` argument's binder list — the seventh and last
argument — is not optional and is not a placeholder to fill. `uniq`'s type is
`∀ {U X} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω) (_ : IsPullback …), χ' = χ m`,
and Lean auto-inserts implicit and instance lambdas only for *leading*
binders and for those left over after the written binders run out —
never mid-list. So `fun m χ' hp ↦ …` binds `χ'` to the `[Mono m]`
instance and `hp` to the real `χ'`, and the mismatch is reported at
the body rather than at the binders, which makes the diagnostic
misleading. The `_` binds the instance explicitly, and a `_`-named binder whose
type is a class is still registered as a local instance.

The `isPullback` argument is a different lambda: there the instance is
auto-inserted as a trailing one, before the body is elaborated, which
is what puts `Mono m` in scope for `mono_iff_injective.mp ‹Mono m›`
below.

The two sibling arguments need no such binder: `(fun m ↦ …)` exhausts
the written binders before the instance, so the instance lambda is
auto-inserted as a trailing one.

The `_` in `(fun m ↦ _)`, by contrast, **is** a hole to fill, and it
is filled below in this same step. Two different `_`s on consecutive
lines: the one in the `uniq` binder list stays, the one in the
`isPullback` argument goes. This step's `Expected:` therefore reads
PASS *once the hole is filled* — the plan's convention is that a step
which states a declaration unproved expects FAIL with placeholder
errors, and a step which states and discharges it expects PASS at the
end.

The `isPullback` argument is the remaining hole and the largest
obligation of this task. Its statement is
`IsPullback m (isTerminalOne.from U) (Classifier.chi m) truth`.
Replace `(fun m ↦ _)` above — the sixth argument, `isPullback` — with
the following, in four named pieces:

```lean
    (fun m ↦ by
      have hinj : Function.Injective m.toVec.get := mono_iff_injective.mp ‹Mono m›
      -- the square: both sides are the constant `1` on the image of `m`
      have hsq : CommSq m (isTerminalOne.from _) (Classifier.chi m) truth :=
        ⟨hom_ext fun i ↦ by simp [Classifier.chi_comp_eq, truth]⟩
      -- membership of a competing cone's left leg, from its own commutation
      have hmem : ∀ (s : PullbackCone (Classifier.chi m) truth) (t : Fin s.pt.len),
          s.fst.toVec.get t ∈ m.toVec.toList := fun s t ↦
        (Classifier.chiVec_get_eq_one_iff m _).mp (by
          have := congrArg (fun k ↦ (k : _ ⟶ mk 2).toVec.get t) s.condition
          simpa [truth] using this)
      exact IsPullback.of_isLimit' hsq
        (PullbackCone.isLimitAux _
          (fun s ↦ Classifier.pullbackLift m hinj s.fst (hmem s))
          (fun s ↦ Classifier.pullbackLift_comp m hinj s.fst (hmem s))
          (fun _ ↦ (toOne_uniq _).trans (toOne_uniq _).symm)
          (fun s n hn ↦
            Classifier.pullbackLift_uniq m hinj s.fst (hmem s) n
              (hn WalkingCospan.left))))
```

Four notes on it. `hmem` is the piece with no counterpart in Task 17's
exports: it derives the membership `pullbackLift` requires from the
competing cone's own commutation `s.condition`, read at an index —
both sides of that equation are the constant `1`, so
`Classifier.chiVec_get_eq_one_iff` converts the value back into
membership. Its statement is written out here because Task 17 does not
supply it and this task's executor cannot read Task 17.

`fac_right` and every such cone's second leg are morphisms into
`mk 1`, and `toOne_uniq` gives each of them equal to `toOne _`, so
`fac_right` is closed two-sidedly —
`(toOne_uniq _).trans (toOne_uniq _).symm` — and **not** by
`toOne_uniq _` alone, whose shape is `?f = toOne ?X` and which would
need `s.snd` to be definitionally `toOne s.pt`. It is not: `s.snd` is
an opaque projection of an arbitrary cone. This is why the terminal
object is `Ω₀` and why `isTerminalOne` is named rather than
reconstructed.

`isLimitAux`'s `uniq` does **not** take
`Classifier.pullbackLift_uniq` directly: its hypothesis is quantified
over the whole index category,
`∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j`, where
`pullbackLift_uniq` wants the single equation `n ≫ m = z`. Hence the
`hn WalkingCospan.left` projection above;
`PullbackCone.fst s = s.π.app WalkingCospan.left` definitionally, so
it typechecks, and mathlib's own `isLimitAux'` does the same.

`CommSq`'s single field is the commutation equation, so the
anonymous-constructor `⟨…⟩` above is the whole square; `#check
@CommSq` and `@PullbackCone.isLimitAux` before writing either, and
expect both `hsq`'s `simp` and `hmem`'s `simpa` to need adjusting.
`hsq`'s goal after `hom_ext` sits at an index of `Fin (mk 1).len`, so
it needs that index collapsed to `0` — add `Fin.fin_one_eq_zero` to the
simp set, or `Subsingleton.elim`; mathlib's own call sites pass the
former explicitly rather than relying on its `@[simp]` attribute.

`Subobject.Classifier` is written qualified: inside
`namespace FinSetSkel`, a bare `Classifier` is the sub-namespace of
Task 17.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: check the axioms, test, wire and commit**

Measure `truth`, `chi_iff_of_isPullback` and `classifier`. Expected:
axioms **contained in** `{propext, Classical.choice, Quot.sound}` —
this is the allowlisted wrapper, so `Classical.choice` is permitted
but not required. `truth` is `point 1` from the choice-free
`Shapes/Core.lean` and will measure `[propext, Quot.sound]` at most;
only `classifier`, which goes through `mkOfTerminalΩ₀` and
`IsPullback`, is expected to carry the third. A tighter set than the
allowlist is not a discrepancy. Confirm `Classifier/Core.lean` is unchanged
by re-measuring its permanent witness `sampleChiVec`, in
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Classifier/Core.lean`.
Expected: `[propext, Quot.sound]`.

Create
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Classifier/Instance.lean`;
it names `classifier` in a `def` and asserts `classifier.Ω = mk 2` and
`classifier.Ω₀ = mk 1` by `rfl`.

Add `public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance`
to `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier.lean`, and the
plain-`import` parallel for the test module to its `GebTests`
counterpart; Task 17 Step 6 created both carrying `Core` alone. As in
Task 16, an unwired module compiles through lake's glob and is never
audited by `lake lint`.

Run: `bash scripts/lint-imports.sh`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`,
`lake lint -- GebTests`
Expected: PASS.

```bash
jj commit -m "feat(finsetskel): add the subobject classifier"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 19: documentation and `TODO.md`

Spec sections: § Documentation, § Amendments to `TODO.md`
(amendments 2 through 8; amendment 1 is already applied on
`feat/choice-free-primitives`).

**Files:**

- Modify: `docs/index.md`, `TODO.md`
- Modify, only as `lake shake` requires and in their own commit: the
  import lines of any of this branch's `.lean` modules (Step 1, which
  runs first for that reason)

- [ ] **Step 1: settle the import lists, in their own commit**

This step runs **before** the documentation edits, and the ordering is
load-bearing. `jj commit` takes no paths here — it commits the whole
working copy — so if the Markdown were already edited, this commit
would swallow it, mislabelling the documentation work as a refactor
and leaving Step 5 with nothing to commit. Running it first keeps this
commit `.lean`-only and lets `pre-push.sh` see unmodified Markdown.

This is also the branch's first `pre-push.sh` run, so it is where
`lake shake` first sees W3's modules and where their import lists are
actually settled — the per-task lists were a starting point, per
§ Global constraints.

Run: `bash scripts/pre-push.sh`
Expected: PASS, or a `lake shake` report. If it reports, adjust the
named modules' import lines, re-run until clean, and re-run the axiom
checks of every module whose imports changed — an import that
disappears can change which instance search finds.

```bash
jj commit -m "refactor(finsetskel): minimise W3's module imports"
jj bookmark set feat/finsetskel-w3 -r @-
```

Skip this commit if `lake shake` reported nothing.

- [ ] **Step 2: add the `docs/index.md` entries**

One entry per content module, eleven in all, in topological order,
placed after the existing `FinSetSkel/Skeleton.lean` and
`ElementaryTopos.lean` entries.

If Task 15 Step 6 reported that `Fin.funDecodeC` re-runs its
computation per application, record that in the
`Logic/Equiv/Fin/Basic.lean` entry: it is a persistent property of the
declaration, and Task 15 has no entry to write it into. Each states what the module
contains, not how it was built. `CONTRIBUTING.md` § Each phase
produces an artifact requires them; `CONTRIBUTING.md` § Document only
the persistent forbids referring to the spec or the plan from any of
them.

- [ ] **Step 3: apply amendments 2, 6 and the status row**

In `TODO.md` § Status: the W3 row becomes `Complete` with the eleven
content module paths, and its label becomes `Rows a–e, g, h, l, m`.
Delete the duplicate `W1 … Not started` row in the same edit: it is
factually wrong, it sits in the table being rewritten, and leaving it
would be the defect amendment 6 exists to remove one row away.

In § Workstreams, W3's bullet becomes "rows a through e, g, h, l and
m". In the operation table, rows f and j are marked derived rather
than assigned to W3, and row h loses its "and `HasEqualizers`". The
sentence below the operation table — "Rows e, j and k are reassigned
to W2 below (§ Class fields); the table above states the plan's
original per-field assignment" — is corrected: the table no longer
states the original assignment once rows f and j are marked derived,
and its enumeration gains `f`.

- [ ] **Step 4: apply amendments 3, 4, 5, 7 and 8**

- Amendment 3: in the operation table's row m, replace
  `SimplexCategory.mono_iff_injective` with
  `ConcreteCategory.mono_iff_injective_of_preservesPullback`. The
  alternative itself is retained.
- Amendment 4: constraint 7's parenthetical gains the distinction
  that "a single consumer in W3" holds of the two `Equiv`s but not of
  the three `Fin` operations beneath them, which rows d and g both
  consume.
- Amendment 5: the standing obligation listing files both concurrent
  pairs append to names
  `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` explicitly.
- Amendment 7: constraint 8 gains the qualification that a wrapper
  may also carry content which cannot be stated choice-free — row g's
  whiskering bridge and row l's derivation of the
  characteristic-vector hypothesis from `IsPullback` are both such.
- Amendment 8: a § Triggers entry records that `Fin.compressEquiv`
  has no consumer. W1 built it for row h, which no longer routes
  through it; besides its own module, its only remaining occurrences
  are its test parallel and its `docs/index.md` entry. The trigger's
  condition is the next occasion to revisit W1's helpers.
- **Not an edit.** A second § Triggers entry, recording that
  `Equiv.arrowCongrLeftC` has a single consumer because W4's
  converged spec put it out of scope, would keep that observation
  alive past Task 20 as amendment 8 keeps `Fin.compressEquiv`'s. It
  is not made here: it amends a constraint the user's approved spec
  rests on, and the decision is the user's. **Do not write it.**
  Report to the orchestrator that the entry is pending the user's
  decision on the `Equiv.arrowCongrLeftC` departure, and continue.

- [ ] **Step 5: lint the documentation and commit**

Run: `doctoc --update-only .`, `markdownlint-cli2 '**/*.md'`,
`bash scripts/pre-push.sh`
Expected: PASS.

```bash
jj commit -m "doc(finsetskel): index W3's modules and amend the roadmap"
jj bookmark set feat/finsetskel-w3 -r @-
```

---

## Task 20: remove the spec and the plan

Spec section: § Scope of this document (the transience paragraph).

**Files:**

- Delete:
  `docs/superpowers/specs/2026-07-29-finsetskel-w3-design.md`
- Delete:
  `docs/superpowers/plans/2026-07-29-finsetskel-w3-design.md`

`CONTRIBUTING.md` § Concern shape: specs and plans are transient.
They remain reachable in history and are absent from the working
tree, so no active branch presents superseded decisions as current.
This is the branch's final commit.

- [ ] **Step 1: confirm nothing references either file**

```bash
grep -rn "2026-07-29-finsetskel-w3-design" \
  --include='*.md' --include='*.lean' .
```

Expected: matches in the two files themselves only. The grep
self-matches, so a bare count is uninformative; what it is looking
for is a `docs/index.md` or `TODO.md` entry added in Task 19 that
cites the spec or the plan. Such a match is **removed**, not
tolerated: `CONTRIBUTING.md` § Document only the persistent forbids a
permanent document referring to a transient one.

- [ ] **Step 2: delete both, verify and commit**

Read this step in full before running anything: the `rm` removes the
file these instructions are in, so the commit that follows must be
run from memory or from a copy taken first.

Run: `bash scripts/pre-push.sh`
Expected: PASS. Run it **before** the deletion, so a failure is
diagnosed with both documents still present.

```bash
rm docs/superpowers/specs/2026-07-29-finsetskel-w3-design.md
rm docs/superpowers/plans/2026-07-29-finsetskel-w3-design.md
```

Run: `bash scripts/pre-push.sh`
Expected: PASS, again — the deletion changes `doctoc`'s and
`markdownlint`'s file set.

```bash
jj commit -m "chore(finsetskel): remove the W3 spec and plan"
jj bookmark set feat/finsetskel-w3 -r @-
```

The branch is then ready for the user's line-by-line review. No
`jj git push` happens without it
(`AGENTS.md` § No `jj git push` without user line-by-line review).

---

## Self-review record

**Spec coverage.** Every section of the spec maps to a task.
§ Decisions fixed here: 1 and 3 → Task 4, 2 → Tasks 2 and 3, 4 →
Task 10, 5 → Tasks 17 and 18, 6 → the module list, 7 → § Global
constraints, 8 → Tasks 1, 5 and 11, 9 → Task 1, 10 → Task 8.
§ Findings: the `Nat` interleaving → Task 2, the product equivalence
→ Tasks 2 and 3, the exponential recursion → Task 4, the domain
transport → Task 1, `LawfulBEq` → § Global constraints (W3 supplies
none), the classifier's consumption of the W1 inversion → Task 17,
row m as adapter → Tasks 10 and 18, every route through `incl` →
Task 10, the three `Prop` classes → Tasks 8 and 9, the index-function
correspondence → Task 5, `truth` is index 1 → Tasks 17 and 18.
§ Shared declarations → Task 1. § Module layout and § Exported names
→ the file-structure and namespace tables. § Deliverables rows a–m →
Tasks 5 through 18. § Tests → each task's own test step. §
Documentation → Task 19 Step 2 and the module docstrings of Tasks 2,
14, 17 and 18. § Amendments → Task 19. § Out of scope → nothing:
row i, row k, the `ElementaryTopos` instance, the constraint-6
comparison lemma, an agreement lemma with mathlib's tainted
encodings, a two-sided `arrowCongrC`, `Fin n`-indexed chosen cones
and the `C`-suffix rename appear in no task. § Verification
obligations 1 through 9 → each task's axiom-check step (1, 2), the
`#check`-in-module rule of § Global constraints (3), Task 14 Step 5
and Task 17 Step 2 (4), the mathlib-name confirmation bullet of
§ Global constraints (5 — that bullet, not the per-task reminders,
which are deliberately partial), Tasks 8, 12, 16 and 18 Step 1 (6),
Task 19 Step 5 (7), § Global constraints and every probe deletion
(8), Task 15 Step 6 (9). `CONTRIBUTING.md` § Cite the literature is
discharged by the `## References` bullet of § Global constraints and
the nine module docstrings carrying `[Freyd1972]`; no task adds a
`docs/references.bib` entry, per the spec.

**Three departures from the spec, all reported rather than taken
silently.** Task 1 records that W4's converged spec puts
`Equiv.arrowCongrLeftC` out of scope, so the declaration has one
consumer rather than two and the spec's § Shared declarations
overstates the ground for its placement; the placement is unchanged,
and Task 19 Step 4 records the corresponding `TODO.md` § Triggers
entry as an explicit do-not-edit plus a report to the orchestrator,
so nothing about the observation survives Task 20 unless the user
asks for the entry. Task 17 Step 2 records the reading of verification
obligation 4 under which row l's fold lemmas carry neither a counter
nor a `Nodup` hypothesis. Task 5 records that rows c, d and h do not
consume `homEquivIdxFun`, although the spec's § W1's index-function
correspondence anticipates that they would: this plan states those
rows in W1's application-normal form and proves them by `hom_ext`,
which needs no equivalence. Row g consumes it, so the deliverable and
W5's access to it are unchanged.

**Verified before this plan was written.** Elaborated at
`v4.33.0-rc1` through the `lean-lsp` MCP and measured monomorphically:
`Equiv.arrowCongrLeftC` (`[Quot.sound]`); `Fin.divNatC`,
`Fin.modNatC`, `Fin.pairC` and all three round-trip proofs verbatim;
`finProdFinEquivC` (`[propext, Quot.sound]`); `finFunctionFinEquivC`
and its computed round trip (`[propext, Quot.sound]`); the row-g
chain's association and types; the `ULift` transport shape of
`homEquivIdxFun`; row h's injection (`[propext]`) and inverse pass
(`[propext, Quot.sound]`); row l's scatter (`[propext, Quot.sound]`,
computing `[0, 1, 0, 1]` at the sample). Signatures confirmed:
`ofChosenFiniteProducts`, `adjunctionOfEquivRight`,
`rightAdjointOfEquiv`, `Closed`, `MonoidalClosed`,
`Subobject.Classifier` and its fields, `mkOfTerminalΩ₀`,
`whiskerLeft_fst`, `whiskerLeft_snd`, `isTerminalTensorUnit`,
`BinaryFan.IsLimit.mk`, `BinaryCofan.IsColimit.mk`, `Fork.IsLimit.mk`,
`Fork.ofι`, `PullbackCone.isLimitAux`, `IsInitial.hasInitial`,
`hasBinaryCoproducts_of_hasColimit_pair`, `asEmptyCone`,
`asEmptyCocone`, `IsTerminal.ofUniqueHom`. Two corrections to the
spec's names follow from that pass and are written into the tasks
that use them: `hasFiniteCoproducts_of_has_binary_and_initial` is
`CategoryTheory.…`, not `CategoryTheory.Limits.…` (Task 9), and
`Mathlib.CategoryTheory.Topos.Classifier` is deprecated in favour of
`Mathlib.CategoryTheory.Subobject.Classifier.Defs` (Task 18).

**Left as routes rather than terms.** Row c's and row d's universal
properties (Tasks 6 and 7), row m (Task 10), the naturality proofs
(Tasks 11 and 13), the whiskering bridge (Task 12), row h's two fold
lemmas and universal property (Tasks 14 and 15), row l's fold lemmas,
inversion lemma and uniqueness (Task 17), and the pullback
construction (Task 18). Each names the lemmas its route needs and
says what to do when one is absent.

**Round 12** (two fresh agents: one asked whether Task 15's sharing
step was sound *or should be replaced*, one on the round-11 repairs)
returned one blocker and four serious findings, all applied — and the
blocker's fix was to delete the apparatus rather than repair it a
fourth time.

The blocker: the step had **no positive control**. `lift` returns a
value, so one trace is equally consistent with sharing and with the
measurement having collapsed — the term folded at elaboration, the
value cached, the trace firing for an unrelated reason. Three rounds
of repair had each removed one way for the step to report success
having measured nothing, and left the general one untouched. The
reviewer also established by probe that `dbgTrace` from `#eval` *is*
captured into the message log as an `info` diagnostic, so
`lean_run_code` can observe it after all — which dissolved round 11's
prohibition, since a snippet carrying its own copies never imports the
edited module. Step 6 is now a single snippet with subject and control
side by side, expecting one trace and five, touching no file in the
repository: no edits to an upstream-eligible module, no build, no
revert, no guard grep, and self-validating, because a run whose
control does not fire is a broken instrument rather than a pass. The
`Fin.funDecodeC` sub-check is deleted — its outcome was predicted, its
finding pre-declared harmless, and it had no consumer — which is a
fourth departure from the spec, obligation 9 naming it, and is
reported as such.

Also applied: the confirmation grep did not cover Step 5's two
witnesses, so a probe could have shipped into an upstream-eligible
module past every check; Task 18 Step 3 called `isPullback` "the fifth
argument" when it is the sixth, in a step whose own text correctly
calls `uniq` the seventh, so an executor trusting the ordinal would
have overwritten `χ`; and Task 8's two in-module `#check`s had no
deletion instruction and would have been committed.

**Round 11** (two fresh agents, both aimed at the previous round's
repairs rather than at unread tasks). The Lean lens returned
**converged**, verifying all five of round 10's repair sites — the
`chi_uniq` closing term by machine probe, including that the `< 2`
ascriptions typecheck off `Fin.isLt` and that `omega` closes from
exactly those four facts. The executability lens returned three
serious findings, **all inside Task 15's `dbgTrace` step**, and
together they had made that step a no-op:

`lean_run_code` resolves an `import` against the built olean, and no
step ran `lake build` between the edit and the snippet — so the
executor would have measured the *stale* module, seen no trace, taken
the `unobservable` branch and passed. The measurement now runs as an
in-module `#eval` read from `lake build`'s output, with `lean_run_code`
explicitly ruled out and the reason given. The `Fin.funDecodeC`
sub-check had nothing to trace at all, no `dbgTrace` ever being
inserted into it; it now says to copy the body into the snippet as
`funDecodeCTraced`. And the one restructuring the five-line branch
permitted — hoisting the vector into a `liftVec` helper — is
structurally identical to what Step 3 already does, so the branch's
only sanctioned action could not have helped; the branch is now
stop-and-report, which also makes the revert instruction complete.

**Round 10** (two fresh agents: executability over four tasks neither
earlier pass had read, Lean correctness over round 9's edits) returned
one blocker and three serious findings, all applied, and every one of
them a defect round 9 had introduced.

The blocker: `chi_uniq`'s closing `omega` cannot succeed. `χ' : X ⟶ mk 2`,
so `(χ'.toVec.get j).isLt` reads `… < (mk 2).len`, and `omega` takes
that projection-of-constructor as an atom rather than reducing it —
leaving `a ≠ 1 ∧ a < c` for unknown `c`, which does not give `a = 0`.
The reviewer probed it and reproduced the failure with the atom named
in the counterexample. The two bounds are now ascribed `< 2`.

Serious: `fac_right` cannot be `toOne_uniq _`, whose shape is
`?f = toOne ?X` and which would need `s.snd` definitionally
`toOne s.pt` — it is an opaque projection of an arbitrary cone; the
route is two-sided. Task 11's permanent-witness instruction was
self-contradictory, demanding a witness "at `FinSetSkel.{0}`" built
from `expEquivIdx`, whose type contains no `FinSetSkel`; it is now
written-out code built from `expEquivHom`, renamed to match, and
Task 12's re-measurement follows it. And Task 15's `dbgTrace` sharing
check named no observation tool, so absence of a trace was
indistinguishable from sharing — the failing branch also being an
unbounded "restructure until shared" on a deliverable Task 16
consumes; it now names `lean_run_code`, distinguishes `unobservable`
from shared, and caps the restructuring at one named alternative.

**Round 9** (two fresh agents: executability over four tasks the
previous round had not read, Lean correctness over the previous
round's own edits). The Lean lens returned **converged** a second
time, catching in its minors the error this plan had introduced one
round earlier: the second `scatterOne` fold lemma's base case is not
`Or.inr h`, which does not inhabit its goal. It also resolved a search
this plan had left open — core's `List.fst_mem_of_mem_zipIdx` extracts
`j ∈ L` from `zipIdx` membership at any counter, so the hand-rolled
lemma the round had added is withdrawn — and supplied the numeral
normalisation `omega` needs in row l's `Fin 2` split.

The executability lens returned three serious, all one root cause:
obligations written from the whole-plan vantage point rather than from
inside a single task. Four tasks were told to "re-measure the earlier
core module's witnesses", every one of which the creating task
deletes and none of which that subagent can reconstruct; core modules
now keep a *named* permanent witness in their `GebTests` parallel —
`samplePoint`, `sampleExpEquivHom`, `sampleEqualizerInj`,
`sampleChiVec` — which the later task measures by name, and which
`lake lint -- GebTests` then audits continuously. Task 14's second
fold lemma delegated its one hard step to a three-name lemma search,
and Task 18's `isPullback` hole — the largest obligation in the task —
was prose only, with the membership hypothesis its `lift` field needs
named nowhere; both now carry written-out terms.

**Round 8** (two fresh agents: Lean correctness, and a fresh-eyes
executability lens simulating a per-task subagent) split. The Lean
lens returned **converged** — no blocker, no serious — having traced
Task 13 Step 3's two-stage proof symbol by symbol and confirmed both
sides meet; its three minors are applied, one of which was a
fictitious lemma name, `Fin.val_eq_of_lt`, that this plan had invented
for row l's `Fin 2` split. The executability lens returned four
serious, all applied and all a class the six static rounds could not
see. Chief among them: ticking this file's `- [ ]` boxes during
execution would have put a plan-file diff inside every task's commit,
since `jj commit` takes the whole working copy — the same failure
Task 19 Step 1 exists to prevent, left unguarded for the plan itself.
Also: two proofs in Task 17 were specified only by reference to
Task 14's, which that subagent cannot read; Task 13 Step 1's fallback
would have had the executor edit Task 11's committed module and then
follow a recipe no longer typechecking against it; and Tasks 11, 14
and 17 omitted the `universe u` / `namespace` / `@[expose] public
section` skeleton that their own `variable` lines require.

**Round 7** (three fresh agents, the consistency lens relaunched after
its first attempt stalled) returned no blocker and three serious
findings, all applied. The consistency lens found the single
cross-reference the round's own renumbering script had missed: Task
19's Files block still pointed the `.lean` import commit at Step 4,
the `TODO.md` amendment step, rather than at Step 1 — the Files block
being the first thing that task's subagent reads. It also corrected a
count in this record and, incidentally, a count in its own brief. The
two from the Lean lens, both applied. Task 13 Step 3's recipe failed a third time,
for a third reason: after `ext t` the `homEquivIdxFun …` term sits
*unapplied* as `expEquivIdx`'s function argument, and `simp only` does
not eta-expand a function occurrence to make an applied-form equation
fire — so the argument is now bridged under a `funext` in a `have`
before the morphisms are compared, and the step's three-move summary
was reordered to match. The reviewer probed a minimal analogue of the
eta failure. Second: Task 19's import commit came *after* the
documentation edits, and `jj commit` takes the whole working copy, so
it would have swallowed `docs/index.md` and `TODO.md` into a commit
messaged `refactor(…)` and left the documentation commit empty. The
import step is now Step 1 and the ordering is recorded as
load-bearing; path-scoped `jj commit` was rejected as the fix, being
its own footgun.

**Round 6** (two fresh agents: Lean correctness, consistency and
executability) returned no blocker and four serious findings, all
applied. Task 13 Step 3's `simp only` recipe still could not fire:
`expEquivHom` is a nested `Equiv.trans`, and the `homEquivIdxFun`
lemmas match neither a `trans` application nor its `.symm`, so
`Equiv.trans_apply` — `@[simp]` in mathlib, but `simp only` does not
load the default set — is now named. Task 14 Step 7's `getElem?` side
goal was closed by `simp [hget]`, which makes no progress: `hget` is
about `l[k]` and the goal about `l[k]?`, so the conditional
`List.getElem?_eq_getElem` never fires; the reviewer probed it and the
route is now an explicit `rw`. Five steps whose code blocks end
declarations in `:= _` claimed `Expected: PASS`, and Task 18 Step 3
asserted that convention held plan-wide; all six now state the real
one. And Task 19 folded `lake shake`'s `.lean` import adjustments into
a documentation commit, against `CONTRIBUTING.md` § Concern shape —
they are now their own commit, declared in the task's Files block and
taken first, since `jj commit` takes the whole working copy.
Minors applied with them: Task 14 now wires its own source index
rather than leaving the module unreachable from a root import for one
commit — with the wiring written into its Step 8, not only into its
Files block — and `scatter`'s bound
is `j.isLt` throughout.

**Round 5** (two fresh agents: Lean correctness, consistency and
executability) returned no blocker and two serious findings, both
applied. One `simpa … using List.getElem_mem _` in Task 14 and another
in Task 17 fail `linter.unnecessarySimpa` — `simp` closes both goals
alone, and `weak.warningAsError` makes the redundant `using` term a
build error. The reviewer diagnosed the cause as open metavariables
and proposed a replacement; both the diagnosis and the replacement
were wrong, verified at this toolchain, so the finding stands but the
fix is `simp [Vector.get_eq_getElem]` in both places, and § Global
constraints now carries the rule. The second: Task 15 Step 6 directed
an edit to a `docs/index.md` entry that does not exist until Task 19
and is not that task's file — the converse of the deferred-wiring
shape rounds 2 through 4 kept finding — now a report to the
orchestrator with a matching hook in Task 19 Step 2.

**Round 4** (two fresh agents: consistency and executability, Lean
correctness) returned one blocker and three serious findings, all
applied. The blocker: `mkOfTerminalΩ₀`'s `uniq` argument was written
`fun m χ' hp ↦ …`, which binds `χ'` to the `[Mono m]` instance,
because Lean auto-inserts instance lambdas only for leading and
trailing binders, never mid-list — Task 18 Step 3 now writes the
binder explicitly, and records why the resulting error would have been
reported at the body rather than at the binders. The serious three
were all one shape found for the third time: Tasks 16 and 18 had Files
blocks claiming index-file edits that no step of theirs performed,
because Tasks 15 and 17 deferred the wiring forward, which would have
left two wrapper modules compiled by lake's glob but never reached by
`runLinter` — green, and unaudited by the axiom linter; and the
self-review record contradicted Task 19's amendment step about the conditional
`TODO.md` entry.

**Round 3** (two fresh agents: Lean correctness, executability under
`superpowers:subagent-driven-development`) returned three blockers
and five serious findings, all applied. From the Lean lens: Task 13's
rewrite recipe could not fire, `tensorLeft` being
`(curriedTensor C).obj X` rather than `◁` syntactically, so
`curriedTensor_obj_map` is now named; `PullbackCone.isLimitAux`'s
`uniq` quantifies over `WalkingCospan` and does not accept
`pullbackLift_uniq` directly, so Task 18 now projects the leg; and
the one typing risk the plan itself calls out — W2's `closed` field
over `cartesian.toMonoidalCategory`, where the instance path is two
`extends` hops — now carries a probe in Task 13 rather than an
assertion. From the executability lens:
`jj edit <bookmark>` followed by `jj commit` would have overwritten
two reviewed commits, since `jj commit` describes the current
working-copy commit rather than creating one beside it (Task 1, and
the `jj new` rule in § Global constraints); no task moved the branch
bookmark, so at the end of the branch the commit the user reviews
would still have been the plan commit (the two-command idiom in
§ Global constraints, written out in every commit step — twenty-one
such steps, Task 19 carrying two, its import commit conditional on
`lake shake` reporting anything); Task 13's Files
list named a `GebMeta.lean` edit no step of it performed, which would
have failed its own `lake lint -- GebTests` (Task 12 Step 1 now
appends both names); Task 8's commit step verified none of what it
wrote to `GebTests`; and Task 19's amendment step carried a step conditioned on
a user decision its executor cannot obtain (now an explicit
do-not-edit with a report).

**Round 2** (two fresh agents: Lean correctness, cross-reference
consistency) returned no blocker and five serious findings, all
applied: `get_scatterOne_of_mem` was not provable in the shape round 1
gave it — its head case needs the strengthened
`get_scatterOne_eq_one_of`, without which the proof would have to
decide list membership and reach the taint the pair exists to avoid
(Task 17); the `Exponential.lean` and `Equalizer.lean` index files
were attributed to tasks whose steps never wired them, leaving the
Task 13 test module imported by nothing (Tasks 11 through 16);
Task 15 had no axiom-check step; and Task 8's "consumed by"
annotation named a task that does not use `isTerminalOne` while
Task 13's "consumes" omitted the cartesian instance it cannot
elaborate without.

**Round 1 of adversarial review** (three fresh agents: Lean
correctness, cross-reference consistency, obligation coverage)
returned no blocker and five serious findings, all applied: the
`Prop`-valued instance test written as a `Prod` (Task 9), the
`Sum.elim` reduction missing from row c's rewrite chains (Task 6),
the decidability route in row l that could have pulled
`LawfulBEq (Fin n)`'s taint into a choice-free module (Task 17, now
a third fold lemma), the absent `[Freyd1972]` citations (§ Global
constraints and nine module docstrings), and the overstated coverage
claim for verification obligation 5 (§ Global constraints, corrected
above). One cosmetic-taste finding was rejected: declaration
docstrings naming a choice-dependent mathlib counterpart follow W1's
own precedent at `FinSetSkel.decidableEqHom`, which names
`instDecidableEqOfLawfulBEq` and `Vector.instLawfulBEq` in exactly
that way.

**Type consistency.** `homEquivIdxFun` itself, with `X` and `Y`
explicit, appears in Tasks 5 and 11; Task 13 applies only its two
`@[simp]` application lemmas. `expEquivIdx` and `expEquivHom` take `m z y`
explicitly, in that order, in Tasks 11 and 13, and `expHomEquiv`
takes `X` then `Z` then `Y`, matching `adjunctionOfEquivRight`'s
argument order. `Equalizer.ι`, `Equalizer.lift` and
`Equalizer.obj` are spelled with the `Equalizer.` prefix in Task 16
and bare inside `namespace FinSetSkel.Equalizer` in Tasks 14 and 15;
`Classifier.chi`, `Classifier.chi_uniq` and
`Classifier.pullbackLift` likewise between Tasks 17 and 18.
`cartesianMonoidalCategory`, `monoidalClosed`, `initialCocone`,
`binaryCoproductCocone`, `equalizerCone` and `classifier` are spelled
identically in their producing tasks, in § Exported names and in W5's
field table.
