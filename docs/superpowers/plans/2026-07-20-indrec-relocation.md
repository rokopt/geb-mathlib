# IR-code morphisms, Universes/Container relocation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Branch setup](#branch-setup)
- [File structure](#file-structure)
- [Task 1: relocate `section Universes`](#task-1-relocate-section-universes)
- [Task 2: relocate `section Container`](#task-2-relocate-section-container)
- [Task 3: docs split and gates](#task-3-docs-split-and-gates)
- [Final verification (whole branch)](#final-verification-whole-branch)

<!-- END doctoc -->

**Goal:** move `section Universes` and `section Container` of
`Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`, with their tests, into
sibling modules `Universes.lean` and `Container.lean`, discharging the
spec's placement requirement (the morphism development precedes the
`Universes` and `Container` sections, so later workstreams can extend
those sections with morphism uses without import cycles into
`Basic.lean`).

**Architecture:** a single-concern, content-preserving refactor (spec
`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
§ Placement and documentation, § Branch decomposition). Every moved
declaration keeps its name, statement, and proof term exactly; a
reviewer verifies the move with `git diff --color-moved`. No new
mathematics, no renames, no proof changes, no morphism uses of
universes or containers yet.

**Import decision (recorded rationale):** each new source module
imports only `Geb.Mathlib.Data.PFunctor.IndRec.Basic` (the header form
of the existing siblings `Hom.lean` and `Functor.lean`). This compiles
today — `IR.interpMor`, consumed by `univEndoMor`, is defined in
`Basic.lean` — and satisfies the import-minimization check (an unused
`Functor` import would be flagged). The placement requirement is
discharged by the extraction itself: a later branch can add a
`Functor` (or `Naturality`) import to the new modules without creating
a cycle, since nothing imports them back into the morphism modules.

**Tech Stack:** Lean 4, mathlib, the project's `IndRec` development;
`jj` (colocated) for all mutations.

## Global Constraints

Copied from the design spec and the relocation handoff; every task's
requirements include these.

- Mathematical content fixed: every moved declaration keeps its name,
  statement, and proof term exactly. The moved declarations' existing
  universe lists are kept verbatim. Docstring scaffolding (module
  docstrings, section headers) is the only text that changes.
- Constructive only: no `noncomputable`, no `Classical`; the axiom
  linter (`lake lint`) permits `{propext, Quot.sound}` only. A pure
  move introduces no new axioms; the gate re-verifies.
- Recursor-only recursion, explicit term-mode proofs: moot for a pure
  move, but binding on any incidental edits — there are none in this
  plan; if execution surfaces one, stop and re-plan.
- Universe discipline: full-or-absent `.{…}` lists; no auto-bound
  `u_1`; remove unused `universe`/`variable` declarations from files
  they are moved out of (verified: `uK`/`uT` occur nowhere in either
  `Basic.lean` outside the moved regions).
- mathlib style: 2-space indent, 100-column lines, module docstring
  mandatory after imports with sections in order (`# Title`, summary,
  `## Main definitions`, `## Implementation notes`, `## References`,
  `## Tags`), each present only when non-vacuous.
- Module system: every new file declares `module` after the copyright
  block; source modules `public import` their dependencies; new
  modules are registered in BOTH the source umbrella
  (`Geb/Mathlib/Data/PFunctor/IndRec.lean`) AND the test umbrella
  (`GebTests/Mathlib/Data/PFunctor/IndRec.lean`) — a missed source
  umbrella is a known failure mode caught only by `pre-push.sh`.
- VCS: `jj` only for mutations (raw mutating `git` is hook-blocked;
  read-only `git`, including `git diff --color-moved`, is fine).
  Commit messages in mathlib conventional form
  (`refactor|doc(indrec): imperative subject`, no capital, no
  trailing period). No pushes.
- Gates per task: `lake build` and `lake test` pass before each
  commit. Red (verify-failure) steps run `lake test` (bare
  `lake build` does not build `GebTests`).

## Branch setup

- [ ] Verify the working copy already sits on `main`'s tip and
  carries only the transient documents (jj auto-tracks them into `@`;
  a `jj new main` here would strand them in the previous `@`):

  ```bash
  jj log -r 'main..@' --summary
  ```

  Expected: `@` is a child of `main`'s tip whose changes are exactly
  this plan and the relocation handoff. If `@` is elsewhere, run
  `jj new main` and then
  `jj restore --from <previous @> docs/superpowers/` to carry the two
  documents over before proceeding.

- [ ] Retire the 2b section of `.superpowers/sdd/progress.md` as done
  (keep its Minor-findings list: the `coprodMor` samples never
  exercise a non-identity reindexing; `Functor.lean` deliberately
  omits `## Main definitions`) and open a relocation-branch section.

- [ ] Commit the transient documents and create the topic bookmark:

  ```bash
  jj commit -m "doc(indrec): add the relocation plan and handoff"
  jj bookmark create refactor/indrec-relocation -r @-
  ```

## File structure

- Create `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean` — the nine
  `section Universes` declarations of `Basic.lean` (Task 1).
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Universes.lean` — the
  `StepConstructors` and `NatFin` test sections of the test
  `Basic.lean` (Task 1).
- Create `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean` — the
  `section Container` declaration `contCode` (Task 2).
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Container.lean` — the
  `Container` test section (Task 2).
- Modify `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` — delete the
  moved sections; module-docstring reductions (Tasks 1–2).
- Modify `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` — delete
  the moved test sections; module-docstring reductions (Tasks 1–2).
- Modify `Geb/Mathlib/Data/PFunctor/IndRec.lean` AND
  `GebTests/Mathlib/Data/PFunctor/IndRec.lean` — register both new
  modules in both umbrellas (Tasks 1–2).
- Modify `docs/index.md` — split the `IndRec/` entry (Task 3).

`TODO.md` needs no change: it does not mention the `Universes` or
`Container` sections (verified by grep).

Line numbers below refer to the pre-branch state of each file; later
tasks re-locate content by its quoted first/last lines, not by number,
since Task 1's deletions shift Task 2's numbers.

---

## Task 1: relocate `section Universes`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Universes.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean`

**Interfaces:**

- Consumes: `IR`, `IR.iota`/`sigma`/`delta`, `IR.interpObj`,
  `IR.interpMor`, `FreeCoprodCompDisc.Endo`/`EndoMor` (all from
  `Basic.lean` and its public imports).
- Produces: the declarations `univBinder`, `univSigma`, `univPi`,
  `univIota`, `UnivConstructor`, `univConstructorCode`, `univCode`,
  `univEndo`, `univEndoMor` — unchanged names, statements, and proof
  terms — now exported from
  `Geb.Mathlib.Data.PFunctor.IndRec.Universes` (and, via the
  umbrella, from `Geb.Mathlib.Data.PFunctor.IndRec` as before).

- [ ] **Step 1: Create the test module (failing).** Create
  `GebTests/Mathlib/Data/PFunctor/IndRec/Universes.lean` with this
  scaffolding:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Universes

  /-!
  # Tests for universe codes

  One-step name constructors (`stepIota`, `stepSigma`, `stepPi`) build
  elements of one application of the universe endofunctor `univEndo` to
  a given universe, generically in the starting types and the given
  universe; `rfl` tests check that their decodings are the expected
  lifted starting types, dependent sums, and dependent products.

  The starting types are then instantiated at a two-part family — the
  natural numbers and every finite type — and the endofunctor is
  iterated from the empty universe, adjoining names whose decodings mix
  both starting types under dependent sums and dependent products.

  `univEndoMor` is generated by `IR.rec`, whose computation rule is
  propositional rather than definitional, so its applications do not
  reduce definitionally; the morphism action is exercised at the
  algebra level in the core `IR` tests.

  ## Tags

  inductive-recursive, universe
  -/

  @[expose] public section

  open CategoryTheory IndRec

  universe uK uT
  ```

  then, below the `universe uK uT` line, the two test sections moved
  verbatim from `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`:
  the whole of `section StepConstructors` … `end StepConstructors`
  (lines 66–101, first declaration `stepIota`, opening `variable (K :
  Type uK) (T : K → Type uT) (X : …)`) and the whole of
  `section NatFin` … `end NatFin` (lines 103–184, declarations
  `NatFinIdx`, `NatFinTypes`, `natFinEndo`, `stage0`–`stage3`,
  `natName`, `finName`, `natName2`, `finSuccFamily`, `sigmaName`,
  `piName`, `sigmaPiName`, and their `example`s, ending with the
  `sigmaPiName` decoding example). Do not edit the moved text.

  Register the module in BOTH umbrellas:
  `Geb/Mathlib/Data/PFunctor/IndRec.lean` gains

  ```lean
  public import Geb.Mathlib.Data.PFunctor.IndRec.Universes
  ```

  after the `Functor` import (the umbrella lists modules in the
  spec-mandated order: morphism development before `Universes` and
  `Container`), and `GebTests/Mathlib/Data/PFunctor/IndRec.lean` gains

  ```lean
  import GebTests.Mathlib.Data.PFunctor.IndRec.Universes
  ```

  after its `Functor` import.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL — the import
  `Geb.Mathlib.Data.PFunctor.IndRec.Universes` does not exist yet.

- [ ] **Step 3: Implement the move.** Create
  `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

  /-!
  # Universes closed under dependent sums and products, as IR codes

  The code of the universe generated by an arbitrary family of starting
  types and closed under dependent sums and dependent products,
  combining Examples 2.5 and 2.6 of
  [GhaniNordvallForsbergMalatesta2015]: the coproduct of one `iota`
  code per starting type (in place of the examples' single `iota` code
  for the natural numbers), one dependent-sum former, and one
  dependent-product former. The universe is an endofunctor example
  (`IR I I`), so the input and output index types coincide.

  ## Main definitions

  * `univCode`, `univEndo`, `univEndoMor` — the code of the universe
    generated by an arbitrary family of starting types and closed under
    dependent sums and dependent products, with the object and morphism
    maps of its interpretation.
  * `univBinder`, `univSigma`, `univPi`, `univIota`,
    `UnivConstructor`, `univConstructorCode` — the constructor
    subcodes: the binder-former subcode shared by the dependent-sum
    and dependent-product formers, the starting-type subcodes, and
    the constructor index assembling them.

  ## References

  * [GhaniNordvallForsbergMalatesta2015]

  ## Tags

  inductive-recursive, universe
  -/

  @[expose] public section

  universe uK uT

  namespace IndRec

  open CategoryTheory
  ```

  (scaffolding order matching the sibling source modules: section,
  `universe`, `namespace`, `open`) then, below the
  `open CategoryTheory` line, the nine declarations of
  `section Universes` of `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
  (lines 1075–1137: `univBinder` through `univEndoMor`, including the
  `variable (K : Type uK) (T : K → Type uT)` line between `univPi` and
  `univIota`), moved verbatim — the `section Universes`/
  `end Universes` wrapper, the `/-! ### Universes closed under … -/`
  header block (absorbed into the module docstring above), and the
  original `universe uK uT` line are dropped; everything else is
  untouched. Close the file with:

  ```lean
  end IndRec
  ```

  In `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`:

  - Delete lines 1059–1140 (from `section Universes` through
    `end Universes` and the following blank line), leaving
    `end IR` … blank line … `section Container` adjacent.
  - In the module docstring's `## Main definitions`, delete the bullet

    ```markdown
    * `univCode`, `univEndo`, `univEndoMor` — the code of the universe
      generated by an arbitrary family of starting types and closed under
      dependent sums and dependent products, with the object and morphism
      maps of its interpretation.
    ```

  - In the module docstring's `## Tags`, change the line to

    ```markdown
    inductive-recursive, polynomial functor, W-type, container
    ```

    (drop `universe`; `container` is dropped by Task 2).

  In `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`:

  - Delete lines 64–185 (`universe uK uT`, the moved sections
    `section StepConstructors` through `end NatFin`, and the interior
    and trailing blank lines), leaving exactly one blank line between
    `open CategoryTheory IndRec` and `section MorphismAction`.
  - In the module docstring, delete the first two summary paragraphs
    ("One-step name constructors …" and "The starting types are
    then …") and rewrite the third paragraph's `univEndoMor` clause so
    it reads:

    ```markdown
    The morphism action is exercised at the algebra level
    (`IR.interpMorStep`), where it computes by `rfl`; `IR.interpMor`
    itself is generated by `IR.rec`, whose computation rule is
    propositional rather than definitional, so its applications do not
    reduce definitionally.
    ```

  - In `## Tags`, change the line to

    ```markdown
    inductive-recursive, polynomial functor, container
    ```

    (drop `universe`; `container` is dropped by Task 2).

- [ ] **Step 4: Run the tests to verify success, and verify content
  preservation.**

  Run: `lake build && lake test`
  Expected: PASS.

  Run: `jj diff` and eyeball: the only changes to the two
  `Basic.lean` files are deletions of the moved regions and the
  docstring edits above; the new files contain the moved text
  unchanged. (The `git diff --color-moved` rendering is only
  available once the new files are in a git commit; it runs after
  Step 5 and again in the final verification.)

  Run (declaration-preservation count — nine declarations in the new
  module, none left in `Basic.lean`):

  ```bash
  grep -c "^def " Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean
  grep -cE "univBinder|univSigma|univPi|univIota|UnivConstructor|univConstructorCode|univCode|univEndo" \
    Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean
  ```

  Expected: first count 9 (`univBinder`, `univSigma`, `univPi`,
  `univIota`, `UnivConstructor`, `univConstructorCode`, `univCode`,
  `univEndo`, `univEndoMor`); second count 0 (the second `grep`
  exits non-zero on zero matches — that is the expected outcome).

- [ ] **Step 5: Commit, then verify the move rendering.**

  ```bash
  jj commit -m "refactor(indrec): move the universe codes into a Universes module"
  git show HEAD --color=always --color-moved=dimmed-zebra
  ```

  (In colocated mode git `HEAD` tracks `@-`, the commit just created;
  if it does not, resolve the commit hash from `jj log`.) Expected:
  the moved declaration blocks render as moved lines (not add/delete
  edit pairs); the only non-moved changes are the docstring and
  umbrella edits above.

---

## Task 2: relocate `section Container`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Container.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean`

**Interfaces:**

- Consumes: `IR`, `IR.iota`/`sigma`/`delta` (from `Basic.lean`),
  `PFunctor` (from `Basic.lean`'s public
  `Mathlib.Data.PFunctor.Univariate.Basic` import).
- Produces: the declaration `contCode` — unchanged name, statement,
  and proof term — now exported from
  `Geb.Mathlib.Data.PFunctor.IndRec.Container`.

- [ ] **Step 1: Create the test module (failing).** Create
  `GebTests/Mathlib/Data/PFunctor/IndRec/Container.lean` with this
  scaffolding:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Container

  /-!
  # Tests for container codes

  A container is translated to an `IR` code over the unit type by
  `contCode`; `rfl` tests check that an interpreted name decodes to
  the unit element, including at separated arity universes.

  ## Tags

  inductive-recursive, container
  -/

  @[expose] public section

  open CategoryTheory IndRec
  ```

  then, below the `open` line, the whole of `section Container` …
  `end Container` of `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`
  (pre-branch lines 308–354; declarations `testCont`, `testContCode`,
  `testContX`, `testContSep`, `testContSepCode`, `testContSepX` and
  their `example`s) with the `section Container`/`end Container`
  wrapper dropped and everything else moved verbatim, including any
  leading comment lines inside the section.

  Register the module in BOTH umbrellas:
  `Geb/Mathlib/Data/PFunctor/IndRec.lean` gains

  ```lean
  public import Geb.Mathlib.Data.PFunctor.IndRec.Container
  ```

  after the `Universes` import, and
  `GebTests/Mathlib/Data/PFunctor/IndRec.lean` gains

  ```lean
  import GebTests.Mathlib.Data.PFunctor.IndRec.Container
  ```

  after its `Universes` import.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL — the import
  `Geb.Mathlib.Data.PFunctor.IndRec.Container` does not exist yet.

- [ ] **Step 3: Implement the move.** Create
  `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

  /-!
  # Simple containers as IR codes over the unit type

  A simple container — a shape type `S` and a direction family
  `P : S → Type` — is mathlib's `PFunctor`. Example 1 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013] represents such a
  container by an `IR` code over the unit type (the paper's `IR 1 1`):
  a `sigma` over the shapes, then for each shape a `delta` over its
  directions, terminating in the constant `iota` code at the unit. The
  initial algebra of the code's interpretation amounts to Martin-Löf's
  well-ordering type (the paper's `W S P`; mathlib's `WType`); the
  initial algebra itself is not constructed here.

  ## Main definitions

  * `contCode` — the `IR` code over the unit type representing a
    simple container (a `PFunctor`), following Example 1 of
    [HancockMcBrideGhaniMalatestaAltenkirch2013].

  ## References

  * [HancockMcBrideGhaniMalatestaAltenkirch2013]

  ## Tags

  inductive-recursive, container, polynomial functor
  -/

  @[expose] public section

  universe uA uB uI uO

  namespace IndRec
  ```

  (no `open CategoryTheory`: `contCode` uses only `IR` and
  `PFunctor`) then, below the `namespace IndRec` line, the `contCode`
  declaration of
  `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (its `/-- … -/`
  docstring and `def contCode … := …` body, pre-branch lines
  1156–1164) moved verbatim — the `section Container`/`end Container`
  wrapper and the `/-! ### Simple containers … -/` header block
  (absorbed into the module docstring above) are dropped. Close the
  file with:

  ```lean
  end IndRec
  ```

  In `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`:

  - Delete the remainder of the moved region: `section Container`
    through `end Container` (pre-branch lines 1141–1166) and the
    blank line separating it from `end IR`, so the file ends
    `end IR` … blank line … `end IndRec`.
  - In the module docstring's title paragraph, delete the final
    sentence "Example 1 of the same paper supplies the container code
    `contCode`."
  - In `## Main definitions`, delete the bullet

    ```markdown
    * `contCode` — the `IR` code over the unit type representing a simple
      container (a `PFunctor`), following Example 1 of
      [HancockMcBrideGhaniMalatestaAltenkirch2013].
    ```

  - In `## Tags`, change the line to

    ```markdown
    inductive-recursive, polynomial functor, W-type
    ```

  In `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`:

  - Delete `section Container` through `end Container` and one of
    the two blank lines around it, leaving exactly one blank line
    between `end Heterogeneous` and `section Precomp`.
  - In the module docstring, delete the container paragraph ("A
    container is translated to an `IR` code over the unit type …").
  - In `## Tags`, change the line to

    ```markdown
    inductive-recursive, polynomial functor
    ```

- [ ] **Step 4: Run the tests to verify success, and verify content
  preservation.**

  Run: `lake build && lake test`
  Expected: PASS.

  Run: `jj diff` and eyeball: the only changes to the two
  `Basic.lean` files are deletions of the moved regions and the
  docstring edits above; the new files contain the moved text
  unchanged.

  Run:

  ```bash
  grep -c "contCode" Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean \
    GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean
  ```

  Expected: `<file>:0` for both files; `grep -c` exits non-zero on
  zero matches — that is the expected outcome.

- [ ] **Step 5: Commit, then verify the move rendering.**

  ```bash
  jj commit -m "refactor(indrec): move the container code into a Container module"
  git show HEAD --color=always --color-moved=dimmed-zebra
  ```

  Expected: the `contCode` block and the container test block render
  as moved lines; the only non-moved changes are the docstring and
  umbrella edits above.

---

## Task 3: docs split and gates

**Files:**

- Modify: `docs/index.md`

**Interfaces:**

- Consumes: everything above.
- Produces: the branch's persistent documentation and a passing
  pre-push gate.

- [ ] **Step 1: Split the `docs/index.md` entry.** In the
  `Geb/Mathlib/Data/PFunctor/IndRec/` entry, delete the two sentences

  > `univCode` instantiates the theory: the code of the universe
  > generated by an arbitrary family of starting types and closed
  > under dependent sums and dependent products (Examples 2.5 and 2.6,
  > combined and generalized), with interpretation maps
  > `univEndo`/`univEndoMor`. `contCode` translates a simple container
  > (a `PFunctor`) to an `IR` code over the unit type
  > (Hancock–McBride–Ghani–Malatesta–Altenkirch Example 1).

  and after the `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` entry
  add:

  ```markdown
  - `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean` — `univCode`
    instantiates the theory: the code of the universe generated by an
    arbitrary family of starting types and closed under dependent sums
    and dependent products (Ghani–Nordvall Forsberg–Malatesta
    Examples 2.5 and 2.6, combined and generalized), assembled from
    constructor subcodes (`univBinder`, `univSigma`, `univPi`,
    `univIota`, `univConstructorCode` over the constructor index
    `UnivConstructor`), with interpretation maps
    `univEndo`/`univEndoMor`. `Classical.choice`-free.
  - `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean` — `contCode`
    translates a simple container (a `PFunctor`) to an `IR` code over
    the unit type (Hancock–McBride–Ghani–Malatesta–Altenkirch
    Example 1). `Classical.choice`-free.
  ```

- [ ] **Step 2: Regenerate TOCs and lint.**

  Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
  Expected: TOCs unchanged or updated; lint passes.

- [ ] **Step 3: Full gates.**

  Run: `lake build && lake test && lake lint && scripts/lint-imports.sh`
  Expected: all pass; axiom linter reports no declaration outside
  `{propext, Quot.sound}`.

  Then run `scripts/pre-push.sh` and confirm it passes (it catches
  umbrella-registration gaps and import-minimization failures).

- [ ] **Step 4: Commit.**

  ```bash
  jj commit -m "doc(indrec): split the index entries for the relocated modules"
  ```

---

## Final verification (whole branch)

- [ ] Run `scripts/pre-push.sh` once more on the completed branch.
- [ ] Content-preservation review over the whole branch:
  `git diff main --color=always --color-moved=dimmed-zebra` — every
  moved
  declaration block renders as a move; the declaration lists before
  and after are identical (`univBinder`, `univSigma`, `univPi`,
  `univIota`, `UnivConstructor`, `univConstructorCode`, `univCode`,
  `univEndo`, `univEndoMor`, `contCode`, and the test declarations
  `stepIota`, `stepSigma`, `stepPi`, `NatFinIdx`, `NatFinTypes`,
  `natFinEndo`, `stage0`–`stage3`, `natName`, `finName`, `natName2`,
  `finSuccFamily`, `sigmaName`, `piName`, `sigmaPiName`, `testCont`,
  `testContCode`, `testContX`, `testContSep`, `testContSepCode`,
  `testContSepX`).
- [ ] `#print axioms` (via `lean_verify` or a scratch snippet) on
  `IndRec.univEndoMor` and `IndRec.contCode`: expected ⊆
  `{propext, Quot.sound}` (unchanged from before the move).
- [ ] Run the `lean4:review` skill and `pr-review-toolkit:review-pr`
  on the branch, per the phase table; fold fixes into their owning
  task commits with `jj absorb`/`jj squash`.
- [ ] Confirm the spec, the plans, and the handoffs remain in the
  working tree (they are removed only at the end of branch 2d, per
  CONTRIBUTING § Concern shape).
- [ ] Write the next session's handoff (branch 2c: naturality and
  Theorem 3) into `docs/superpowers/handoffs/`, carrying forward the
  relocation handoff's After-this-branch sections (the 2c
  deliverables, the Lemma-3/Lemma-4 naturality upgrade budget, the
  de-risk note, the candidate `TODO.md` "Tests:" item, the statement
  universes) and the 2d section.
