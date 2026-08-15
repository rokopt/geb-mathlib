# GebLang library and pipelines implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Executor context](#executor-context)
- [File structure](#file-structure)
- [Task 1: the `GebLang` library and its placeholder module](#task-1-the-geblang-library-and-its-placeholder-module)
- [Task 2: the `GebTests/Lang/` placeholder test](#task-2-the-gebtestslang-placeholder-test)
- [Task 3: the literate pipeline](#task-3-the-literate-pipeline)
- [Task 4: doc-gen4 rendering of the library](#task-4-doc-gen4-rendering-of-the-library)
- [Task 5: CI and pre-push wiring](#task-5-ci-and-pre-push-wiring)
- [Task 6: documentation with no floodgate change](#task-6-documentation-with-no-floodgate-change)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** add the `GebLang` library, its placeholder module and test,
and the two documentation pipelines that render it, with no change to
any allowed-import list.

**Architecture:** `GebLang` is a top-level Lean library, sibling to
`Geb`, whose sources are ordinary Lean files carrying Verso-checked
docstrings (`doc.verso = true`, set for this library alone). The same
sources feed `doc-gen4` (the API reference) and Verso's literate
pipeline (a static site scoped by `literate.toml` and driven by
`scripts/literate.sh`). Nothing in this plan widens an allowed-import
list, so the floodgate invariant is untouched throughout.

**Tech Stack:** Lean 4 (`v4.34.0-rc1`), Lake, mathlib, Batteries,
Cslib, Verso (`v4.34.0-rc1`), doc-gen4 (`v4.34.0-rc1`), bash, GitHub
Actions, `jj`.

**Spec:** `docs/superpowers/specs/2026-08-15-geblang-literate-design.md`

This is the first of the two plans that spec mandates
(§ Import rules). The second,
`docs/superpowers/plans/2026-08-15-geblang-floodgate.md`, executes
after this one and carries every floodgate change: the
`scripts/lint-imports.sh` revision, the transitive-import check, the
`scripts/extract-pr.sh` extension, the rule documents, and the
`TODO.md` resolutions.

## Global constraints

Copied from the spec and the repository rules; every task's
requirements implicitly include this section.

- Lean sources: `module` keyword after the copyright block; no
  `noncomputable`; `Classical` minimised; 2-space indentation; 100
  characters maximum per line; mathlib naming (`UpperCamelCase` for
  `Type`-valued and `Prop`-valued declarations, `lowerCamelCase` for
  other terms); mandatory module docstring and mandatory declaration
  docstrings; no development-history references in docstrings.
- Copyright header form, verbatim:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  ```

- `GebLang` docstrings are Verso markup (`doc.verso = true` on that
  library alone). Verso headers are `#` lines, list items start with
  `*` and not with `-`, and a checked constant reference is written
  ``{name}`Foo` ``. Every other library keeps mathlib-conventional
  Markdown docstrings.
- `GebLang/` modules import only `Mathlib.*`, `Batteries.*`, `Cslib.*`
  and `GebLang.*`. The `GebLang.lean` umbrella additionally imports
  `GebMeta`, as `Geb.lean` and `GebTests.lean` do.
- The self-prefix `GebLang.` appears only in the module path of an
  import line: not in namespace declarations, declaration bodies,
  docstrings or comments. The same holds for `GebTests.Lang.` in
  `GebTests/Lang/`. Plan 2 makes `scripts/lint-imports.sh` enforce
  this; the sources this plan writes already satisfy it.
- `lintDriverArgs` stays `["Geb"]`. `GebLang` is linted by an explicit
  `lake lint -- GebLang`, the `GebTests` pattern.
- Markdown: 80-character lines outside tables and code blocks;
  `doctoc` markers in every committed document with more than one `##`
  heading; internal links are repository-relative paths.
- Commit subjects: `<type>(<scope>): <subject>`, imperative present
  tense, lowercase first letter, no trailing period, under 72
  characters (`scripts/check-commit-msg.sh`).

## Executor context

Context a fresh executor cannot recover from the spec.

- **Version control is `jj`, not raw `git`.** Mutating raw `git`
  commands are blocked by a `PreToolUse` hook. Commit with
  `jj commit -m '...'`; after `jj commit` the working copy is already
  a fresh empty change, so do not run `jj new` afterward. Advance the
  bookmark after each commit with
  `jj bookmark move feat/geblang-literate --to @-`. Never push.
- **Markdown writes are hook-linted** at error level by Vale and
  `markdownlint-cli2`. Vale rejects spaced em dashes, the Latin
  abbreviation for `for example`, the capitalised spelling of
  `Cslib`, the clipped form of `repository`, and colloquialisms. Its
  project vocabulary is
  `styles/config/vocabularies/GebMathlib/accept.txt`, one term per
  line; add a genuinely recurring technical term there rather than
  contorting prose, and reword a one-off informal word instead.
  Identifiers inside backticks are outside Vale's scope, so write
  `GebLang` in backticks in prose.
- **Build costs.** `lake build GebLang` is cheap. The first
  `lake build :literateHtml` compiles the `verso-literate`
  executables from source and takes minutes; later runs after a
  docstring edit are incremental. Run `lake exe cache get` before the
  first build in a cold workspace.
- **Foreground `sleep` is blocked** for executors. Poll a served site
  with `curl --retry` rather than sleeping, and clean up with
  `pkill -f verso-serve`.
- **Never use `lake env lean`**; it drops `lakefile.toml` options and
  reports spurious errors. Use `lake build`.
- **Script self-tests stage synthetic trees.** Read
  `scripts/tests/test-lint-imports.sh` and
  `scripts/tests/test-extract-pr.sh` for the fixture pattern before
  writing any test in plan 2. This plan changes only
  `scripts/tests/test-lint-driver.sh`, which runs against the real
  tree.
- **Verification before completion.** A task is complete when its
  commands have been run and their output read. Report the output;
  do not infer a pass.

## File structure

Created by this plan:

- `GebLang.lean` (umbrella; imports `GebMeta` and the library's
  modules; its module docstring is the literate site's landing page).
- `GebLang/Basic.lean` (the placeholder module; one declaration with a
  Verso-checked docstring).
- `GebTests/Lang.lean` (index for the test subdirectory).
- `GebTests/Lang/Basic.lean` (the placeholder test).
- `literate.toml` (literate site configuration, repository root).
- `scripts/literate.sh` (build and serve verbs).

Modified by this plan: `lakefile.toml`, `GebTests.lean`, `ci.yml`,
`doc-build.yml`, `scripts/pre-push.sh`,
`scripts/tests/test-lint-driver.sh`, `docs/rules/lean-coding.md`,
`docs/rules/ci-and-workflow.md`, `TODO.md`. `README.md` is left to
plan 2, which revises it in the one pass the spec's § Standards and
rule documents calls for.

## Task 1: the `GebLang` library and its placeholder module

**Files:**

- Modify: `lakefile.toml`
- Create: `GebLang.lean`
- Create: `GebLang/Basic.lean`

**Interfaces:**

- Consumes: nothing.
- Produces: the Lake library target `GebLang`, which
  `lake build GebLang`, `lake lint -- GebLang` and
  `lake build GebLang:docs` each accept; the declaration
  `gebLangAnchor : Nat`, which Task 2's test asserts against.

- [ ] **Step 1: add the library to `lakefile.toml`**

Change line 2 from

```toml
defaultTargets = ["Geb"]
```

to

```toml
defaultTargets = ["Geb", "GebLang"]
```

`GebLang` is ordinary Lean code whose import closure the default build
already provides, so it belongs in the default build (unlike the
manual). Leave `lintDriverArgs = ["Geb"]` unchanged.

- [ ] **Step 2: declare the library**

Insert the following after the `GebMeta` library block (after
`name = "GebMeta"`, before the `# The Verso manual:` comment block):

```toml
# The Geb language, in Verso's literate style. `doc.verso` switches
# this library's docstrings to checked Verso markup, which both
# doc-gen4 and the literate pipeline render; it is set per-library so
# the upstream-eligible subtrees keep mathlib-conventional Markdown
# docstrings, which render correctly in consumers that do not set the
# option.
[[lean_lib]]
name = "GebLang"
globs = ["GebLang.*"]

[lean_lib.leanOptions]
doc.verso = true
```

A `[lean_lib.leanOptions]` table attaches to the `[[lean_lib]]` entry
above it; this is the same shape the `GebTests` and `GebManual`
entries already use.

- [ ] **Step 3: write the placeholder module**

Create `GebLang/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

/-!
# Anchor for the Geb language's core data structures

The library's content occupies this module. Its prose is the
literate site's page for the module and doc-gen4's module
description, so the module anchors both documentation pipelines
against a source with a docstring of each kind.

## Main definitions

* {name}`gebLangAnchor`, the declaration whose docstring exercises
  the declaration-level pipeline.

## Tags

geb, language
-/

@[expose] public section

/-- A declaration whose docstring renders in both of the library's
documentation pipelines: as page prose in the literate site, and in
doc-gen4's reference. Its checked {name}`Nat` reference elaborates
under `doc.verso`. -/
def gebLangAnchor : Nat := 0
```

The declaration is replaced, not grown, when content lands; Task 6
records that expectation in `TODO.md`. Note the Verso list marker
`*`, the `{name}` roles, and the absence of the `GebLang.` prefix
anywhere outside an import path.

- [ ] **Step 4: write the umbrella**

Create `GebLang.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all, shake: keep-downstream

public import GebLang.Basic

import GebMeta

/-!
# The Geb language

`GebLang` holds the core data structures of the Geb language. It sits
at the bottom of this repository's dependency order: its modules
import mathlib, Batteries and Cslib, and each other, and every other
library here may import them.

The library is written in Verso's literate style. A module docstring
is the prose of the module's page, and declaration docstrings render
as prose beside their highlighted code. The same sources feed
doc-gen4's API reference.

## Main definitions

* {name}`gebLangAnchor`, in `GebLang.Basic`.
-/
```

The `-- shake: keep-all, shake: keep-downstream` annotation on the
`module` line matches `Geb.lean` and `GebTests.lean` and keeps the
widened `lake shake` from flagging the index imports. The `GebMeta`
import registers the axiom linter for `lake lint -- GebLang`.

- [ ] **Step 5: build the library**

Run: `lake build GebLang`

Expected: exit 0, no warnings. A Verso parse error in a docstring
reports at the docstring's position; the two docstring dialects differ
in list markers (`*`, not `-`) and in role syntax.

- [ ] **Step 6: lint the library**

Run: `lake lint -- GebLang`

Expected: exit 0, and the output names the axiom linter's
`All declarations depend only on permitted axioms.` result. This
confirms the umbrella's `GebMeta` import registers
`GebMeta.detectNonstandardAxiom` for this root module, and that the
placeholder passes it.

- [ ] **Step 7: confirm the default build covers the library**

Run: `lake build`

Expected: exit 0, and `GebLang` among the targets built (the
`defaultTargets` change of Step 1).

- [ ] **Step 8: commit**

```bash
jj commit -m 'feat(geblang): add the GebLang library and its anchor module'
jj bookmark move feat/geblang-literate --to @-
```

## Task 2: the `GebTests/Lang/` placeholder test

**Files:**

- Create: `GebTests/Lang.lean`
- Create: `GebTests/Lang/Basic.lean`
- Modify: `GebTests.lean`

**Interfaces:**

- Consumes: `gebLangAnchor : Nat` from `GebLang.Basic` (Task 1).
- Produces: `GebTests.Lang` reachable from the `GebTests` umbrella, so
  the test driver and `lake lint -- GebTests` reach it.

- [ ] **Step 1: write the test module**

Create `GebTests/Lang/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebLang.Basic
public meta import GebLang.Basic

/-!
# Tests for the Geb language's anchor module

The anchor declaration evaluates to its stated value, exercising the
test driver against the `GebLang` library.

## Tags

geb, language
-/

@[expose] public section

#guard gebLangAnchor = 0
```

The `public meta import` beside the ordinary `public import` is the
sanctioned repair for a `#guard` whose wrapper calls a non-`meta`
declaration from another module of this package: `#guard` runs its
argument in the interpreter, and the interpreter needs the imported
module's IR available to meta code. The LSP is not an oracle for this,
so the claim is settled by `lake build` alone
(`docs/rules/lean-coding.md` § Lean 4 module system).

The docstrings here are mathlib-conventional Markdown: `doc.verso` is
set for the `GebLang` library, not for `GebTests`.

- [ ] **Step 2: write the subdirectory index**

Create `GebTests/Lang.lean`, following `GebTests/Mathlib.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Lang.Basic

/-!
# GebTests.Lang — tests for the GebLang library
-/
```

- [ ] **Step 3: reach the index from the test umbrella**

In `GebTests.lean`, add `public import GebTests.Lang` to the import
block, keeping alphabetical order:

```lean
public import GebTests.Cslib
public import GebTests.Internal
public import GebTests.Lang
public import GebTests.Mathlib
```

and extend the module docstring's mirror sentence, which currently
reads

```text
Test library root. Mirrors `Geb.lean` structure: `GebTests.Mathlib`
tests `Geb.Mathlib`; `GebTests.Cslib` tests `Geb.Cslib`;
`GebTests.Internal` tests `Geb.Internal`.
```

to

```text
Test library root. Mirrors `Geb.lean` structure: `GebTests.Mathlib`
tests `Geb.Mathlib`; `GebTests.Cslib` tests `Geb.Cslib`;
`GebTests.Internal` tests `Geb.Internal`. `GebTests.Lang` tests
`GebLang`, whose sources are a sibling library rather than a `Geb`
subtree.
```

- [ ] **Step 4: run the test driver**

Run: `lake test`

Expected: exit 0. A failing `#guard` reports at its own line; a
missing `public meta import` reports as an interpreter failure rather
than an elaboration error.

- [ ] **Step 5: lint the test library**

Run: `lake lint -- GebTests`

Expected: exit 0.

- [ ] **Step 6: commit**

```bash
jj commit -m 'test(geblang): add the GebTests.Lang placeholder test'
jj bookmark move feat/geblang-literate --to @-
```

## Task 3: the literate pipeline

**Files:**

- Create: `literate.toml`
- Create: `scripts/literate.sh`

**Interfaces:**

- Consumes: the `GebLang` library target (Task 1).
- Produces: `bash scripts/literate.sh build` and
  `bash scripts/literate.sh serve`; the site path printed by
  `lake query :literateHtml`, which Task 5 uploads as a CI artifact.

- [ ] **Step 1: write `literate.toml`**

Create `literate.toml` at the repository root:

```toml
# Verso literate site configuration. The [[targets]] entry scopes the
# site to the GebLang library: the literateHtml package facet
# otherwise enumerates every library and executable of the package,
# so an unscoped run would render and build Geb, GebTests, GebMeta,
# GebManual and the manual generator's Main. The filter runs in the
# planner before any module is fetched, so the scoping also bounds
# what is compiled.
#
# The root-level keys precede the table headers: a key placed after
# [[targets]] becomes a key of that target entry and is silently
# ignored by the target decoder.
docstrings_as_text = true
landing_page = "GebLang"

[metadata]
title = "The Geb language"

[[targets]]
library = "GebLang"
```

Ordering, per-module titles and themes are deferred until content
exists (spec § Literate rendering).

- [ ] **Step 2: write `scripts/literate.sh`**

Create `scripts/literate.sh`, mirroring `scripts/manual.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/literate.sh
#
# Build or serve the Verso literate site for the GebLang library.
# Runs from the repository root regardless of the invoking directory:
# literate.toml, the site's output path, and the lint's nolints path
# (scripts/nolints.json) are all resolved against the working
# directory.
#
# CI (doc-build.yml) runs the build verb. The library itself is in
# defaultTargets, so an ordinary lake build compiles it; only the
# rendering is confined to this script.

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

case "${1:-}" in
  build)
    lake build GebLang
    lake lint -- GebLang
    lake build :literateHtml
    ;;
  serve)
    exec lake exe verso-serve "$(lake query :literateHtml)"
    ;;
  *)
    cat >&2 <<'EOF'
usage: scripts/literate.sh {build|serve}

  build  Build the GebLang library, lint it, and render the literate
         site. The first run compiles Verso's literate executables
         from source, which takes minutes; later runs are
         incremental.
  serve  Serve the rendered site with verso-serve, which prints the
         URL it binds (port 8000, or a higher free port when 8000 is
         taken).

There is no watch mode: after editing a docstring, re-run 'build' and
refresh the browser. Lake rebuilds only the changed modules.
EOF
    exit 2
    ;;
esac
```

Build precedes lint so a clean checkout lints built oleans, as
`scripts/manual.sh` does.

- [ ] **Step 3: make the script executable**

Run: `chmod +x scripts/literate.sh`

- [ ] **Step 4: check the usage path**

Run: `bash scripts/literate.sh; echo "exit=$?"`

Expected: the usage text on stderr and `exit=2`.

- [ ] **Step 5: build the site**

Run: `bash scripts/literate.sh build`

Expected: exit 0. The first run compiles `verso-literate`,
`verso-literate-plan` and `verso-literate-html` from source and takes
minutes.

- [ ] **Step 6: confirm `lake query` prints only the path**

Run: `lake query :literateHtml`

Expected: a single line naming a directory under `.lake/build`. The
`serve` verb and the CI artifact upload both consume this output as a
path, so any extra line breaks them. If the command prints more than
the path, record the deviation and stop; do not work around it.

- [ ] **Step 7: confirm the site's scope**

Run:

```bash
ls "$(lake query :literateHtml)"
grep -rl 'GebManual\|GebMeta\|GebTests' "$(lake query :literateHtml)" || echo 'no foreign module pages'
```

Expected: the second command prints `no foreign module pages`. No
`Geb`, `GebTests`, `GebMeta` or `GebManual` module, and not the
manual generator's `Main`, appears in the site (spec § Verification).

- [ ] **Step 8: serve the site and inspect both pages**

Run:

```bash
bash scripts/literate.sh serve &
curl --retry 10 --retry-delay 1 --retry-connrefused -s http://localhost:8000/ -o /tmp/literate-landing.html
curl --retry 5 --retry-connrefused -s http://localhost:8000/ -w '%{http_code}\n' -o /dev/null
```

Expected: HTTP 200. Read `/tmp/literate-landing.html` and confirm the
landing page carries the umbrella's prose, then locate the
`GebLang.Basic` page and confirm the `{name}` roles render as resolved
references rather than as literal braces. If `verso-serve` binds a
higher port, take the port from its own output.

Clean up: `pkill -f verso-serve`

- [ ] **Step 9: commit**

```bash
jj commit -m 'feat(geblang): add the literate site config and command'
jj bookmark move feat/geblang-literate --to @-
```

## Task 4: doc-gen4 rendering of the library

**Files:**

- Modify: `TODO.md` (only in the conditional branch of Step 3)

**Interfaces:**

- Consumes: the `GebLang` library target (Task 1).
- Produces: the verified fact that the pinned doc-gen4 renders
  Verso-format docstrings, which Task 5 relies on when adding
  `lake build GebLang:docs` to `doc-build.yml`, and which plan 2's
  `TODO.md` task cites when revising § Verso adoption.

- [ ] **Step 1: build the documentation**

Run: `lake build GebLang:docs`

Expected: exit 0.

- [ ] **Step 2: inspect the rendered docstrings**

Run:

```bash
grep -o '{name}' .lake/build/doc/GebLang/Basic.html | head
grep -c 'gebLangAnchor' .lake/build/doc/GebLang/Basic.html
```

Expected: the first command prints nothing (the role markup is
resolved, not rendered literally) and the second prints a non-zero
count. The pinned doc-gen4 (`v4.34.0-rc1`) carries
`DocGen4/DB/VersoDocString.lean`, the Verso docstring renderer, so
this is the expected outcome.

- [ ] **Step 3: record a gap only if one appears**

If, and only if, Step 2 shows literal `{name}` markup in the output,
the pin predates doc-gen4's Verso support. In that case the docstring
still renders legibly as text; append to `TODO.md` § Triggers:

```markdown
- **doc-gen4 renders `GebLang` Verso roles literally**: the pinned
  doc-gen4 emits the `{name}` role markup verbatim rather than as a
  resolved reference, so the API reference shows braces where the
  literate site shows a link. Trigger: the next doc-gen4 pin bump,
  at which point the rendering is re-checked and this entry is
  removed once it resolves.
```

Otherwise make no edit and record in the task report that the pinned
doc-gen4 renders the roles resolved.

- [ ] **Step 4: commit only if Step 3 added an entry**

```bash
jj commit -m 'doc(geblang): record the doc-gen4 Verso rendering gap'
jj bookmark move feat/geblang-literate --to @-
```

If Step 3 made no edit, there is nothing to commit; proceed to Task 5.

## Task 5: CI and pre-push wiring

**Files:**

- Modify: `.github/workflows/ci.yml`
- Modify: `.github/workflows/doc-build.yml`
- Modify: `scripts/pre-push.sh`
- Modify: `scripts/tests/test-lint-driver.sh`

**Interfaces:**

- Consumes: `lake lint -- GebLang`, `lake build GebLang:docs`,
  `bash scripts/literate.sh build`, `lake query :literateHtml` (Tasks
  1, 3, 4).
- Produces: the `geb-literate` CI artifact; the
  `check_coverage GebLang ""` scan and the
  `scripts/literate.sh build` workflow-literal guard in
  `scripts/tests/test-lint-driver.sh`.

- [ ] **Step 1: extend `ci.yml`'s build job**

In `.github/workflows/ci.yml`, replace the comment and step at lines
70 to 76,

```yaml
      # `lake shake` requires built oleans for every library it
      # scans. `build: true` above honours `defaultTargets` (Geb
      # only), so build `GebTests` explicitly here.
      - name: lake build GebTests (prerequisite for lake shake)
        run: lake build GebTests
      - name: lake lint GebTests (axiom + style linters on tests)
        run: lake lint -- GebTests
```

with

```yaml
      # `lake shake` requires built oleans for every library it
      # scans. `build: true` above honours `defaultTargets` (Geb and
      # GebLang), so build `GebTests` explicitly here.
      - name: lake build GebTests (prerequisite for lake shake)
        run: lake build GebTests
      - name: lake lint GebTests (axiom + style linters on tests)
        run: lake lint -- GebTests
      - name: lake lint GebLang (axiom + style linters on the language library)
        run: lake lint -- GebLang
```

and widen the shake step at line 82 from

```yaml
        run: lake shake --add-public --keep-implied --keep-prefix Geb GebTests
```

to

```yaml
        run: lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang
```

- [ ] **Step 2: extend `doc-build.yml`**

In `.github/workflows/doc-build.yml`, extend the paths filter (lines 8
to 16) to

```yaml
    paths:
      - 'Geb/**'
      - 'GebLang.lean'
      - 'GebLang/**'
      - 'GebTests/**'
      - 'docs/**'
      - 'lakefile.toml'
      - 'lean-toolchain'
      - 'literate.toml'
      - 'manual/**'
      - 'scripts/literate.sh'
      - 'scripts/manual.sh'
      - 'scripts/nolints.json'
```

and append to the steps, after the existing manual upload:

```yaml
      - run: lake build GebLang:docs
      - run: bash scripts/literate.sh build
      - name: Locate the generated literate site
        run: echo "LITERATE_HTML=$(lake query :literateHtml)" >> "$GITHUB_ENV"
      - name: Upload the generated literate site
        uses: actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a  # v7.0.1
        with:
          name: geb-literate
          path: ${{ env.LITERATE_HTML }}
          if-no-files-found: error
```

`lake build GebLang:docs` is placed with the other doc-gen4 build
rather than inside `scripts/literate.sh`, which drives the literate
product alone. The upload-artifact SHA is the one already pinned twice
in this file; keep the tag comment.

- [ ] **Step 3: extend `scripts/pre-push.sh`**

Four edits.

Add the lint step after the existing `lake lint -- GebTests` step
(after line 69):

```bash
step "lake lint GebLang (axiom + style linters on the language library)"
lake lint -- GebLang
```

Widen the shake step (line 72) to

```bash
lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang
```

Update the two comments that name the root libraries. The comment at
lines 62 to 64 becomes

```bash
# `lake shake` requires built oleans for every library it scans.
# `lake build` alone honours `defaultTargets` (Geb and GebLang), so
# build `GebTests` explicitly here.
```

and the cache-fetch rationale sentence at lines 17 to 19 becomes

```bash
# Fetch the full mathlib olean cache, mirroring CI's
# leanprover/lean-action. Without it, after a toolchain bump only
# the oleans that the root libraries `Geb` and `GebLang` directly
# import are present, and the
```

leaving the rest of that comment paragraph unchanged.

Widen the docs-coverage reminder. Line 149 becomes

```bash
if diff_against_main | grep -qE '^(Geb/Mathlib|Geb/Cslib|Geb/Internal|GebLang)/.*\.lean$'; then
```

and the reminder's message text (lines 153 to 155) becomes

```bash
    echo "  Lean files under Geb/Mathlib/, Geb/Cslib/," >&2
    echo "  Geb/Internal/, or GebLang/ changed, but" >&2
    echo "  docs/index.md was not touched. Verify each new" >&2
    echo "  concept is reflected in docs/index.md." >&2
```

replacing the four existing `echo` lines of that block. Update the
stub-implementation comment at lines 138 to 140 in the same edit, so
it names the same four directories:

```bash
# Stub implementation: surface a reminder when .lean files in
# Geb/Mathlib/, Geb/Cslib/, Geb/Internal/, or GebLang/ change
# without docs/index.md being touched in the same branch's diff.
```

- [ ] **Step 4: extend `scripts/tests/test-lint-driver.sh`**

Three edits.

Add the coverage scan after line 96
(`check_coverage GebManual "manual/"`):

```bash
check_coverage GebLang ""
```

`GebLang` lives at the package root, so the existing generalization
applies with an empty prefix, as for `Geb`.

Extend the workflow check at lines 98 to 104 to one literal per
product:

```bash
# --- 3. doc-build.yml retains the product build steps ----------------
# The manual is linted only by scripts/manual.sh build, and the
# literate site is rendered only by scripts/literate.sh build, both in
# doc-build.yml; losing either step would silently drop that product.
if ! grep -qF 'scripts/manual.sh build' .github/workflows/doc-build.yml; then
  echo "FAIL: doc-build.yml lost the 'scripts/manual.sh build' step" >&2
  failed=1
fi
if ! grep -qF 'scripts/literate.sh build' .github/workflows/doc-build.yml; then
  echo "FAIL: doc-build.yml lost the 'scripts/literate.sh build' step" >&2
  failed=1
fi
```

Update the header comment's two affected sentences. In the numbered
list, item 2's first sentence becomes

```bash
#   2. Coverage completeness: every `Geb.*`, `GebLang.*` and
#      `GebManual.*` source module is transitively imported by its own
#      umbrella (`Geb`, `GebLang`, `GebManual`), so linting the root
#      module reaches every declaration the no-argument path would
#      have.
```

and item 3 becomes

```bash
#   3. `doc-build.yml` retains the `scripts/manual.sh build` and
#      `scripts/literate.sh build` steps, the only places the manual
#      is linted and the literate site is rendered.
```

Update the `mod_to_file` comment above line 61 so it names the third
library:

```bash
# Module name to file path within a library's srcDir; dots map to
# slashes. Geb and GebLang live at the package root; GebManual under
# manual/ (lakefile.toml srcDir), whose generator root Main is outside
# the GebManual prefix by design and so outside this scan.
```

- [ ] **Step 5: run the lint-driver test**

Run: `bash scripts/tests/test-lint-driver.sh`

Expected: `test-lint-driver: ok`, exit 0. A failure naming `GebLang`
orphans means a `GebLang/` module is unreachable from the umbrella.

- [ ] **Step 6: check the workflow files parse**

Run:

```bash
markdownlint-cli2 '**/*.md' >/dev/null && echo 'markdown ok'
python3 -c 'import yaml,sys; [yaml.safe_load(open(f)) for f in sys.argv[1:]]; print("yaml ok")' \
  .github/workflows/ci.yml .github/workflows/doc-build.yml
```

Expected: `yaml ok`. If `python3` or its `yaml` module is absent, skip
this step and rely on the workflow run after the push.

- [ ] **Step 7: run the shake step the workflows now run**

Run:

```bash
lake build GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang
```

Expected: exit 0. A report against a `GebLang/` module means an
unused import there; remove it rather than suppressing it, unless the
import is needed only for `#guard` evaluation or instance resolution,
in which case `-- shake: keep` is the sanctioned suppression.

- [ ] **Step 8: commit**

```bash
jj commit -m 'ci(geblang): build, lint and render GebLang in CI and pre-push'
jj bookmark move feat/geblang-literate --to @-
```

## Task 6: documentation with no floodgate change

**Files:**

- Modify: `docs/rules/lean-coding.md`
- Modify: `docs/rules/ci-and-workflow.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: everything above.
- Produces: the persistent documentation of the library and its two
  pipelines. Plan 2 carries every remaining documentation change: the
  rule documents' import tables and floodgate sections,
  `docs/index.md` § Directory structure, the whole of `README.md`
  (revised in one pass there, including the § Documentation entry for
  `scripts/literate.sh`), `CONTRIBUTING.md`, `AGENTS.md`,
  `docs/process.md`, the enumeration sweep, and the three `TODO.md`
  resolutions.

- [ ] **Step 1: add the literate conventions to `docs/rules/lean-coding.md`**

Add a TOC entry after `- [Verso manual modules (manual/)](#verso-manual-modules-manual)`:

```markdown
- [Literate modules (GebLang)](#literate-modules-geblang)
```

and add the section itself after § Verso manual modules (manual/),
before § Lean 4 skill workflows:

````markdown
## Literate modules (`GebLang`)

The `GebLang` library is rendered twice from one set of sources: by
doc-gen4 into the API reference, and by Verso's literate pipeline
into a static site (`scripts/literate.sh`, `literate.toml`). Its
docstrings are written for both.

- A module docstring is the prose of the module's page. Declaration
  docstrings render as prose beside their code, which is what
  `docstrings_as_text = true` in `literate.toml` selects.
- `lakefile.toml` sets `doc.verso = true` for the `GebLang` library
  alone, so its docstrings are checked Verso markup rather than
  Markdown: a header is a `#` line, a list item starts with `*`, and
  a checked reference to a constant is written ``{name}`Foo` ``. The
  option is compile-time, so a consumer compiling the same file
  without it renders the markup literally; that is why the
  upstream-eligible subtrees keep mathlib-conventional Markdown
  docstrings.
- Literate sources are ordinary Lean files: no `#doc`, no Verso
  imports, no Verso commands. `linter.hashCommand` stays enabled for
  them, the `module` discipline applies unchanged, and building the
  library compiles no Verso. Verso compiles only when the site is
  rendered.
````

Also extend the axiom-linter sentence in § Constructive-only Lean
code, which currently reads

```markdown
- The `GebMeta.detectNonstandardAxiom` `@[env_linter]` fails
  `lake lint` when any `Geb` or `GebTests` declaration depends on
  an axiom outside its permitted set.
```

to

```markdown
- The `GebMeta.detectNonstandardAxiom` `@[env_linter]` fails
  `lake lint` when any `Geb`, `GebTests` or `GebLang` declaration
  depends on an axiom outside its permitted set.
```

- [ ] **Step 2: extend `docs/rules/ci-and-workflow.md`**

Add a TOC entry after `- [Verso manual build](#verso-manual-build)`:

```markdown
- [Literate site build](#literate-site-build)
```

In § Pre-push checklist, extend the two build bullets. The bullet

```markdown
- `lake build GebTests` then `lake lint -- GebTests`. The axiom
  env_linter (`GebMeta.detectNonstandardAxiom`) runs under both
  `lake lint` invocations (`Geb` and `GebTests`), failing when a
  declaration depends on an axiom outside `{propext, Quot.sound}`,
  except that modules in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only that).
```

becomes

```markdown
- `lake build GebTests` then `lake lint -- GebTests`, then
  `lake lint -- GebLang`. The axiom env_linter
  (`GebMeta.detectNonstandardAxiom`) runs under all three `lake lint`
  invocations (`Geb`, `GebTests` and `GebLang`), failing when a
  declaration depends on an axiom outside `{propext, Quot.sound}`,
  except that modules in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only that).
```

The bullet

```markdown
- `lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests`.
```

becomes

```markdown
- `lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests GebLang`.
```

The `lake exe cache get` bullet's second sentence, which reads

```markdown
  The cache fetch is
  required because `lake build` alone fetches only the oleans
  `Geb` imports;
```

becomes

```markdown
  The cache fetch is
  required because `lake build` alone fetches only the oleans the
  root libraries `Geb` and `GebLang` import;
```

The docs-coverage bullet

```markdown
- Docs-coverage reminder: Lean changes under an upstream-eligible
  or the `Geb/Internal/` subtree without a `docs/index.md` change.
```

becomes

```markdown
- Docs-coverage reminder: Lean changes under an upstream-eligible
  subtree, `Geb/Internal/`, or `GebLang/` without a `docs/index.md`
  change.
```

Add the new section after § Verso manual build:

```markdown
## Literate site build

The literate site (the `GebLang` library rendered by Verso's
literate pipeline) builds only through `scripts/literate.sh build`:
`lake build GebLang`, `lake lint -- GebLang`,
`lake build :literateHtml`, in that order, so a clean checkout lints
built oleans. `literate.toml` scopes the site to the `GebLang`
library; without that scoping the package facet renders and builds
every library and executable of the package. CI runs the script in
`doc-build.yml` and uploads the HTML as the `geb-literate` artifact,
beside `lake build GebLang:docs` for the doc-gen4 reference. The
rendering stays out of the pre-push checklist, as the manual's does,
because the first run compiles Verso from source; the library itself
is in `defaultTargets`, so an ordinary `lake build` compiles it.
`scripts/tests/test-lint-driver.sh` § 3 guards the workflow step.
```

- [ ] **Step 3: revise `TODO.md` § Verso adoption**

In the § Verso adoption entry under § Triggers, replace scope 1,

```markdown
  1. Docstrings in `.lean` files: gated on doc-gen4 gaining Verso-aware
     rendering and mathlib migrating to Verso; contraindicated for
     `Geb/Mathlib/` and `Geb/Cslib/` until both hold (Verso-markup docstrings
     would read as foreign to mathlib reviewers and would not render on the
     doc-gen4 site).
```

with

```markdown
  1. Docstrings in `.lean` files: the doc-gen4 half of the gate is met at
     the pin, which renders Verso-format docstrings
     (`DocGen4/DB/VersoDocString.lean`); the mathlib-migration half is not.
     Still contraindicated for `Geb/Mathlib/` and `Geb/Cslib/`, whose
     Verso-markup docstrings would read as foreign to mathlib reviewers.
     `GebLang` is not gated on the migration: its docstrings are Verso
     markup under `doc.verso`, and `scripts/extract-pr.sh` converts them to
     plain Markdown at extraction, so no unconverted markup reaches an
     upstream reviewer.
```

and extend scope 2's bullet,

```markdown
  2. Persistent prose (`docs/`, a future Geb-language exposition): gated on the
     prose growing substantial and describing stable, existing code.
```

with a following sentence:

```markdown
     The `GebLang` literate site (`scripts/literate.sh`) already renders that
     library's docstrings as exposition, so a Geb-language exposition chooses
     between extending it and a separate Verso document.
```

The `scripts/extract-pr.sh` conversion this text names lands in plan
2; both plans are on the same branch and the branch is not pushed
between them, so the statement is true at every merged state.

- [ ] **Step 4: record the placeholder-replacement expectations**

Add two entries to `TODO.md` § Triggers:

```markdown
- **Replace `GebLang/Basic.lean`**: the module holds one anchor
  declaration so that both documentation pipelines have a module
  docstring and a declaration docstring to render. Trigger: the first
  `GebLang` content workstream, which replaces the module rather than
  growing it.
- **Remove `GebTests/Lang/Basic.lean`**: the module holds one `#guard`
  against the anchor declaration, validating the test driver path and
  the lint path for the `GebLang` library. Trigger: the arrival of
  real `GebTests/Lang/` tests, which supersede it.
```

- [ ] **Step 5: run the Markdown checks**

Run:

```bash
doctoc --update-only . && markdownlint-cli2 '**/*.md' && bash scripts/check-md-links.sh
```

Expected: exit 0 from each. `doctoc` inserts a `**Table of Contents**`
title line into any TOC it regenerates; delete it, since the
repository's TOCs carry none. If `doctoc` is absent, verify the two
TOC entries added in Steps 1 and 2 by hand.

- [ ] **Step 6: commit**

```bash
jj commit -m 'doc(geblang): document the library and its two pipelines'
jj bookmark move feat/geblang-literate --to @-
```

- [ ] **Step 7: run the full pre-push checklist**

Run: `bash scripts/pre-push.sh`

Expected: exit 0, ending with the `pre-push: clean.` line. This is the
plan's end-to-end verification. The workflow files themselves are
verified by CI after the user's review and push, as for the manual
workstream.
