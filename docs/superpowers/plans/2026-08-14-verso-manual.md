# Verso Manual Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
  - [Task 1: Verso dependency and bump automation](#task-1-verso-dependency-and-bump-automation)
  - [Task 2: Manual skeleton, Lake targets, module-form check](#task-2-manual-skeleton-lake-targets-module-form-check)
  - [Task 3: Lint integration](#task-3-lint-integration)
  - [Task 4: Initial content](#task-4-initial-content)
  - [Task 5: Build-and-serve script](#task-5-build-and-serve-script)
  - [Task 6: CI](#task-6-ci)
  - [Task 7: Lint-driver guard extension](#task-7-lint-driver-guard-extension)
  - [Task 8: Documentation and rule deltas](#task-8-documentation-and-rule-deltas)
  - [Task 9: Full verification](#task-9-full-verification)
  - [After the tasks](#after-the-tasks)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a Verso manual to the repository: the `verso`
dependency, a `manual/` document library and generator, a
build-and-serve script, a CI step, lint accommodations, and an
initial project-overview document.

**Architecture:** One Lake package: a `lean_lib GebManual` and a
`lean_exe geb-manual`, both with `srcDir = "manual"`, generate HTML
into `manual/_out/` via `manualMain`. The manual is outside
`defaultTargets`, the test driver, and pre-push; only
`scripts/manual.sh build` (locally and in `doc-build.yml`) builds
it.

**Tech Stack:** Lean 4 `v4.34.0-rc1`, Lake, Verso `v4.34.0-rc1`
(`Manual` genre), batteries `runLinter`, `jj`, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-08-14-verso-manual-design.md`
(the plan argues from the spec; read both).

## Global Constraints

- The toolchain is `leanprover/lean4:v4.34.0-rc1`; every `rev` in
  `lakefile.toml` is the same tag, rewritten wholesale by
  `update.yml`.
- Commits with `jj` only; the PreToolUse hook blocks mutating raw
  `git`. Messages: `<type>(<scope>): <subject>`, lowercase subject,
  no trailing period (`scripts/check-commit-msg.sh`).
- No pushing; the user reviews line-by-line before any push.
- Markdown: `markdownlint-cli2`, Vale (error level), `doctoc`
  TOCs on files with more than one `##` heading,
  repository-relative internal links.
- `.lean` files: copyright header, then `module` where feasible
  (Task 2 settles feasibility for `#doc` files); mathlib naming and
  docstring rules per `docs/rules/lean-coding.md`.
- The manual never joins `defaultTargets`, `testDriver`, or the
  pre-push checks; `lake build`, `lake test`, and default
  `lake lint` must compile nothing new after every task.
- First `lake build GebManual` compiles Verso from source
  (several minutes); no binary cache covers it.

---

### Task 1: Verso dependency and bump automation

**Files:**

- Modify: `lakefile.toml` (requires section, before `cslib`)
- Modify: `lake-manifest.json` (via `lake update verso`, not by
  hand)
- Modify: `.github/workflows/update.yml:43` (step name only)

**Interfaces:**

- Consumes: nothing from other tasks.
- Produces: the `verso` package in the workspace; later tasks'
  `import VersoManual` and `lake exe verso-serve` resolve through
  it.

- [ ] **Step 1: Record the pins that must not move**

Run:

```bash
grep -B1 -A4 '"name": "plausible"' lake-manifest.json
grep -B1 -A4 '"name": "MD4Lean"' lake-manifest.json
```

Save both `rev` values (for example into scratch notes); Step 4
asserts
they are unchanged.

- [ ] **Step 2: Add the require**

Insert into `lakefile.toml`, above the `[[require]]` for `cslib`
(making `verso` the first require, ahead of both `doc-gen4` and
`mathlib`):

```toml
# Pinned in lockstep with `lean-toolchain`; bump `rev` when bumping
# the toolchain version. Verso's tags are named after Lean
# toolchains; if a bump targets a toolchain Verso has not yet
# tagged, the bump waits for the tag (`update.yml` reports the
# failed update rather than committing it). Declared ahead of
# doc-gen4 and mathlib so that, under Lake's reverse-order root
# resolution, mathlib's plausible pin and doc-gen4's MD4Lean pin
# take precedence over verso's branch-pinned requires.
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.34.0-rc1"
```

- [ ] **Step 3: Materialize**

Run: `lake update verso`
Expected: clones `verso` plus new transitives (`subverso`,
`illuminate`); `MD4Lean` already present. No error. (Network
required.)

- [ ] **Step 4: Verify the manifest diff**

Run: `jj diff lake-manifest.json` and the two `grep`s from Step 1.
Expected: new entries for `verso` (`inputRev` `v4.34.0-rc1`),
`subverso`, `illuminate`; the `plausible` and `MD4Lean` revs are
byte-identical to Step 1. If either moved, stop: the require is in
the wrong position; re-check Step 2 placement.

- [ ] **Step 5: Verify nothing new compiles**

Run: `lake build`
Expected: completes quickly with no Verso modules compiled (the
manual library does not exist yet, and `verso` is not imported by
any default target).

- [ ] **Step 6: Update the bump step name**

In `.github/workflows/update.yml`, change:

```yaml
      - name: Set mathlib, cslib, doc-gen4 revs to the target tag
```

to:

```yaml
      - name: Set verso, mathlib, cslib, doc-gen4 revs to the target tag
```

- [ ] **Step 7: Commit**

```bash
jj commit -m 'chore(deps): add verso pinned to the toolchain tag

Declared ahead of doc-gen4 and mathlib so their MD4Lean and
plausible pins take precedence over verso'"'"'s branch requires
under Lake'"'"'s reverse-order root resolution. The update.yml step
name gains the new member of the rev enumeration it names.'
```

(Note: `scripts/lake-update-warning.sh` will warn about the
manifest change on a non-`bump/*` branch during pre-push; that is
informational and expected here.)

---

### Task 2: Manual skeleton, Lake targets, module-form check

**Files:**

- Modify: `lakefile.toml` (append targets)
- Create: `manual/GebManual.lean`
- Create: `manual/GebManual/Root.lean`
- Create: `manual/Main.lean`
- Modify: `.gitignore` (add `/manual/_out`)

**Interfaces:**

- Consumes: the `verso` package (Task 1).
- Produces: library `GebManual` (root module `GebManual`, document
  root `GebManual.Root` holding `#doc (Manual) "Geb"`), executable
  `geb-manual` (`main : List String → IO UInt32` calling
  `manualMain (%doc GebManual.Root)`), output directory
  `manual/_out/html-multi/`. Tasks 3–8 use these names verbatim.

- [ ] **Step 1: Append the Lake targets**

Append to `lakefile.toml`:

```toml
# The Verso manual: document library and generator executable,
# with sources under manual/. Excluded from defaultTargets and the
# test driver, so lake build, lake test, and the default lake lint
# compile nothing new; scripts/manual.sh build (run by
# doc-build.yml in CI) is the only builder. linter.hashCommand is
# disabled because #doc, the Verso document command, is the
# library's content; verso.code.warnLineLength widens Verso's
# code-line warning to the repository's line width.
[[lean_lib]]
name = "GebManual"
srcDir = "manual"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100
weak.linter.hashCommand = false

[[lean_exe]]
name = "geb-manual"
srcDir = "manual"
root = "Main"
supportInterpreter = true
```

- [ ] **Step 2: Write the library root**

Create `manual/GebManual.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebManual.Root

/-! # GebManual

Library index for the Geb manual.
-/
```

- [ ] **Step 3: Write a minimal document root**

Create `manual/GebManual/Root.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual

open Verso.Genre Manual

/-! # Manual root

The root `Part` of the Geb manual. Chapters are included here.
-/

#doc (Manual) "Geb" =>

The Geb manual.
```

- [ ] **Step 4: Write the generator**

Create `manual/Main.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebManual

open Verso.Genre.Manual

/-! # Generator entry point

Passes the root `Part` to `manualMain`. Outside the `GebManual`
module prefix, so `lake lint -- GebManual` does not reach it.
-/

/-- Generate the Geb manual. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebManual.Root)
    (options := args)
    (config := {
      sourceLink := some "https://github.com/rokopt/geb-mathlib",
      issueLink := some "https://github.com/rokopt/geb-mathlib/issues"
    })
```

- [ ] **Step 5: Build (module-form check)**

Run: `lake build GebManual` (first run compiles Verso; minutes).
Expected: success. This is the spec's module-form check
(§ Generator executable): at `v4.34.0-rc1`, `#doc` emits a
`public def`, so `module`-form document files are expected to
work. If elaboration of `#doc`, `%doc`, or `{include ...}` fails
with a module-system visibility error: remove the `module` line
(and change `public import` to `import`) from
`manual/GebManual/Root.lean`, then, only if the failure persists,
from the other `manual/` files; re-run, and record the exact
error and the surviving file set for Task 8's rule delta. Any
other error is a genuine defect: diagnose before changing form.

- [ ] **Step 6: Build and run the generator**

Run:

```bash
lake build geb-manual
lake exe geb-manual --output manual/_out
test -f manual/_out/html-multi/index.html && echo OK
```

Expected: `OK`. (No `--` separator before `--output`: Lake's `exe`
forwards trailing arguments verbatim, and `manualMain` rejects a
literal `--`.)

- [ ] **Step 7: Ignore the output directory**

Append to `.gitignore`:

```text
/manual/_out
```

Run: `jj st`
Expected: `manual/_out` absent from the change list.

- [ ] **Step 8: Verify the default targets are untouched**

Run: `lake build && lake test`
Expected: both complete with no new compilation.

- [ ] **Step 9: Commit**

```bash
jj commit -m 'feat(verso): add the GebManual library and generator

lean_lib GebManual and lean_exe geb-manual, sources under manual/
via srcDir, output to manual/_out (gitignored). Outside
defaultTargets and the test driver; nothing default-built changes.'
```

(If Step 5 took the non-`module` fallback, state that and the
error in the commit body.)

---

### Task 3: Lint integration

**Files:**

- Create: `scripts/nolints.json`
- Modify: `lakefile.toml` (only if Step 3 finds further linter
  failures)

**Interfaces:**

- Consumes: `GebManual` (Task 2).
- Produces: `scripts/nolints.json` (the path batteries `runLinter`
  hardcodes), consumed by every later `lake lint -- GebManual`.
  Task 4 extends it if new generated `def`s appear.

- [ ] **Step 1: Run the lint and collect failures**

Run: `lake lint -- GebManual 2>&1 | tee /tmp/manual-lint-1.txt`
Expected: FAIL with `docBlame` on the `def`s Verso elaborates from
`#doc` blocks (one per `#doc` module; the failure lines print the
exact declaration names). No `nonstandard axiom` failures may
appear: their presence means `GebMeta` entered the lint
environment, which contradicts the boundary of the spec's
§ Linting; stop and find which import pulled it in.

- [ ] **Step 2: Write the nolints file**

Create `scripts/nolints.json` containing one `docBlame` pair per
declaration name printed in Step 1, in this shape (the names below
are illustrative; use the printed ones):

```json
[
  ["docBlame", "«Geb»"]
]
```

- [ ] **Step 3: Re-run to clean**

Run: `lake lint -- GebManual`
Expected: PASS. If a linter other than `docBlame` fails on a
document module, disable that one linter for the library in
`lakefile.toml` under `[lean_lib.leanOptions]`
(`weak.linter.<name> = false`), note it for Task 8's rule delta,
and re-run. Keep `weak.warningAsError` untouched: the
accommodation set stays exactly what a clean lint requires.

- [ ] **Step 4: Verify the default lint is untouched**

Run: `lake lint`
Expected: PASS, output shows
`Running linter on specified modules: [Geb]` (the new nolints file
must not change the `Geb` lint's result: its entries name only
manual declarations).

- [ ] **Step 5: Commit**

```bash
jj commit -m 'chore(lint): exempt verso-generated document defs from docBlame

scripts/nolints.json is new (the path batteries runLinter
hardcodes); its entries name only the defs #doc elaborates, which
carry no docstrings. The manual lint runs without the axiom
linter: no manual module imports GebMeta.'
```

---

### Task 4: Initial content

**Files:**

- Create: `manual/GebManual/Bibliography.lean`
- Create: `manual/GebManual/Introduction.lean`
- Create: `manual/GebManual/WTypes.lean`
- Modify: `manual/GebManual/Root.lean` (include the chapters)
- Modify: `scripts/nolints.json` (new `#doc` `def`s)

**Interfaces:**

- Consumes: `GebManual.Root` (Task 2), `scripts/nolints.json`
  (Task 3), library modules `Geb.Mathlib.Data.W.Basic`
  (`WType.elim`, `WType.elim_mk`, `WType.elim_unique`,
  `WType.para`, `WType.para_mk`), `docs/references.bib` entry
  `Meertens1992`.
- Produces: modules `GebManual.Introduction`, `GebManual.WTypes`,
  `GebManual.Bibliography` (bibliography `def Meertens1992`).

Use the copyright header of Task 2 on every new file, and the
`module` form Task 2 settled (adjust `module`/`public import` per
its outcome).

- [ ] **Step 1: Write the bibliography**

Create `manual/GebManual/Bibliography.lean` (field values
transcribed from `docs/references.bib:209-218`; the entry shape is
Verso's `Article`, as in the precedent):

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual

open Verso.Genre.Manual

/-! # Bibliography

The works the manual cites, as Verso bibliography entries.
`docs/references.bib` is the authoritative record; these are
rendering transcriptions keyed identically (the UpperCamelCase
names mirror the bib keys; see `docs/rules/lean-coding.md`).
-/

/-- Meertens, on paramorphisms. -/
def Meertens1992 : Article := {
  title := inlines!"Paramorphisms",
  authors := #[inlines!"L. Meertens"],
  journal := inlines!"Formal Aspects of Computing",
  year := 1992,
  month := none,
  volume := inlines!"4",
  number := inlines!"5",
  pages := some (413, 424),
  url := some "https://doi.org/10.1007/BF01211391"
}
```

- [ ] **Step 2: Write the introduction chapter**

Create `manual/GebManual/Introduction.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual

open Verso.Genre Manual

/-! # Introduction chapter -/

#doc (Manual) "Introduction" =>

Geb is a programming language whose first-class notions include
"programming language" itself. Its specification, interpreter, and
compiler are developed as formal mathematics; this repository
develops that mathematics in Lean 4 against mathlib.

Two disciplines shape the development. The first is constructive:
no `noncomputable` definitions, with `Classical` reasoning
minimised and tracked module by module. The second is
upstream-directed: content is authored to be plausibly
upstreamable, with `Geb/Mathlib/` targeting mathlib4,
`Geb/Cslib/` targeting CSLib, and `Geb/Internal/` holding the
downstream-only remainder.

The chapters that follow present the implemented mathematics one
area at a time, in dependency order, with type-checked references
into the source.
```

- [ ] **Step 3: Write the area chapter**

Create `manual/GebManual/WTypes.lean`:

````lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Mathlib.Data.W.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # W-types chapter -/

#doc (Manual) "W-types and term algebras" =>

A W-type is the type of well-founded trees over a signature: a
type of shapes together with a family assigning each shape its
branching. mathlib's {name}`WType` provides the type and its fold
{name}`WType.elim`, the morphism into an algebra of the polynomial
endofunctor `X ↦ Σ a, β a → X`. The development adds the two laws
mathlib does not state: the computation rule {name}`WType.elim_mk`
and the uniqueness {name}`WType.elim_unique`. Together they make
the W-type the initial algebra of that endofunctor, stated
concretely.

{name}`WType.para` generalises the fold to a paramorphism, whose
step additionally sees each node's children as subtrees paired
with their folded values {citep Meertens1992}[]:

```signature
WType.para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ
```

Its computation rule is {name}`WType.para_mk`: the paramorphism at
a node applies the step to the node's children paired with their
own paramorphisms.
````

- [ ] **Step 4: Include the chapters from the root**

In `manual/GebManual/Root.lean`, add below the existing
`public import VersoManual` line:

```lean
public import GebManual.Introduction
public import GebManual.WTypes
```

and replace the document body (everything after the
`#doc (Manual) "Geb" =>` line) with:

```lean
{include 0 GebManual.Introduction}

{include 0 GebManual.WTypes}
```

- [ ] **Step 5: Build, extend nolints, lint**

Run:

```bash
lake build GebManual
lake lint -- GebManual 2>&1 | tee /tmp/manual-lint-2.txt
```

Expected: the build succeeds (`{name}` roles fail elaboration if
a referenced declaration or the signature block does not match
the source; fix the document, not the source); the lint fails only
with `docBlame` on the two new `#doc` `def`s. Add those names to
`scripts/nolints.json` (keep the array sorted by declaration
name), re-run, expect PASS. `Meertens1992` must NOT need an
entry: it has a docstring.

- [ ] **Step 6: Generate and inspect**

Run:

```bash
lake exe geb-manual --output manual/_out
grep -rl "Paramorphisms" manual/_out/html-multi/ | head -1
```

Expected: the generator succeeds and the bibliography title
appears in the output.

- [ ] **Step 7: Commit**

```bash
jj commit -m 'feat(verso): add the introduction and w-type chapters

Project-overview introduction (Geb as a programming language, the
constructive and upstream-directed disciplines) and an initial
area chapter on the W-type fold and paramorphism, citing
Meertens1992 with the key shared with docs/references.bib.'
```

---

### Task 5: Build-and-serve script

**Files:**

- Create: `scripts/manual.sh`

**Interfaces:**

- Consumes: targets `GebManual`, `geb-manual` (Task 2), the
  `verso-serve` executable (shipped by the `verso` package).
- Produces: `scripts/manual.sh build` (the exact command CI runs in
  Task 6 and the guard greps for in Task 7) and
  `scripts/manual.sh serve`.

- [ ] **Step 1: Write the script**

Create `scripts/manual.sh` (mode 755):

```bash
#!/usr/bin/env bash
#
# scripts/manual.sh
#
# Build or serve the Verso manual (the GebManual library and the
# geb-manual generator). Runs from the repository root regardless
# of the invoking directory: the lint's nolints path
# (scripts/nolints.json) and the generator's --output path are
# both resolved against the working directory.
#
# CI (doc-build.yml) runs the build verb; the manual is otherwise
# outside every default build, test, and lint path.

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

case "${1:-}" in
  build)
    lake build GebManual
    lake lint -- GebManual
    lake exe geb-manual --output manual/_out
    ;;
  serve)
    exec lake exe verso-serve manual/_out/html-multi
    ;;
  *)
    cat >&2 <<'EOF'
usage: scripts/manual.sh {build|serve}

  build  Build the GebManual library, lint it, and generate the
         HTML into manual/_out/html-multi.
  serve  Serve manual/_out/html-multi with verso-serve, which
         prints the URL it binds (port 8000, or a higher free
         port when 8000 is taken).

There is no watch mode: after editing, re-run 'build' and refresh
the browser. Lake rebuilds only the changed modules.
EOF
    exit 2
    ;;
esac
```

- [ ] **Step 2: Verify the usage path**

Run: `bash scripts/manual.sh; echo "rc=$?"`
Expected: the usage text on stderr and `rc=2`.

- [ ] **Step 3: Verify the build verb, from elsewhere**

Run: `(cd /tmp && bash "$OLDPWD/scripts/manual.sh" build)`
(from the repository root, so `$OLDPWD` resolves; or use the
absolute script path). Expected: PASS, proving the
repository-root resolution, since the lint needs
`scripts/nolints.json`.

- [ ] **Step 4: Verify the serve verb**

Run:

```bash
bash scripts/manual.sh serve &
sleep 3
curl -fsS "http://127.0.0.1:8000/" >/dev/null && echo SERVE-OK
kill %1
```

Expected: `SERVE-OK`. If port 8000 was already taken, read the
URL from the serve banner and `curl` that instead; the check is
that the printed URL serves the manual.

- [ ] **Step 5: Commit**

```bash
jj commit -m 'feat(scripts): add manual.sh with build and serve verbs

build runs build-then-lint-then-generate, the order the precedent
CI fix established, identically to CI; serve wraps verso-serve,
which prints the URL it binds. Usage text records the
rebuild-and-refresh reload workflow.'
```

---

### Task 6: CI

**Files:**

- Modify: `.github/workflows/doc-build.yml`

**Interfaces:**

- Consumes: `scripts/manual.sh build` (Task 5).
- Produces: the workflow step line `bash scripts/manual.sh build`
  (Task 7's guard greps for `scripts/manual.sh build`) and the
  `geb-manual` artifact.

- [ ] **Step 1: Extend the paths filter**

In `doc-build.yml`, extend the `pull_request.paths` list with:

```yaml
      - 'manual/**'
      - 'scripts/manual.sh'
      - 'scripts/nolints.json'
```

(`scripts/nolints.json` because the manual lint consumes it: a
nolints change must trigger the workflow that runs that lint.)

- [ ] **Step 2: Append the build and upload steps**

Append to the job's `steps` (after the existing upload step; the
`upload-artifact` SHA is the one already pinned in this file):

```yaml
      - run: bash scripts/manual.sh build
      - name: Upload the generated manual
        uses: actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a  # v7.0.1
        with:
          name: geb-manual
          path: manual/_out/html-multi
          if-no-files-found: error
```

- [ ] **Step 3: Sanity-check the YAML**

Run:

```bash
python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/doc-build.yml'))" && echo YAML-OK
```

Expected: `YAML-OK`.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'ci(verso): build and upload the manual in doc-build

bash scripts/manual.sh build, then artifact geb-manual from
manual/_out/html-multi. The paths filter gains manual/, the
script, and scripts/nolints.json, which the manual lint consumes.
Publication stays out of scope; the artifact is the CI product.'
```

---

### Task 7: Lint-driver guard extension

**Files:**

- Modify: `scripts/tests/test-lint-driver.sh`

**Interfaces:**

- Consumes: `manual/` module tree (Tasks 2, 4), the
  `scripts/manual.sh build` line in `doc-build.yml` (Task 6).
- Produces: the extended guard run by `pre-push.sh` and `ci.yml`.

- [ ] **Step 1: Generalise the coverage scan and add the workflow check**

In `scripts/tests/test-lint-driver.sh`, replace section 2 (from
the `# --- 2. Coverage completeness` comment through the
`orphans` check) with a two-library version, and append a
section 3. Section 1 (the executed `lake lint`) stays `Geb`-only:
executing the manual lint here would compile Verso in `pre-push.sh`
and `ci.yml`, which the lakefile comment forbids. New content:

```bash
# --- 2. Coverage completeness (no module orphaned from the umbrella) -----
# Module name to file path within a library's srcDir; dots map to
# slashes. Geb lives at the package root; GebManual under manual/
# (lakefile.toml srcDir), whose generator root Main is outside the
# GebManual prefix by design and so outside this scan.
mod_to_file() { echo "${2}${1//.//}.lean"; }

check_coverage() {
  local root="$1" prefix="$2"
  local all_mods reachable frontier next m f imps i orphans
  all_mods="$( { echo "$root"; find "${prefix}${root}" -name '*.lean' \
    | sed -E "s,^${prefix},,; s,/,.,g; s,\.lean$,,"; } | sort -u )"
  reachable="$root"
  frontier="$root"
  while [[ -n "$frontier" ]]; do
    next=""
    for m in $frontier; do
      f="$(mod_to_file "$m" "$prefix")"
      [[ -f "$f" ]] || continue
      imps="$(grep -oE "^(public )?import ${root}(\.[A-Za-z0-9_]+)+" "$f" \
        | sed -E 's/^(public )?import //')"
      for i in $imps; do
        if ! grep -qxF "$i" <<<"$reachable"; then
          reachable="$reachable"$'\n'"$i"
          next="$next $i"
        fi
      done
    done
    frontier="$next"
  done
  reachable="$(sort -u <<<"$reachable")"
  orphans="$(comm -23 <(echo "$all_mods") <(echo "$reachable"))"
  if [[ -n "$orphans" ]]; then
    echo "FAIL: $root modules not reachable from the '$root' umbrella (would escape lint):" >&2
    echo "$orphans" | sed 's/^/  /' >&2
    failed=1
  fi
}

check_coverage Geb ""
check_coverage GebManual "manual/"

# --- 3. doc-build.yml retains the manual build step ----------------------
# The manual is linted only by scripts/manual.sh build in
# doc-build.yml; losing that step would silently drop the lint.
if ! grep -qF 'scripts/manual.sh build' .github/workflows/doc-build.yml; then
  echo "FAIL: doc-build.yml lost the 'scripts/manual.sh build' step" >&2
  failed=1
fi
```

Also update the header comment's property list (three properties:
invocation form; coverage completeness for `Geb` and `GebManual`;
the `doc-build.yml` step).

- [ ] **Step 2: Run the guard**

Run: `bash scripts/tests/test-lint-driver.sh`
Expected: `test-lint-driver: ok`.

- [ ] **Step 3: Verify the guard actually guards**

Temporarily delete the `public import GebManual.WTypes` line from
`manual/GebManual/Root.lean`, run the guard, expect a FAIL naming
`GebManual.WTypes` (and `GebManual.Bibliography`); restore the
line (`jj restore manual/GebManual/Root.lean`), re-run, expect
`ok`.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'test(lint): extend the lint-driver guard to the manual

The coverage scan generalises over (root module, srcDir) pairs,
covering GebManual under manual/ with Main outside the scanned
prefix by construction; a third check asserts doc-build.yml
retains the scripts/manual.sh build step. The executed-lint check
stays Geb-only so the guard never compiles Verso.'
```

---

### Task 8: Documentation and rule deltas

**Files:**

- Modify: `README.md` (§ Documentation)
- Modify: `docs/index.md` (§ Directory structure)
- Modify: `docs/rules/ci-and-workflow.md` (new section)
- Modify: `docs/rules/lean-coding.md` (new section)

**Interfaces:**

- Consumes: outcomes of Tasks 2–7 (in particular Task 2's
  module-form result and Task 3's accommodation list).
- Produces: the user-facing build/serve/reload documentation and
  the binding rule deltas.

- [ ] **Step 1: README**

In `README.md` § Documentation, append:

```markdown
- The Geb manual (Verso): `scripts/manual.sh build` builds and
  generates it (`manual/_out/html-multi/`);
  `scripts/manual.sh serve` serves it and prints the URL. There
  is no watch mode: after editing under `manual/`, re-run
  `build` and refresh the browser. Built in CI by `doc-build.yml`,
  not by `lake build`.
```

- [ ] **Step 2: docs/index.md pointer**

In `docs/index.md` § Directory structure, append to the top-level
list:

```markdown
- `manual/` — the Verso manual (build and serve commands:
  `README.md` § Documentation).
```

- [ ] **Step 3: CI rule**

In `docs/rules/ci-and-workflow.md`, add before § Action pinning
policy:

```markdown
## Verso manual build

The manual (`lean_lib GebManual`, `lean_exe geb-manual`, sources
under `manual/`) builds only through `scripts/manual.sh build`:
`lake build GebManual`, `lake lint -- GebManual`,
`lake exe geb-manual --output manual/_out`, in that order: build
precedes lint so a clean checkout lints built oleans. CI runs the
script in `doc-build.yml` and uploads the HTML as the `geb-manual`
artifact. The manual is outside `defaultTargets`, the test driver,
and the pre-push checklist, so no contributor builds Verso
implicitly; `scripts/tests/test-lint-driver.sh` § 3 guards the
workflow step.
```

- [ ] **Step 4: Lean rule deltas**

In `docs/rules/lean-coding.md`, add before § Lean 4 skill
workflows (adjust the third bullet to Task 2's outcome; drop it
if `module` form succeeded, and adjust the fourth to Task 3's
final accommodation list):

```markdown
## Verso manual modules (manual/)

- The manual's modules import the specific `Geb` modules they
  reference, never `GebMeta`, so `lake lint -- GebManual` runs
  without the axiom linter: the constructive discipline governs
  the formalization, and the manual's document objects are
  rendering data whose terms depend on Verso's own axiom usage.
  If a `Geb` module the manual imports ever pulls in `GebMeta`
  transitively, this boundary must be revisited.
- Bibliography entries are top-level `def`s whose names are the
  `docs/references.bib` keys, UpperCamelCase, departing from
  lowerCamelCase term naming: the key identity across the `.bib`,
  the Lean source, and the rendered citations outweighs the
  naming rule. The `.bib` entry is authoritative; the Lean entry
  is a rendering transcription corrected against it.
- [Only if Task 2 fell back:] The document modules do not declare
  `module`: at the pinned Verso, `#doc` fails under the module
  system with [the recorded error].
- The `def`s `#doc` elaborates carry no docstrings and are
  exempted from `docBlame` in `scripts/nolints.json`; the manual
  library's `leanOptions` disable `linter.hashCommand` (`#doc` is
  the document syntax) and widen `verso.code.warnLineLength`
  to 100.
```

- [ ] **Step 5: Markdown checks**

Run:

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
bash scripts/check-md-links.sh
```

Expected: all clean (`doctoc` may rewrite TOCs for the edited
files; include those rewrites in the commit).

- [ ] **Step 6: Commit**

```bash
jj commit -m 'doc(verso): document the manual and record the rule deltas

README and docs/index.md state the build, serve, and reload
workflow; ci-and-workflow.md records the CI-only build through
scripts/manual.sh; lean-coding.md records the axiom-linter
boundary, the bibliography-key naming exemption, and the
generated-def lint accommodations.'
```

---

### Task 9: Full verification

**Files:** none (fixes only if a check fails).

**Interfaces:**

- Consumes: everything above.
- Produces: the verified branch, ready for the spec/plan removal
  commits and user review.

- [ ] **Step 1: The spec's verification list**

Run, in order, expecting every check to pass:

```bash
bash scripts/manual.sh build
bash scripts/manual.sh serve &
sleep 3 && curl -fsS "http://127.0.0.1:8000/" | grep -qi geb && echo SERVE-OK
kill %1
lake lint -- GebManual   # PASS without GebMeta in scope
bash scripts/tests/test-lint-driver.sh
```

Also confirm in a browser (user-visible check, can be deferred to
the user's review): the served manual renders both chapters, the
`{name}` hovers, and the bibliography.

- [ ] **Step 2: Pre-push checklist**

Run: `bash scripts/pre-push.sh`
Expected: PASS apart from the documented informational warning
from `scripts/lake-update-warning.sh` about the manifest change
on a non-`bump/*` branch. Any other failure: fix it in the task
that owns the file, then re-run.

- [ ] **Step 3: Commit message audit**

Run:

```bash
jj log -r 'main..@' --no-graph -T 'description.first_line() ++ "\n"' \
  | bash scripts/check-commit-msg.sh
```

Expected: PASS.

- [ ] **Step 4: Commit (only if fixes were needed)**

```bash
jj commit -m 'fix(verso): <describe the verification fix>'
```

---

### After the tasks

Per `CONTRIBUTING.md` § Concern shape, the branch ends with
commits removing `docs/superpowers/specs/2026-08-14-verso-manual-design.md`,
its `.review-*.md` records, and this plan, after the user's
line-by-line review and before merge. Do not remove them as part
of Task 9; the user drives the branch-finishing step.
