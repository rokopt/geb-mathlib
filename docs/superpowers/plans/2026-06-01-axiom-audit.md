# In-Lean axiom audit (`@[env_linter]`) Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File Structure](#file-structure)
- [Task 1: Create the `GebMeta` linter library](#task-1-create-the-gebmeta-linter-library)
- [Task 2: Register the linter in `Geb` and `GebTests`](#task-2-register-the-linter-in-geb-and-gebtests)
- [Task 3: Negative + positive smoke test](#task-3-negative--positive-smoke-test)
- [Task 4: Unit tests for the pure classifier](#task-4-unit-tests-for-the-pure-classifier)
- [Task 5: Wire the audit into CI](#task-5-wire-the-audit-into-ci)
- [Task 6: Wire the audit into `scripts/pre-push.sh`](#task-6-wire-the-audit-into-scriptspre-pushsh)
- [Task 7: Delete the vendored bash script](#task-7-delete-the-vendored-bash-script)
- [Task 8: Update the rule docs](#task-8-update-the-rule-docs)
- [Task 9: Final verification](#task-9-final-verification)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the vendored bash axiom checker
(`scripts/check-axioms.sh`) with a batteries `@[env_linter]` built
on `Lean.collectAxioms` that fails `lake lint` when any `Geb` or
`GebTests` declaration depends on an axiom outside
`{propext, Quot.sound}`.

**Architecture:** A small tooling library `GebMeta` defines a pure
classifier (`offendingAxioms`) and an `@[env_linter]`
(`detectNonstandardAxiom`). `Geb.lean` and `GebTests.lean` import
`GebMeta` so the linter is registered when `runLinter` (driven by
`lake lint`) loads either library; `runLinter` lints only the
target library's own declarations and exits non-zero on findings. A
committed smoke test stages a throwaway bad-axiom fixture in a
tempdir to prove the linter fails when it should.

**Tech Stack:** Lean 4 (toolchain `v4.31.0-rc1`), Lake, batteries
`Batteries.Tactic.Lint` (`@[env_linter]` / `runLinter`),
`Lean.collectAxioms`, bash, GitHub Actions, `jj`.

**VCS note:** This repository uses `jj` (colocated). A PreToolUse
hook blocks raw mutating `git`. Use `jj` for commits: stage nothing
manually; `jj` auto-tracks the working copy. The commit steps below
use `jj commit -m "<msg>"` (which describes the current change and
starts a new one). Do **not** push; the user reviews before any
push. End each commit message with the
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
trailer.

**Reference spec:**
`docs/superpowers/specs/2026-06-01-axiom-audit-design.md`.

---

## File Structure

- Create `GebMeta.lean` — module `GebMeta`: pure classifier
  (`standardAxioms`, `offendingAxioms`) and the `@[env_linter]`
  `detectNonstandardAxiom`. Outside the `Geb`/`GebTests` namespaces
  so it is not itself audited.
- Modify `lakefile.toml` — add `[[lean_lib]] name = "GebMeta"`.
- Modify `Geb.lean` — `import GebMeta` (registers the linter when
  `Geb` is linted). The file is `shake: keep-all`, so the import is
  not stripped.
- Modify `GebTests.lean` — `import GebMeta` (registers the linter
  when `GebTests` is linted). Also `shake: keep-all`.
- Create `GebTests/Internal/AxiomLinter.lean` — module
  `GebTests.Internal.AxiomLinter`: `#guard` unit tests for
  `offendingAxioms`.
- Modify `GebTests/Internal.lean` — index the new test module.
- Create `scripts/tests/test-axiom-linter.sh` — negative + positive
  smoke test (tempdir-staged fixture).
- Modify `.github/workflows/ci.yml` — remove the `axiom_check` job;
  add `GebTests` lint coverage and the smoke test to the `build`
  job.
- Modify `scripts/pre-push.sh` — add `GebTests` lint coverage;
  replace the `check-axioms.sh` step with the smoke test.
- Delete `scripts/check-axioms.sh`.
- Modify `docs/rules/lean-coding.md` and
  `docs/rules/ci-and-workflow.md` — describe the linter instead of
  the bash script.

**Lean-mechanics note for the implementer:** the module system
(`module`, `public`, `meta`) and the `@[env_linter]` requirement
(declaration must be `public` and `meta`) are exercised here. Each
implementation task ends by building and observing; where the exact
modifier or import form is uncertain, the step states the likely
error and the adjustment. Use the `lean4` skill / Lean LSP to read
compiler errors precisely.

---

## Task 1: Create the `GebMeta` linter library

**Files:**

- Create: `GebMeta.lean`
- Modify: `lakefile.toml` (add a `[[lean_lib]]` block)

- [ ] **Step 1: Add the library to `lakefile.toml`**

Append this block after the existing `[[lean_lib]]` blocks (after
the `GebTests` one):

```toml
[[lean_lib]]
name = "GebMeta"
```

- [ ] **Step 2: Write `GebMeta.lean`**

Create `GebMeta.lean` with exactly this content:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public meta import Lean.Util.CollectAxioms
public meta import Batteries.Tactic.Lint.Basic

/-!
# Axiom-hygiene linter

`detectNonstandardAxiom` is an `@[env_linter]` that fails
`lake lint` when a declaration depends on any axiom outside the
constructive standard set `{propext, Quot.sound}`. It is built on
`Lean.collectAxioms` (core Lean), the same primitive `#print
axioms` uses. The module lives outside the `Geb`/`GebTests`
namespaces so the linter does not audit its own metaprogramming
code.

## References

- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Batteries/Tactic/Lint/Basic.lean` — the `Linter` interface and
  the `@[env_linter]` attribute.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebMeta

/-- Axioms a constructive development permits: `propext` and
`Quot.sound`. -/
def standardAxioms : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Quot.sound

/-- The elements of `used` that are not standard axioms. -/
def offendingAxioms (used : Array Name) : Array Name :=
  used.filter (fun a => !standardAxioms.contains a)

/-- Flags a declaration depending on a non-standard axiom
(anything outside `{propext, Quot.sound}`, e.g. `Classical.choice`,
`sorryAx`, `Lean.ofReduceBool`). -/
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let bad := offendingAxioms (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on propext and Quot.sound."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

end GebMeta
```

- [ ] **Step 3: Build the library and observe**

Run: `lake build GebMeta`
Expected: builds with no errors.

If the build fails:

- "unknown identifier 'collectAxioms'": change the call to
  `Lean.collectAxioms` (it is `Lean.collectAxioms`; `open Lean`
  should suffice — confirm the `open` line is present).
- "unknown identifier 'Linter'" / "unknown attribute 'env_linter'":
  confirm `public meta import Batteries.Tactic.Lint.Basic` and
  `open ... Batteries.Tactic.Lint` are present; mathlib's batteries
  pin provides them.
- An error that the `@[env_linter]` target must be `public`/`meta`:
  confirm the declaration is inside the `public meta section`. If
  `NameSet`/`m!`/`MessageData` are unknown, they come from `Lean`
  (the batteries import re-exports them via `open Lean`).
- If `({} : NameSet)` is rejected, use `(∅ : NameSet)` or
  `NameSet.empty`.

- [ ] **Step 4: Commit**

```bash
jj commit -m "feat(meta): add axiom-hygiene env_linter GebMeta

detectNonstandardAxiom flags any Geb/GebTests declaration depending
on an axiom outside {propext, Quot.sound}, via Lean.collectAxioms.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Register the linter in `Geb` and `GebTests`

The linter only runs under `runLinter` if its module is in the
import closure of the library being linted. `Geb.lean` and
`GebTests.lean` are `shake: keep-all`, so an added import is not
stripped by `lake shake`.

**Files:**

- Modify: `Geb.lean`
- Modify: `GebTests.lean`

- [ ] **Step 1: Import `GebMeta` from `Geb.lean`**

In `Geb.lean`, add `import GebMeta` immediately after the existing
`public import Geb.Internal` line (a plain, non-`public` import — it
is needed only to register the linter, not to re-export it):

```lean
public import Geb.Mathlib
public import Geb.Cslib
public import Geb.Internal
import GebMeta
```

- [ ] **Step 2: Import `GebMeta` from `GebTests.lean`**

In `GebTests.lean`, add `import GebMeta` after the existing
`public import GebTests.Internal` line:

```lean
public import GebTests.Mathlib
public import GebTests.Cslib
public import GebTests.Internal
import GebMeta
```

- [ ] **Step 3: Build both libraries**

Run: `lake build Geb GebTests`
Expected: builds with no errors.

If a build error reports that a non-`public` import is not allowed
in a `module` with `public import`s, change `import GebMeta` to
`public import GebMeta` in the failing file and rebuild.

- [ ] **Step 4: Confirm `lake lint` passes on the (clean) repo**

Run: `lake lint`
Expected: exits 0; output ends with "All linting checks passed!"
(no `detectNonstandardAxiom` errors — there are no `Geb`
declarations yet).

Run: `lake lint -- GebTests`
Expected: exits 0; "All linting checks passed!".

If `lake lint -- GebTests` is rejected by lake's argument parser,
try `lake lint GebTests`; record which form works (the smoke test
and CI/pre-push wiring below use the same form).

- [ ] **Step 5: Confirm `lake shake` does not strip the import**

Run: `lake build GebTests`
Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: exits 0, no suggestion to remove `import GebMeta` (the
`shake: keep-all` annotation on the roots prevents it). If shake
flags the import, confirm the root files still carry
`module -- shake: keep-all` on their `module` line.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(meta): register axiom linter in Geb and GebTests

Geb.lean and GebTests.lean import GebMeta so detectNonstandardAxiom
is active when runLinter lints either library.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: Negative + positive smoke test

This is the behavioral proof that the linter fails when it should.
It mirrors `scripts/tests/test-lint-imports.sh`: stage fixtures in a
tempdir, run the linter, assert outcomes. Nothing axiom-violating is
committed.

**Files:**

- Create: `scripts/tests/test-axiom-linter.sh`

- [ ] **Step 1: Write the test script**

Create `scripts/tests/test-axiom-linter.sh` with this content
(`chmod +x` it after writing):

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-axiom-linter.sh
#
# Smoke test for the GebMeta.detectNonstandardAxiom env_linter.
# Stages throwaway fixtures in a temp directory: a violating one
# (a theorem proved via a custom axiom) that the linter must reject,
# and a clean one that it must accept. Nothing axiom-violating is
# committed to the repository.
#
# Exit 0 if both scenarios behave; non-zero otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
failed=0

cat > "$tmp/Bad.lean" <<'EOF'
module
import GebMeta
axiom badAx : (1 : Nat) = 2
theorem usesBad : (1 : Nat) = 2 := badAx
#lint only GebMeta.detectNonstandardAxiom
EOF

cat > "$tmp/Good.lean" <<'EOF'
module
import GebMeta
theorem fine : True := True.intro
#lint only GebMeta.detectNonstandardAxiom
EOF

out_bad="$(lake env lean "$tmp/Bad.lean" 2>&1)"
rc_bad=$?
if [[ "$rc_bad" -eq 0 ]]; then
  echo "FAIL: linter accepted a declaration using a non-standard axiom" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi
if ! grep -qF 'badAx' <<<"$out_bad"; then
  echo "FAIL: violation output did not name the offending axiom 'badAx'" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi

out_good="$(lake env lean "$tmp/Good.lean" 2>&1)"
rc_good=$?
if [[ "$rc_good" -ne 0 ]]; then
  echo "FAIL: linter rejected clean code" >&2
  echo "  output: $out_good" >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-axiom-linter: FAIL" >&2
  exit 1
fi
echo "test-axiom-linter: ok"
exit 0
```

- [ ] **Step 2: Make it executable**

Run: `chmod +x scripts/tests/test-axiom-linter.sh`

- [ ] **Step 3: Run it and observe**

Run: `bash scripts/tests/test-axiom-linter.sh`
Expected: prints `test-axiom-linter: ok`, exits 0.

If it fails, diagnose against the printed fixture output:

- If `Bad.lean` exits 0 (linter did not fire): confirm the linter
  name in `#lint only GebMeta.detectNonstandardAxiom` matches the
  registered declaration name, and that `import GebMeta` resolves
  under `lake env lean` (run `lake env lean "$tmp/Bad.lean"`
  manually to read the error).
- If `lake env lean` rejects the `module` header on the fixture,
  remove the `module` line from both fixtures and re-run (the linter
  registration comes from `import GebMeta`, not from the fixture
  being a module).
- If `#lint only` reports "not a linter": use the exact registered
  name shown by `#lint` with no `only` (run a fixture containing
  just `import GebMeta` and `#lint`), then correct the name.
- If the clean fixture (`Good.lean`) fails: inspect its output;
  `True.intro` depends on no axioms, so any failure indicates a
  classifier bug in `offendingAxioms`.

- [ ] **Step 4: Commit**

```bash
jj commit -m "test(meta): smoke-test the axiom linter on staged fixtures

scripts/tests/test-axiom-linter.sh stages a bad-axiom fixture and a
clean fixture in a tempdir and asserts the linter rejects the former
and accepts the latter. No axiom-violating code is committed.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: Unit tests for the pure classifier

**Files:**

- Create: `GebTests/Internal/AxiomLinter.lean`
- Modify: `GebTests/Internal.lean`

- [ ] **Step 1: Write the `#guard` unit tests**

Create `GebTests/Internal/AxiomLinter.lean` with this content:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import GebMeta

/-!
# Unit tests for `GebMeta.offendingAxioms`

Example-based checks of the pure axiom classifier behind the
`detectNonstandardAxiom` linter.
-/

open GebMeta

-- The standard axioms are accepted (none offending).
#guard offendingAxioms #[``propext, ``Quot.sound] == #[]

-- A non-standard axiom is reported.
#guard offendingAxioms #[``propext, ``Classical.choice, ``Quot.sound]
  == #[``Classical.choice]

-- `sorryAx` is reported.
#guard offendingAxioms #[``sorryAx] == #[``sorryAx]
```

- [ ] **Step 2: Index the test module**

In `GebTests/Internal.lean`, (a) add the `shake: keep-all`
annotation to the `module` line and (b) add the import. The result:

```lean
module -- shake: keep-all

import GebTests.Internal.AxiomLinter

/-!
# GebTests.Internal — tests for downstream-only content
-/
```

(Keep the existing copyright header above the `module` line
unchanged.)

- [ ] **Step 3: Build the tests and observe the `#guard`s**

Run: `lake build GebTests`
Expected: builds with no errors. A failing `#guard` would error at
build time naming the line.

If `#guard` reports it cannot evaluate `offendingAxioms` because it
is `meta`: move `standardAxioms` and `offendingAxioms` out of the
`public meta section` in `GebMeta.lean` into plain `public def`s
(they are pure data functions needing only `Lean` names), leaving
only `detectNonstandardAxiom` in the `public meta section`; add
`public import Lean.Data.NameSet` to `GebMeta.lean` for `NameSet`,
then rebuild `GebMeta` and `GebTests`.

If `==` on `Array Name` is rejected, compare via
`.toList == [...]` or `decide`.

- [ ] **Step 4: Run the test driver**

Run: `lake test`
Expected: exits 0 (the test library, `GebTests`, builds; `#guard`s
pass).

- [ ] **Step 5: Commit**

```bash
jj commit -m "test(meta): unit-test offendingAxioms with #guard

GebTests/Internal/AxiomLinter.lean checks the pure classifier on
standard, Classical.choice, and sorryAx inputs.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 5: Wire the audit into CI

**Files:**

- Modify: `.github/workflows/ci.yml`

- [ ] **Step 1: Add `GebTests` lint and the smoke test to the
  `build` job**

In `.github/workflows/ci.yml`, the `build` job already runs
`leanprover/lean-action` (with `lint: true`, which lints `Geb`),
then `lake build GebTests`, then `lake shake`, then
`test-lake-shake.sh`. After the `lake build GebTests` step and
before the `lake shake` step, insert:

```yaml
      - name: lake lint GebTests (axiom + style linters on tests)
        run: lake lint -- GebTests
      - name: scripts/tests/test-axiom-linter.sh
        run: bash scripts/tests/test-axiom-linter.sh
```

Use whichever `lake lint` argument form Task 2 Step 4 confirmed
(`lake lint -- GebTests` or `lake lint GebTests`).

- [ ] **Step 2: Remove the `axiom_check` job**

Delete the entire `axiom_check:` job (the `- name:
scripts/check-axioms.sh` step, its `run:` line, the job's
`leanprover/lean-action` step, `runs-on`, `name`, and the
`axiom_check:` key). Its function — auditing axioms — is now covered
by the `build` job's lint steps.

- [ ] **Step 3: Validate the workflow file**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/ci.yml'))"`
Expected: no output, exit 0 (valid YAML).

If `actionlint` is available, run `actionlint .github/workflows/ci.yml`
and expect no errors.

- [ ] **Step 4: Commit**

```bash
jj commit -m "ci: run the axiom linter via lake lint; drop axiom_check job

The build job lints Geb (via lean-action) and GebTests (explicit
step), running detectNonstandardAxiom, plus the linter smoke test.
The separate check-axioms job is removed.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 6: Wire the audit into `scripts/pre-push.sh`

**Files:**

- Modify: `scripts/pre-push.sh`

- [ ] **Step 1: Add a `GebTests` lint step after `lake build
  GebTests`**

In `scripts/pre-push.sh`, immediately after the existing

```bash
step "lake build GebTests (prerequisite for lake shake)"
lake build GebTests
```

insert:

```bash
step "lake lint GebTests (axiom + style linters on tests)"
lake lint -- GebTests
```

(Use the argument form confirmed in Task 2 Step 4.)

- [ ] **Step 2: Replace the `check-axioms.sh` step with the smoke
  test**

Replace these two lines:

```bash
step "scripts/check-axioms.sh"
bash scripts/check-axioms.sh Geb/ GebTests/
```

with:

```bash
step "scripts/tests/test-axiom-linter.sh"
bash scripts/tests/test-axiom-linter.sh
```

- [ ] **Step 3: Run the full pre-push checklist**

Run: `bash scripts/pre-push.sh`
Expected: every step passes; the script reaches its end without a
non-zero exit. (This builds, tests, lints both libraries, runs the
smoke test, and runs markdownlint.)

If `markdownlint-cli2 '**/*.md'` fails on `.remember/` files
unrelated to this change, that is pre-existing; fix only if the
checklist treats it as blocking — otherwise note it and continue.

- [ ] **Step 4: Commit**

```bash
jj commit -m "ci: run axiom linter in pre-push; drop check-axioms step

pre-push.sh lints GebTests (in addition to lean-action's Geb lint)
and runs the linter smoke test in place of scripts/check-axioms.sh.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 7: Delete the vendored bash script

**Files:**

- Delete: `scripts/check-axioms.sh`

- [ ] **Step 1: Confirm no remaining live references**

Run:
`grep -rn 'check-axioms' . --include='*.sh' --include='*.yml' | grep -v '\.git/'`
Expected: no matches in `scripts/` or `.github/` (only historical
`docs/superpowers/` references may remain; those are point-in-time
records and stay).

If a live reference remains in `scripts/` or `.github/`, it was
missed in Tasks 5–6; fix it before deleting.

- [ ] **Step 2: Delete the script**

Run: `rm scripts/check-axioms.sh`

- [ ] **Step 3: Commit**

```bash
jj commit -m "chore: remove vendored scripts/check-axioms.sh

Superseded by the GebMeta.detectNonstandardAxiom env_linter.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 8: Update the rule docs

**Files:**

- Modify: `docs/rules/lean-coding.md`
- Modify: `docs/rules/ci-and-workflow.md`

- [ ] **Step 1: Update `docs/rules/lean-coding.md` §
  Constructive-only**

Replace this bullet:

```markdown
- `scripts/check-axioms.sh` (vendored from `lean4-skills` with
  `Classical.choice` excluded from the allowlist) is part of the
  pre-commit / pre-push checklist and runs in CI.
```

with:

```markdown
- The `GebMeta.detectNonstandardAxiom` `@[env_linter]` fails
  `lake lint` when any `Geb` or `GebTests` declaration depends on
  an axiom outside `{propext, Quot.sound}` (`Classical.choice`
  excluded, per this discipline). It runs in CI and the pre-push
  checklist; `scripts/tests/test-axiom-linter.sh` smoke-tests it.
```

- [ ] **Step 2: Update `docs/rules/ci-and-workflow.md` § Pre-push
  checklist item 10**

Replace item 10:

```markdown
10. `bash scripts/check-axioms.sh Geb/ GebTests/` quiet. The
    script requires `lake build` to have populated `.lake/build/`
    (item 1 above guarantees this in the checklist order); run
    manually in a fresh worktree, it reports 0 declarations and
    exits 3 — which is a missing-build artefact, not a real
    failure.
```

with:

```markdown
10. The axiom env_linter (`GebMeta.detectNonstandardAxiom`) runs
    under `lake lint`: `Geb` is covered by item 3's `lake lint`,
    and `GebTests` by an added `lake lint -- GebTests` step (after
    `lake build GebTests`). It fails when any declaration depends
    on an axiom outside `{propext, Quot.sound}`.
    `scripts/tests/test-axiom-linter.sh` smoke-tests the linter.
```

- [ ] **Step 3: Regenerate any affected TOCs and lint the docs**

Run: `doctoc --update-only docs/rules/lean-coding.md docs/rules/ci-and-workflow.md`
(Heading text was not changed, so TOCs should be unaffected; this
confirms it.)

Run: `markdownlint-cli2 'docs/rules/lean-coding.md' 'docs/rules/ci-and-workflow.md'`
Expected: no errors for these two files.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc: describe the axiom env_linter in the rule docs

Replace the scripts/check-axioms.sh references in lean-coding.md and
ci-and-workflow.md with the GebMeta.detectNonstandardAxiom linter.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 9: Final verification

**Files:** none (verification only).

- [ ] **Step 1: Clean build + lint of both libraries**

Run: `lake build Geb GebTests GebMeta`
Expected: exits 0.

Run: `lake lint`
Expected: exits 0, "All linting checks passed!".

Run: `lake lint -- GebTests`
Expected: exits 0.

- [ ] **Step 2: Linter behavioral test**

Run: `bash scripts/tests/test-axiom-linter.sh`
Expected: `test-axiom-linter: ok`, exit 0.

- [ ] **Step 3: Full pre-push checklist**

Run: `bash scripts/pre-push.sh`
Expected: completes without a non-zero exit (build, test, both
lints, smoke test, shake, import lint, markdownlint).

- [ ] **Step 4: Confirm the bash script is gone and nothing live
  references it**

Run: `test ! -e scripts/check-axioms.sh && echo "removed"`
Expected: `removed`.

Run:
`grep -rn 'check-axioms' scripts .github docs/rules | grep -v '\.git/'`
Expected: no matches.

- [ ] **Step 5: Stop for line-by-line review**

Do not push. Present the branch (`feat/axiom-audit`) diff for the
user's line-by-line review per `CONTRIBUTING.md` § Working.
