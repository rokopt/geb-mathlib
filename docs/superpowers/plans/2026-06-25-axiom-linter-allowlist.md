# Axiom-linter `Classical.choice` allowlist Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
  - [Task 1: Module-aware decision logic and linter](#task-1-module-aware-decision-logic-and-linter)
  - [Task 2: Allowed-direction fixture, allowlist entry, smoke test](#task-2-allowed-direction-fixture-allowlist-entry-smoke-test)
- [Post-implementation (handled outside this plan)](#post-implementation-handled-outside-this-plan)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend `GebMeta.detectNonstandardAxiom` so a named set of
exact modules may additionally depend on `Classical.choice` (and only
that), while all other modules stay strict.

**Architecture:** Pure decision functions (`permittedAxioms`,
`offendingAxioms`) parameterized by the permitted set, plus a
`moduleOf?` env lookup; the linter resolves each declaration's module
and applies the right permitted set. Allowlist ships containing only a
dedicated test fixture module.

**Tech Stack:** Lean 4 metaprogramming (`Lean.collectAxioms`,
`Environment.getModuleIdxFor?`, Batteries `Linter` / `@[env_linter]`),
`lake`, `jj` (VCS).

## Global Constraints

From `docs/superpowers/specs/2026-06-25-axiom-linter-allowlist-design.md`
and repo rules.

- **`GebMeta` is not self-audited** (it lives outside `Geb`/`GebTests`
  namespaces by design), so its own use of metaprogramming is exempt
  from the axiom linter. The fixture under `GebTests/` *is* audited.
- **Module system:** copyright block, then `module`. `GebMeta.lean`
  uses `public meta section`. A `GebTests` file that defines a public
  declaration needs `@[expose] public section` (a module of only
  private declarations is a build error under `weak.warningAsError`).
- **Style:** 2-space indent, 100-char lines, Unicode, `autoImplicit
  = false`. `snake_case` Prop lemmas; `lowerCamelCase` defs;
  docstrings on every `def`.
- **Permit only `Classical.choice` in allowlisted modules**; every
  other axiom (`sorryAx`, `Lean.ofReduceBool`, …) stays forbidden
  everywhere. Unresolved module → strict (fail-safe).
- **Exact module names** in the allowlist (no prefixes).
- **VCS:** `jj` only (a hook blocks raw mutating `git`). Commits land
  on bookmark `feat/axiom-linter-allowlist`. No push without
  line-by-line user review.
- **Verification gates:** `lake build`, `lake build GebTests`,
  `lake lint`, `lake lint -- GebTests`, `bash
  scripts/tests/test-axiom-linter.sh`, `bash scripts/lint-imports.sh`,
  `markdownlint-cli2` on touched Markdown.

The module-resolution API and the full linter were prototype-compiled
against the pin (toolchain `v4.32.0-rc1`) during spec review; the
forms below are the verified ones.

---

### Task 1: Module-aware decision logic and linter

**Files:**

- Modify: `GebMeta.lean` (decision functions + linter)
- Modify: `GebTests/Internal/AxiomLinter.lean` (update existing tests;
  add allowlist-logic unit tests and the module-resolution meta-test)

**Interfaces:**

- Produces:
  - `GebMeta.standardAxioms : NameSet` (unchanged: `{propext,
    Quot.sound}`).
  - `GebMeta.classicalAllowedModules : NameSet` (ships empty here;
    Task 2 adds the fixture module).
  - `GebMeta.permittedAxioms (allowed : NameSet) (mod : Name) :
    NameSet` — `standardAxioms`, plus `Classical.choice` iff
    `allowed.contains mod`.
  - `GebMeta.offendingAxioms (permitted : NameSet) (used : Array Name)
    : Array Name` — `used.filter (∉ permitted)` (gains the leading
    `permitted` parameter).
  - `GebMeta.moduleOf? (env : Environment) (declName : Name) : Option
    Name`.

Note on testability: `permittedAxioms` takes the allowlist as an
explicit parameter (the spec sketched it closing over the global).
This refines the spec's stated "pure functions taking the permitted
set explicitly" philosophy and lets the unit tests exercise the
allowlist logic without mutating the global `classicalAllowedModules`.
The linter passes `classicalAllowedModules`.

- [ ] **Step 1: Write the failing tests**

In `GebTests/Internal/AxiomLinter.lean`, first fix the header for the
new tests: the `NameSet` literals need `Lean` open, `run_cmd` needs
`Lean.Elab.Command` (as a `meta` import, since `run_cmd` emits a
`meta` definition), and the `run_cmd`'s `throwError` pulls
`Lean.Exception` (which `lake shake` requires be a plain
`public import`). Set the top of the file to:

```lean
module -- shake: keep-all
public meta import Lean.Elab.Command
public import Lean.Exception
import GebMeta
```

and change the `open` line to `open Lean GebMeta`.

Then update the three existing `#guard`s to the new two-argument
`offendingAxioms`, and append the allowlist-logic tests and the
module-resolution meta-test:

```lean
-- The standard axioms are accepted (none offending).
#guard offendingAxioms standardAxioms #[``propext, ``Quot.sound] == #[]

-- A non-standard axiom is reported.
#guard offendingAxioms standardAxioms #[``propext, ``Classical.choice, ``Quot.sound]
  == #[``Classical.choice]

-- `sorryAx` is reported.
#guard offendingAxioms standardAxioms #[``sorryAx] == #[``sorryAx]

-- `permittedAxioms`: a non-allowlisted module gets the strict set.
#guard !((permittedAxioms ({} : NameSet) `Some.Module).contains ``Classical.choice)

-- `permittedAxioms`: an allowlisted module additionally permits
-- `Classical.choice`, and nothing else.
#guard (permittedAxioms (({} : NameSet).insert `Some.Module) `Some.Module).contains
  ``Classical.choice
#guard !((permittedAxioms (({} : NameSet).insert `Some.Module) `Some.Module).contains
  ``sorryAx)

-- Under the permissive set: `Classical.choice` is allowed, but
-- `sorryAx` remains offending (the "did not widen too far" assertion).
#guard offendingAxioms (standardAxioms.insert ``Classical.choice) #[``Classical.choice]
  == #[]
#guard offendingAxioms (standardAxioms.insert ``Classical.choice) #[``sorryAx]
  == #[``sorryAx]
#guard offendingAxioms (standardAxioms.insert ``Classical.choice)
  #[``Classical.choice, ``sorryAx] == #[``sorryAx]

-- Module resolution returns a module for an imported declaration.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (GebMeta.moduleOf? env ``propext).isSome do
    throwError "moduleOf? failed to resolve the imported declaration `propext`"
```

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Internal.AxiomLinter`
Expected: FAIL — `unknown identifier 'permittedAxioms'` /
`offendingAxioms` arity mismatch.

- [ ] **Step 3: Implement the GebMeta changes**

Replace the body of `GebMeta.lean`'s `namespace GebMeta` (the
`standardAxioms`/`offendingAxioms`/`detectNonstandardAxiom` block)
with:

```lean
/-- Axioms a constructive development permits: `propext` and
`Quot.sound`. -/
def standardAxioms : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Quot.sound

/-- Exact module names additionally permitted to depend on
`Classical.choice` (and only `Classical.choice`). Empty here; the
test fixture and feature wrappers add their own module names. -/
def classicalAllowedModules : NameSet := {}

/-- Permitted axioms for a declaration in module `mod`, given the
allowlist `allowed`: the standard set, plus `Classical.choice` exactly
when `mod` is allowlisted. -/
def permittedAxioms (allowed : NameSet) (mod : Name) : NameSet :=
  if allowed.contains mod then standardAxioms.insert ``Classical.choice
  else standardAxioms

/-- The elements of `used` not in the `permitted` set. -/
def offendingAxioms (permitted : NameSet) (used : Array Name) : Array Name :=
  used.filter (fun a => !permitted.contains a)

/-- The defining module of `declName`, if resolvable. Returns `none`
for a declaration in the current (not-yet-imported) module. -/
def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Flags a declaration depending on an axiom outside its permitted
set. A declaration in a module listed in `classicalAllowedModules`
additionally permits `Classical.choice` (and only that); every other
axiom (`sorryAx`, `Lean.ofReduceBool`, …) is forbidden everywhere. A
declaration whose module is unresolvable is held to the strict set. -/
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let mod := (moduleOf? (← getEnv) declName).getD .anonymous
    let permitted := permittedAxioms classicalAllowedModules mod
    let bad := offendingAxioms permitted (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true
```

- [ ] **Step 4: Run to verify it passes**

Run: `lake build GebTests.Internal.AxiomLinter`
Expected: PASS (all `#guard`s and the `run_cmd` meta-test succeed).

- [ ] **Step 5: Confirm the linter still builds and lints the package**

Run: `lake build && lake lint`
Expected: build succeeds; `lake lint` over `Geb` reports no offending
axioms (nothing in `Geb` uses `Classical.choice`).

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(linter): scope detectNonstandardAxiom Classical.choice by module"
```

---

### Task 2: Allowed-direction fixture, allowlist entry, smoke test

**Files:**

- Create: `GebTests/Internal/AxiomLinterClassicalFixture.lean`
- Modify: `GebTests/Internal.lean` (import the fixture)
- Modify: `GebMeta.lean` (add the fixture module to
  `classicalAllowedModules`)
- Modify: `scripts/tests/test-axiom-linter.sh` (add a non-allowlisted
  `Classical.choice` rejection case)

**Interfaces:**

- Consumes: the Task 1 linter and `classicalAllowedModules`.
- Produces: `GebTests.Internal.AxiomLinterClassicalFixture.usesClassicalChoice`,
  a `Classical.choice`-dependent declaration in an allowlisted module.

- [ ] **Step 1: Create the fixture (not yet allowlisted)**

Create `GebTests/Internal/AxiomLinterClassicalFixture.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

@[expose] public section

/-!
# Axiom-linter fixture: a deliberate `Classical.choice` dependency

This module exists to exercise `GebMeta.detectNonstandardAxiom`'s
module-scoped `Classical.choice` allowlist. Its module name is listed
in `GebMeta.classicalAllowedModules`, so the linter accepts the
declaration below despite its `Classical.choice` dependency.
-/

/-- A declaration depending on `Classical.choice` (through
`Classical.em`), used only to test the allowlist. -/
theorem usesClassicalChoice : True :=
  (Classical.em True).elim (fun _ => trivial) (fun _ => trivial)
```

Add the import to `GebTests/Internal.lean` (after the existing
`import GebTests.Internal.AxiomLinter`, before the docstring):

```lean
import GebTests.Internal.AxiomLinter
import GebTests.Internal.AxiomLinterClassicalFixture
```

- [ ] **Step 2: Verify the fixture is rejected while NOT allowlisted**

Run: `lake build GebTests && lake lint -- GebTests`
Expected: FAIL — `usesClassicalChoice depends on non-standard
axiom(s): [Classical.choice]` (the module is not yet allowlisted, so
the strict set applies). This confirms the default-strict behavior.

- [ ] **Step 3: Add the fixture module to the allowlist**

In `GebMeta.lean`, change `classicalAllowedModules`:

```lean
def classicalAllowedModules : NameSet :=
  ({} : NameSet).insert `GebTests.Internal.AxiomLinterClassicalFixture
```

- [ ] **Step 4: Verify the fixture is now accepted**

Run: `lake build GebTests && lake lint -- GebTests`
Expected: PASS — the `Classical.choice` dependency is permitted for
the allowlisted fixture module; no other axiom is permitted. This is
the end-to-end allowed-path proof.

- [ ] **Step 5: Extend the smoke test with a rejection case**

In `scripts/tests/test-axiom-linter.sh`, after the existing
`out_good` check (and before the final `failed` summary), add a
`Choice.lean` fixture (a non-allowlisted module using
`Classical.choice`) and assert rejection naming `Classical.choice`:

```bash
cat > "$tmp/Choice.lean" <<'EOF'
import GebMeta
import Batteries.Tactic.Lint
theorem usesChoice : True := (Classical.em True).elim (fun _ => trivial) (fun _ => trivial)
#lint only detectNonstandardAxiom
EOF

out_choice="$(lake env lean "$tmp/Choice.lean" 2>&1)"
rc_choice=$?
if [[ "$rc_choice" -eq 0 ]]; then
  echo "FAIL: linter accepted Classical.choice in a non-allowlisted module" >&2
  echo "  output: $out_choice" >&2
  failed=1
fi
if ! grep -qF 'Classical.choice' <<<"$out_choice"; then
  echo "FAIL: violation output did not name 'Classical.choice'" >&2
  echo "  output: $out_choice" >&2
  failed=1
fi
```

(The temp module is not in the package, so its declaration's module is
unresolvable and the fail-safe strict set applies — which is exactly
why `Classical.choice` must be rejected here.)

- [ ] **Step 6: Run the smoke test**

Run: `bash scripts/tests/test-axiom-linter.sh`
Expected: `test-axiom-linter: ok` (the original `badAx`/clean cases
plus the new `Classical.choice` rejection case all behave).

- [ ] **Step 7: Full verification gate**

Run each and confirm before proceeding:

- `lake build` — Expected: succeeds.
- `lake build GebTests` — Expected: succeeds.
- `lake test` — Expected: `GebTests` builds; all `#guard`/`run_cmd`
  checks pass.
- `lake lint` — Expected: no offending axioms in `Geb`.
- `lake lint -- GebTests` — Expected: no offending axioms (the
  fixture's `Classical.choice` is permitted; nothing else is).
- `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
  — Expected: exit 0 (the test file's `Lean.Elab.Command`/
  `Lean.Exception` imports are present, so shake suggests no additions).
- `bash scripts/tests/test-axiom-linter.sh` — Expected:
  `test-axiom-linter: ok`.
- `bash scripts/lint-imports.sh` — Expected: no violations.

- [ ] **Step 8: Commit**

```bash
jj commit -m "test(linter): add allowlisted Classical.choice fixture and smoke case"
```

- [ ] **Step 9: Advance the bookmark**

```bash
jj bookmark set feat/axiom-linter-allowlist -r @-
```

---

## Post-implementation (handled outside this plan)

- Pre-commit Lean review (`lean4:review`) on `GebMeta.lean` and the
  fixture; then line-by-line user review. No push without review.
- Per `CONTRIBUTING.md` § Concern shape, the spec and plan are removed
  in the branch's final commits before merge to `main`.
- After this lands on `main`: rebase `feat/slice-pfunctor` onto the
  updated `main` and amend its spec/plan to the two-file
  constructive-core + categorical-wrapper architecture, adding the
  wrapper module to `classicalAllowedModules`.
