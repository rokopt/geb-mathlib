# Allow test-sibling imports in `lint-imports.sh`: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Scope](#scope)
- [Background](#background)
- [Design](#design)
  - [Allowed imports and leakage, per root](#allowed-imports-and-leakage-per-root)
  - [Implementation](#implementation)
- [Documentation](#documentation)
- [Testing](#testing)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Status

Design for review. Spec and plan are transient artifacts removed in
the topic branch's final commits, per `CONTRIBUTING.md` § Concern
shape. This concern lands on its own branch off `main`
(`fix/lint-imports-test-siblings`); the slice-polynomial-functor
branch rebases onto the updated `main` afterward.

## Scope

`scripts/lint-imports.sh` forbids a `GebTests/<subtree>/` file from
importing a `GebTests.<subtree>.*` test sibling, because the test
roots are scanned with the same allowed-import list as the source
roots (`Mathlib.*`, `Geb.Mathlib.*` only). This blocks the
narrow-and-deep test index chain (a `GebTests/Mathlib/Data.lean`
importing `GebTests.Mathlib.Data.PFunctor`). Fix the script and the
rule documentation so test files may import their own test siblings,
while keeping source roots unable to import test modules and keeping
the no-leakage rule binding test files for both relevant prefixes.
No source-code or content change.

## Background

`check_subtree` (`scripts/lint-imports.sh`) takes one leakage prefix,
one optional required-init module, a set of find-roots, and an
allowed-import list, and enforces three rules per file: module-form
header, allowed imports (no bare umbrella), required init, and
no-leakage of the self-prefix outside import lines. It is currently
called once per upstream target, scanning source and test roots
together:

```text
check_subtree "Geb.Mathlib." ""           Geb/Mathlib GebTests/Mathlib \
  -- "Mathlib." "Geb.Mathlib."
check_subtree "Geb.Cslib."   "Cslib.Init" Geb/Cslib   GebTests/Cslib \
  -- "Mathlib." "Cslib." "Geb.Cslib."
```

So `GebTests/Mathlib/` inherits the source allowed-import list, which
omits `GebTests.Mathlib.*`. This is the first time `GebTests/Mathlib/`
gains a subdirectory index chain, which is what surfaces the gap.

The floodgate intent is that a test subtree mirrors its source
subtree: as `Geb/Mathlib/` files import `Geb.Mathlib.*` siblings,
`GebTests/Mathlib/` files should import `GebTests.Mathlib.*` siblings;
on extraction both map to the corresponding upstream module
namespaces.

## Design

Split each upstream target into a source call and a test call with
distinct allowed-import lists and leakage prefixes.

### Allowed imports and leakage, per root

| Root | Allowed imports | Leakage-forbidden prefixes |
| --- | --- | --- |
| `Geb/Mathlib/` | `Mathlib.*`, `Geb.Mathlib.*` | `Geb.Mathlib.` |
| `GebTests/Mathlib/` | `Mathlib.*`, `Geb.Mathlib.*`, `GebTests.Mathlib.*` | `Geb.Mathlib.`, `GebTests.Mathlib.` |
| `Geb/Cslib/` | `Mathlib.*`, `Cslib.*`, `Geb.Cslib.*` | `Geb.Cslib.` |
| `GebTests/Cslib/` | `Mathlib.*`, `Cslib.*`, `Geb.Cslib.*`, `GebTests.Cslib.*` | `Geb.Cslib.`, `GebTests.Cslib.` |

Rationale for the leakage column on test roots: a test file may
import its test siblings, but neither the source self-prefix
(`Geb.Mathlib.`) nor the test self-prefix (`GebTests.Mathlib.`) may
appear outside import lines — both are rewritten on extraction, so
bodies and docstrings use bare names (via `open`). Keeping
`Geb.Mathlib.` in the test leakage set is what catches a test
docstring that names `Geb.Mathlib.Foo` (the existing behaviour must
not regress). Source roots are unchanged and cannot import
`GebTests.*` (the test prefix is absent from their allowed list), so
source still cannot depend on tests.

The `GebTests.<subtree>.*` strings are distinct from `Geb.<subtree>.*`:
the literal `Geb.Mathlib.` does not occur within `GebTests.Mathlib.`
(the character after `Geb` is `T`, not `.`), so the two leakage checks
are independent.

### Implementation

Generalize `check_subtree` to accept a list of leakage prefixes (Rule
2 loops over them) instead of a single one; the required-init,
allowed-import, module-form, and umbrella rules are unchanged. Replace
the two call sites with four (source + test per upstream target) using
the table above. The Cslib test root retains the mandatory
`Cslib.Init` import requirement.

Exact argument-parsing form (verified by prototype):
`<leakage-prefix>... -- <required-init> <roots>... -- <allowed-prefix>...`
— two `--` separators, the first terminating the leakage-prefix list,
the second the existing separator between roots and allowed prefixes.
(A single `--` is ambiguous: with a list-valued leakage parameter and
a possibly-empty `required-init`, the parser cannot tell where the
leakage list ends.)

## Documentation

`docs/rules/upstream-eligible.md` § Subtree import rules: the table
currently lists `Geb/Mathlib/ (and tests)` as one row with allowed
imports `Mathlib.*`, `Geb.Mathlib.*`. Split or annotate it so test
roots additionally allow `GebTests.<subtree>.*` (test-sibling
imports), and note that the test self-prefix `GebTests.<subtree>.`
also must not leak outside import lines. `scripts/lint-imports.sh`'s
header comment is updated to match.

## Testing

`scripts/tests/test-lint-imports.sh` (the smoke test) gains cases for
each subtree (the `Mathlib` forms below, plus the symmetric `Cslib`
analogs — `GebTests.Cslib.*` / `Geb.Cslib.*`):

- a `GebTests/Mathlib/` file importing a `GebTests.Mathlib.*` sibling
  passes (the new allowance);
- a `Geb/Mathlib/` (source) file importing a `GebTests.Mathlib.*`
  module fails (source cannot depend on tests);
- a `GebTests/Mathlib/` file naming `GebTests.Mathlib.Foo` outside an
  import line fails (test self-prefix leakage);
- a `GebTests/Mathlib/` file naming `Geb.Mathlib.Foo` outside an
  import line fails (source self-prefix leakage still binds tests).

The existing cases must continue to pass.

## Verification

- `bash scripts/tests/test-lint-imports.sh` passes (old and new
  cases).
- `bash scripts/lint-imports.sh` is clean on the current tree (the
  refactor changes no verdict for existing files).
- `markdownlint-cli2` on the touched rule doc.

## References

- `scripts/lint-imports.sh`, `scripts/tests/test-lint-imports.sh`.
- `docs/rules/upstream-eligible.md` § Subtree import rules.
- `CONTRIBUTING.md` § Floodgate test.
