# Module-scoped `Classical.choice` allowlist for the axiom linter: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Scope](#scope)
- [Background](#background)
- [Design](#design)
  - [`GebMeta` decision logic](#gebmeta-decision-logic)
  - [The linter](#the-linter)
  - [Safety semantics](#safety-semantics)
  - [Allowlist lifecycle](#allowlist-lifecycle)
- [Testing](#testing)
- [Out of scope](#out-of-scope)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Status

Design for review. Spec and plan are transient artifacts removed in
the topic branch's final commits, per `CONTRIBUTING.md` § Concern
shape. This concern lands on its own branch off `main`
(`feat/axiom-linter-allowlist`); dependent feature branches rebase
onto the updated `main` afterward.

## Scope

Extend `GebMeta.detectNonstandardAxiom` so that a named set of exact
modules may additionally depend on `Classical.choice` (and only
`Classical.choice`), while every other module remains held to the
strict constructive set `{propext, Quot.sound}`. No change to any
`Geb` or production `GebTests` content; the allowlist contains only
the test fixture module introduced by this branch.

## Background

The repo's constructive-only discipline forbids `Classical.choice`:
`GebMeta.detectNonstandardAxiom` (`GebMeta.lean`) fails `lake lint`
for any `Geb`/`GebTests` declaration whose `collectAxioms` result
leaves `{propext, Quot.sound}`.

Building polynomial-functor content on mathlib's category theory
requires this relaxation. mathlib's `CategoryTheory.Over` is
`Classical.choice`-dependent at the type level: a declaration whose
signature merely names `Over X` depends on `Classical.choice` (an
identity `fun X : Over Bool => X` reports
`[propext, Classical.choice, Quot.sound]`), because `Over X` unfolds
to `CostructuredArrow (𝟭 _) X` and that specialization references a
`Classical.choice`-tainted constant. The taint is in mathlib's proof
automation (`cat_disch`/`aesop_cat` discharges category and functor
coherence goals classically), not in the categorical data: the bare
`Category (Type u)` instance and `PFunctor.Obj`/`PFunctor.map` are
axiom-free.

The dependent development is therefore split: a constructive core (no
`Over`, certified by the strict linter) and a thin categorical
wrapper (named in the allowlist, permitted `Classical.choice`). This
document specifies the linter change that the wrapper requires. The
constructive core and wrapper are a separate concern on a separate
branch.

## Design

### `GebMeta` decision logic

Factor the permitted-axiom decision into pure functions taking the
permitted set explicitly (so the logic is unit-testable without the
environment):

```lean
/-- Constructive standard set: `{propext, Quot.sound}`. -/
def standardAxioms : NameSet := …  -- unchanged

/-- Exact module names additionally permitted to depend on
`Classical.choice` (and only `Classical.choice`). On this branch it
contains only the test fixture module (named in the plan);
categorical-wrapper feature branches append their own module name. -/
def classicalAllowedModules : NameSet := …  -- {test fixture module}

/-- Permitted axioms for a declaration defined in module `mod`. -/
def permittedAxioms (mod : Name) : NameSet :=
  if classicalAllowedModules.contains mod then
    standardAxioms.insert ``Classical.choice
  else standardAxioms

/-- The elements of `used` not in the permitted set. -/
def offendingAxioms (permitted : NameSet) (used : Array Name) : Array Name :=
  used.filter (fun a => !permitted.contains a)
```

`offendingAxioms` gains a leading `permitted` parameter (previously it
closed over `standardAxioms`). The existing unit tests are updated to
pass `standardAxioms` explicitly.

### The linter

```lean
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let mod := moduleOf? (← getEnv) declName |>.getD .anonymous
    let bad := offendingAxioms (permittedAxioms mod) (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  …
```

`moduleOf?` resolves a declaration's defining module via
`Environment.getModuleIdxFor?` composed with the environment header's
`moduleNames`, with type `Environment → Name → Option Name`:

```lean
def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none
```

(`Environment.getModuleFor?` does not exist in the pinned toolchain.)
`Linter.test` runs in `MetaM`, where `getEnv` is available.

### Safety semantics

- Allowlisting a module adds exactly `Classical.choice` to its
  permitted set, and nothing else. `sorryAx`, `Lean.ofReduceBool`,
  and every other axiom remain forbidden in allowlisted and
  non-allowlisted modules alike.
- Fail-safe: if `moduleOf?` returns `none` (module unresolvable),
  the declaration is held to the strict `{propext, Quot.sound}` set.
  Unknown is never permitted.
- The linter cannot distinguish `Classical.choice` originating in
  mathlib from `Classical.choice` introduced locally; both are the
  same axiom. Allowlisting a module therefore trusts that module.
  The mitigation is to keep allowlisted modules thin (the categorical
  wrapper only), minimizing room for unintended classicality.

### Allowlist lifecycle

`classicalAllowedModules` contains only the test fixture module on
this branch, so the change permits `Classical.choice` in no `Geb` or
production `GebTests` content. A feature that introduces a categorical
wrapper module appends that exact module name to the set as part of
its own diff.

## Testing

The decision logic is the risk surface and is tested directly; the
environment plumbing is tested in isolation.

- Pure-function unit tests (extending
  `GebTests/Internal/AxiomLinter.lean`):
  - `permittedAxioms mod` equals `standardAxioms` for a
    non-allowlisted `mod`, and `standardAxioms` with
    `Classical.choice` inserted for an allowlisted `mod`.
  - `offendingAxioms`: under the strict set, `Classical.choice` is
    offending; under the permissive set it is not; under both sets
    `sorryAx` is offending (the assertion that the relaxation did not
    widen beyond `Classical.choice`); `propext` and `Quot.sound` are
    never offending.
- Module-resolution meta-test: an `#eval`/`#guard_msgs` check, in an
  environment-bearing monad (`CommandElabM`, where `getEnv` is
  available), that `moduleOf?` resolves a known declaration to a
  non-`anonymous` module. It asserts `.isSome` / non-anonymous rather
  than an exact module `Name`, which is toolchain-dependent. The
  declaration must be an imported one (e.g. `propext` or a `GebMeta`
  constant): `getModuleIdxFor?` returns `none` for a declaration
  defined locally in the test module, which would defeat the check.
- Allowed-direction integration fixture: a dedicated `GebTests`
  module that is listed in `classicalAllowedModules` and contains a
  declaration depending on `Classical.choice` (a deliberate, valid
  use). `lake lint` passing over the repository proves the end-to-end
  allow path. The forbidden direction is not a standing fixture (it
  would fail CI by construction) and is covered by the unit tests.

## Out of scope

- Per-declaration opt-in (an attribute). Granularity is exact module
  names, by decision; an attribute mechanism is not added.
- Module-prefix matching. Exact names only, so no module is permitted
  by accident.
- Any relaxation for axioms other than `Classical.choice`.

## References

- `GebMeta.lean` — the current linter.
- `GebTests/Internal/AxiomLinter.lean` — current pure-function tests.
- `docs/rules/lean-coding.md` § Constructive-only Lean code.
- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Lean/Environment.lean` (core Lean) —
  `Environment.getModuleIdxFor?`, `EnvironmentHeader.moduleNames`.
