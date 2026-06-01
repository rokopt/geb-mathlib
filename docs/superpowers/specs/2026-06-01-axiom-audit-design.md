# In-Lean axiom audit (`@[env_linter]`)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [Prior art](#prior-art)
- [Background: the `collectAxioms` primitive](#background-the-collectaxioms-primitive)
- [Design](#design)
  - [The linter](#the-linter)
  - [Core logic](#core-logic)
  - [Where the linter lives, and self-exclusion](#where-the-linter-lives-and-self-exclusion)
  - [Linting both libraries](#linting-both-libraries)
  - [Integration](#integration)
- [Testing](#testing)
- [Non-goals](#non-goals)
- [Limitations](#limitations)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

Replace the vendored bash axiom checker (`scripts/check-axioms.sh`)
with an environment linter that, on every `lake lint` run, fails
when any declaration in the `Geb` or `GebTests` libraries depends
on an axiom outside the allowed set `{propext, Quot.sound}`. The
linter runs in the existing `lake lint` step in CI and in
`scripts/pre-push.sh`; no separate executable or CI job is added.

## Motivation

`scripts/check-axioms.sh` is a copy of `check_axioms_inline.sh` from
the third-party AI-agent skill pack `cameronfreer/lean4-skills`
(the in-tree vendoring header misattributes it to
`leanprover-community`). The script appends `#print axioms`
commands to each source file, runs `lake env lean`, and parses the
human-readable output with `grep`/`sed`/regex. That design is
fragile: the predecessor `geb` repository accumulated nine numbered
local modifications to it across two fixes, addressing bare-name
extraction failures, an unabsorbed `maxErrors` cap message, a
SIGPIPE-under-`pipefail` miscategorisation, `lake env lean`
diagnostics that diverge from `lake build` because `lake env lean`
does not apply `lakefile.toml` `[leanOptions]`, a parser that did
not match Lean 4's quoted single-line bracketed output, an
undetected leading-`error:` diagnostic form, and a split
pre/post-marker error classifier.

Of those nine modifications, two are repository-specific features
rather than defect fixes: the `Classical.choice` exclusion (which
this copy has) and the `AXIOM_ALLOW` mechanism (which it does not).
Of the seven defect fixes, this copy already independently
incorporates the core of the parser rewrite, so only that fix's
residue applies; the other six apply in full. Separately, the
surface-syntax declaration extractor misses Lean module-system
`public`/`private` declarations — a defect neither predecessor fix
addressed. Every defect is latent today only because `Geb/` and
`GebTests/` contain no declarations yet; each fires the first time
content lands, and CI (`.github/workflows/ci.yml`) and
`scripts/pre-push.sh` run the check on every push.

All those defects share one root cause: scraping a pretty-printer's
text output and reconstructing the environment from `lake env lean`
stdout. Lean exposes the dependency data directly through
`Lean.collectAxioms`, which reads the kernel environment. The
community-standard mechanism for checking a property of every
declaration in a library is an environment linter
(`@[env_linter]`), run by the `runLinter` driver that `lake lint`
invokes. Implementing the audit as an `@[env_linter]` built on
`collectAxioms` parses no text, runs no `lake env lean`, adds no
new executable or CI job, and follows existing prior art rather
than inventing a tool (see [Prior art](#prior-art)).

## Prior art

The pieces are standard and individually attested:

- The per-declaration axiom check is `#print axioms` /
  `Lean.collectAxioms`, against the standard axioms
  `{propext, Classical.choice, Quot.sound}`; the official Lean
  guide "Validating a Lean Proof" prescribes it.
- `@[env_linter]` is the batteries mechanism for running a test on
  every declaration in a library, used by batteries' own linters
  (`impossibleInstance`, `simpNF`, …) and driven by
  `scripts/runLinter.lean`, which `exit 1`s when any linter
  reports.
- `Lean.collectAxioms` restricting the allowed axioms has direct
  precedent: `teorth/equational_theories` enforces the allow-list
  `[propext, Classical.choice, Quot.sound]` with a hard
  `throwError` from its `@[equational_result]` attribute handler
  (`equational_theories/EquationalResult.lean`); `riccardobrasca/SDG`
  (a constructive project) registers a `detectClassicalLinter`
  (`SDG/Linters/choice.lean`) that flags `Classical.choice`/
  `sorryAx` via `collectAxioms`; and mathlib's `assert_no_sorry`
  (`Mathlib/Util/AssertNoSorry.lean`) checks `sorryAx` the same way.

This design differs from those only where the repository requires:
the allowed set excludes `Classical.choice` (constructive
discipline), and the linter is a hard failure over the whole
library rather than an opt-in per-declaration warning.

## Background: the `collectAxioms` primitive

`Lean.collectAxioms` is defined in core Lean at
`Lean/Util/CollectAxioms.lean` (toolchain `v4.31.0-rc1`, this
repository's pin):

```text
public def collectAxioms [Monad m] [MonadEnv m]
    (constName : Name) : m (Array Name)
```

It returns the sorted transitive axiom dependencies of a constant
and runs in any `MonadEnv` monad, including the `MetaM` in which a
linter's `test` runs. Two properties bear on the design:

- For imported declarations it reads a per-module
  `exportedAxiomsExt`, whose entries are computed at
  olean-serialization time over the full private environment
  (`env.setExporting false`), so the axioms reachable through a
  `private` helper are folded into the dependency set of any
  declaration that reaches it through its kernel terms (type and
  value). Dependencies that are not kernel-term references — for
  example a declaration named only by an attribute such as
  `@[implemented_by]`, or reached only through elaboration/`meta`
  code — are outside `collectAxioms`'s walk. Because the
  `runLinter` driver imports the linted library normally, this
  extension is loaded and used; no manual environment loading is
  required.
- It follows axioms referenced by other axioms: `collect` recurses
  through an `.axiomInfo` constant's type
  (`Lean/Util/CollectAxioms.lean`, toolchain `v4.31.0-rc1`). An
  earlier version did not; the change is attributed to
  `leanprover/lean4` PR #8842 (Lean 4.23.0), which this
  repository's pin postdates.

## Design

### The linter

A single `@[env_linter]` declaration in a downstream-only tooling
module, following the batteries `Linter` interface
(`Batteries/Tactic/Lint/Basic.lean`, structure `Linter` with
`test : Name → MetaM (Option MessageData)`):

```text
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let used ← Lean.collectAxioms declName
    let bad := offendingAxioms used
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad}"
  noErrorsFound :=
    "All declarations depend only on propext and Quot.sound."
  errorsFound :=
    "Declarations depend on non-standard axioms."
  isFast := true
```

The `@[env_linter]` attribute adds it to the default linter set
that `runLinter` executes (`Batteries/Tactic/Lint/Basic.lean`).
`isFast := true` keeps it in the fast set; `collectAxioms` is cheap
because it reads the pre-computed extension. The attribute requires
the declaration to be `public` and `meta` (it rejects others), so
the linter and its helpers sit in a `public meta section`, as
batteries' own linters do; the plan places the module accordingly.

### Core logic

Split into a pure classifier and the linter glue so the classifier
is unit-testable without an environment.

- `standardAxioms : NameSet` containing exactly `propext` and
  `Quot.sound` — the complete allowed set (a `NameSet`, for
  membership tests). Any axiom outside this set is reported,
  including `Classical.choice`, `sorryAx`, and the
  compiler-reflection axioms `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, and `Lean.trustCompiler`.
- `offendingAxioms (used : Array Name) : Array Name` — pure;
  returns the elements of `used` not in `standardAxioms`.
- `test` (above) runs `collectAxioms` per declaration and reports
  via `offendingAxioms`.

`runLinter` applies the linter to the declarations defined in the
target library's modules — `getDeclsInPackage` selects constants
whose defining module name has the package as a prefix
(`Batteries/Tactic/Lint/Frontend.lean`) — so no explicit namespace
filter is needed and the whole imported environment (mathlib,
cslib) is not audited. Auto-generated declarations (recursors,
projections, equation lemmas) are included and reported separately
in the driver's summary; the linter runs on them too, which is
harmless because they are expected to be axiom-clean.

### Where the linter lives, and self-exclusion

The linter is defined in a tooling module that is imported into
the linted libraries' environment (so the `@[env_linter]` is
registered when `runLinter` loads them) but is not itself among
the linted modules (so it does not audit its own metaprogramming
code, which may legitimately use non-standard axioms from the Lean
or batteries libraries). This mirrors the way a standalone audit
executable would have lived outside the audited namespaces. The
exact module path and the set of modules `lake lint` targets are
fixed in the plan; the requirement is: registered in the closure
of both linted libraries, not a lint target itself.

### Linting both libraries

The audit must cover `Geb` and `GebTests`, as the bash step did
(`scripts/check-axioms.sh Geb/ GebTests/`). A no-argument
`lake lint` lints only `defaultTargets` (`Geb`); it does not lint
`GebTests`. `GebTests` must therefore be linted by an explicit
second invocation (`lake lint -- GebTests`, the `--` forwarding
arguments to the `runLinter` driver). This is a definite
requirement, not a contingency: removing the bash step without
adding `GebTests` lint coverage would silently drop `GebTests`
from the axiom audit. The plan fixes the exact invocation form.

### Integration

- `.github/workflows/ci.yml`: the existing `build` job runs
  `leanprover/lean-action` with `lint: true`, which runs
  `lake lint` (no arguments) and so covers `Geb` only; registering
  the linter makes it run over `Geb` there. A step that also lints
  `GebTests` (`lake lint -- GebTests` or equivalent) is added so
  the audit covers both libraries. The separate `axiom_check` job
  (which ran the bash script) is removed.
- `scripts/pre-push.sh`: the existing `lake lint` step
  (`docs/rules/ci-and-workflow.md` § Pre-push checklist item 3)
  runs the linter over `Geb`; a `GebTests` lint invocation is added
  for the same coverage. The separate `scripts/check-axioms.sh`
  step (checklist item 10) is removed.
- `scripts/check-axioms.sh`: delete. (No `scripts/tests/` artifact
  references it; that directory holds only the lake-shake,
  lint-imports, and mathlib-bump-detect tests.)
- `scripts/tests/test-axiom-linter.sh`: add (the negative test,
  see [Testing](#testing)) and wire into `scripts/pre-push.sh` and
  CI alongside the existing `scripts/tests/test-*.sh` smoke tests.
- `docs/rules/lean-coding.md` § Constructive-only and
  `docs/rules/ci-and-workflow.md` item 10: rewrite the
  `scripts/check-axioms.sh` references to describe the linter
  running under `lake lint`. Item 10's note about the bash
  script's fresh-worktree behavior (it "reports 0 declarations and
  exits 3") is dropped; the "exits 3" figure is not reproduced
  from the script source and is not carried forward.
- Historical artifacts that mention the script —
  `docs/superpowers/plans/2026-05-27-docs-audience-split.md` and
  `docs/superpowers/specs/2026-05-30-mathlib-bump-process-design.md`
  — are point-in-time records of prior work and are left unchanged.

## Testing

- Unit: example-based `#guard` tests in a `GebTests` module
  exercising `offendingAxioms` on synthetic `Array Name` inputs
  (the allowed set yields the empty array; `Classical.choice` and
  `sorryAx` are returned). These follow the repository's
  examples-with-concepts discipline and require no environment.
- Positive integration: `lake lint` over the real repository
  passes. This runs in CI and pre-push on every push.
- Negative integration: a committed smoke test
  `scripts/tests/test-axiom-linter.sh`, mirroring
  `scripts/tests/test-lint-imports.sh`. It **stages a throwaway
  fixture in a temporary directory** at test time — a `.lean` file
  that imports the linter's module and declares its own local
  `axiom` plus a declaration depending on it — exercises the
  registered linter against it, and asserts the linter reports the
  violation (non-zero exit and the expected axiom name in the
  output); it also asserts a clean fixture passes. Staging the
  offending declaration in a tempdir, rather than committing a
  `lean_lib` that uses a non-standard axiom, keeps all committed
  source within the constructive-only discipline (only the linter
  module, which is axiom-clean, is committed). The test is run in
  `scripts/pre-push.sh` and CI alongside the existing
  `scripts/tests/test-*.sh` smoke tests. The exact invocation form
  (`#lint only`, the `runLinter` driver, or `lake lint` over the
  staged file) is fixed in the plan.

## Non-goals

- No `AXIOM_ALLOW`-style per-declaration exception mechanism. The
  policy is a hard `{propext, Quot.sound}` with no override; an
  exception mechanism is deferred until a concrete need arises.
- No retention of `scripts/check-axioms.sh` as a fallback. The
  repository carries one axiom-audit mechanism.
- No standalone audit executable. The audit is a linter in the
  existing `lake lint` gate; this avoids a separate executable, a
  separate CI job, and run-time environment loading.
- No pairing with `lean4checker` (kernel replay) in this
  workstream. It is complementary (mathlib runs it in a daily
  cron) and can be added separately if wanted.

## Limitations

- The audit covers declarations `runLinter` visits in the linted
  libraries. A `private` declaration a visited declaration reaches
  through its type or value is covered: its axioms are folded into
  the dependent's pre-computed axiom set (see
  [Background](#background-the-collectaxioms-primitive)). The
  residual gap is code reached only via attributes or
  elaboration-time references.
- `Lean.collectAxioms` reports the axioms a declaration depends on;
  it does not attribute which sub-term introduced an axiom. The
  linter reports the depending declaration, which suffices for the
  gate.
- The linter runs under `lake lint`, not `lake build`; a
  non-standard axiom does not fail `lake build` alone. Both CI and
  `scripts/pre-push.sh` run `lake lint`, so the gate holds on every
  push, matching the bash script's placement.

## Verification

- `lake lint` passes locally on the current (declaration-free)
  repository, with the linter registered.
- `scripts/tests/test-axiom-linter.sh` passes: it confirms the
  linter reports a staged bad-axiom fixture (non-zero exit, axiom
  named) and accepts a clean one.
- The full `scripts/pre-push.sh` checklist passes with the linter
  registered, the new smoke test added, and the bash step removed.

## References

- `Lean/Util/CollectAxioms.lean`, toolchain `v4.31.0-rc1` —
  `Lean.collectAxioms`, the exported-axioms pre-computation, and
  the `.axiomInfo` recursion (PR #8842 behavior).
- `Batteries/Tactic/Lint/Basic.lean` and
  `Batteries/Tactic/Lint/Frontend.lean`, and
  `scripts/runLinter.lean` (batteries) — the `Linter` interface,
  the `@[env_linter]` attribute, and the `runLinter` driver that
  `lake lint` invokes and that exits non-zero on findings.
- `teorth/equational_theories`,
  `equational_theories/EquationalResult.lean` — `collectAxioms`
  axiom allow-list enforced as a hard error.
- `riccardobrasca/SDG`, `SDG/Linters/choice.lean` — a
  `collectAxioms`-based `detectClassicalLinter` for
  `Classical.choice`/`sorryAx`, in a constructive project
  (registered via `addLinter`).
- mathlib `Mathlib/Util/AssertNoSorry.lean` — `collectAxioms`-based
  `sorryAx` check.
- Lean reference, "Validating a Lean Proof"
  (`https://lean-lang.org/doc/reference/latest/ValidatingProofs/`)
  — the standard per-declaration axiom check.
- `cameronfreer/lean4-skills`,
  `plugins/lean4/lib/scripts/check_axioms_inline.sh` — the
  upstream of the vendored bash script.
- `docs/rules/lean-coding.md` § Constructive-only Lean code.
- `docs/rules/ci-and-workflow.md` § Pre-push checklist.
