---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

# CI and workflow conventions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Commit-message convention (mathlib-derived)](#commit-message-convention-mathlib-derived)
- [Pre-push checklist](#pre-push-checklist)
- [Action pinning policy](#action-pinning-policy)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies to GitHub Actions workflow files and scripts.

## Commit-message convention (mathlib-derived)

See `https://leanprover-community.github.io/contribute/commit.html`
for mathlib's full convention.

```text
<type>(<optional-scope>): <subject>

<body>

<footers>
```

Types: `feat | fix | doc | style | refactor | test | chore | perf | ci`.
Imperative present tense, no capital, no trailing period. Subject
under 72 characters when possible.

Documented footers: `Closes #123, #456`, `BREAKING CHANGE: ...`,
`- [ ] depends on: #XXXX`. Mathlib's published convention does not
include `Moves:` or `Deletions:`, so nor does ours.

## Pre-push checklist

`scripts/pre-push.sh` is the authoritative checklist; it exits
non-zero on any failure. This summary groups what it runs; consult
the script for the exact order.

Build and Lean linters:

- `lake exe cache get` populates the full mathlib olean cache
  (mirroring CI's `leanprover/lean-action`). The cache fetch is
  required because `lake build` alone fetches only the oleans
  `Geb` imports; the `lake shake` step injects an arbitrary
  mathlib import and needs that module's olean present, which
  after a toolchain bump it otherwise would not be.
- `lake build`, `lake test`, `lake lint`.
- `lake build GebTests` then `lake lint -- GebTests`. The axiom
  env_linter (`GebMeta.detectNonstandardAxiom`) runs under both
  `lake lint` invocations (`Geb` and `GebTests`), failing when a
  declaration depends on an axiom outside `{propext, Quot.sound}`,
  except that modules in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only that).
- `lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests`.

Script self-tests:

- `scripts/lint-imports.sh` and `scripts/tests/test-lint-imports.sh`.
- `scripts/tests/test-lake-shake.sh`,
  `scripts/tests/test-extract-pr.sh`,
  `scripts/tests/test-axiom-linter.sh`,
  `scripts/tests/test-lint-driver.sh`.
- `scripts/tests/test-mathlib-bump-detect.sh`,
  `scripts/tests/test-jj-bump-detect.sh`,
  `scripts/tests/test-regenerate-integration.sh`,
  `scripts/tests/test-diff-against-main.sh`.
- `scripts/hooks/tests/test-block-mutating-git.sh`.

Markdown and project-rule checks:

- `doctoc --dryrun --update-only .` (TOC freshness; skipped when
  `doctoc` is absent) and `markdownlint-cli2 '**/*.md'`.
- `scripts/lake-update-warning.sh` (warns on a `lake-manifest.json`
  change outside a `bump/*` or `chore/bootstrap` branch).
- Docs-coverage reminder: Lean changes under an upstream-eligible
  or the `Geb/Internal/` subtree without a `docs/index.md` change.

Informational reminders (printed, not enforced):

- (PR-candidate) PR descriptions, Zulip messages, and GitHub
  comments are user-authored ("use your own words"); the user
  reviews the diff line-by-line before any push.
- (Lean-content) run `lean4:golf` on changed proofs and
  `lean4:review` on the diff; (PR-candidate)
  `pr-review-toolkit:review-pr`.

## Action pinning policy

All third-party actions in `.github/workflows/*.yml` are pinned to
a specific commit SHA, with the SHA followed by a comment naming
the corresponding tag for human readers. Dependabot
(`.github/dependabot.yml`) opens a pull request bumping the SHA and
its tag comment when an action publishes a new release; review the
upstream release notes before merging.
