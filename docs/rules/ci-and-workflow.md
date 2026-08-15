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
- [Verso manual build](#verso-manual-build)
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
at most 72 characters: `scripts/check-commit-msg.sh` rejects a
longer one, so the bound is enforced rather than advisory.

Documented footers: `Closes #123, #456`, `BREAKING CHANGE: ...`,
`- [ ] depends on: #XXXX`. Mathlib's published convention does not
include `Moves:` or `Deletions:`, so nor does ours.

## Pre-push checklist

The checklist is split by what a change touches. `scripts/pre-push.sh`
checks repository content: the Lean sources and the Markdown that
the build system acts on. `scripts/test-tooling.sh` runs the build
system's own self-tests. `scripts/pre-push-full.sh` runs both, in
that order, and is the one to run for a change touching the build
system itself; content-only changes need `scripts/pre-push.sh`
alone. Each exits non-zero on any failure. This summary groups what
they run; consult the scripts for the exact order.

`scripts/test-tooling.sh` discovers its tests by glob over
`scripts/tests/test-*.sh` and `scripts/hooks/tests/test-*.sh`, so a
new test script runs by virtue of existing. Several of those tests
drive `lake` against the live project, which is why
`pre-push-full.sh` runs `pre-push.sh` first: they need the built
tree and populated olean cache its `lake exe cache get` and
`lake build` steps leave behind. Running `test-tooling.sh` on its
own requires a prior `lake build`.

`scripts/pre-push.sh` runs the build and Lean linters:

- `lake exe cache get` populates the full mathlib olean cache
  (mirroring CI's `leanprover/lean-action`). The cache fetch is
  required because `lake build` alone fetches only the oleans
  `Geb` imports; the `lake shake` step injects an arbitrary
  mathlib import and needs that module's olean present, which
  after a toolchain bump it otherwise would not be. The fetch runs
  only when `lean-toolchain` or `lake-manifest.json` differs from
  the copy recorded at the last fetch (`.lake/cache-get.stamp`),
  and holds a lock in the cache directory while it runs. Both
  guards follow from `cache get` unpacking each module whose local
  Lake `depHash` differs from the archive's: part of the dependency
  tree disagrees on that hash while the artifacts are identical, so
  an unguarded fetch overwrites a locally built tree that Lake
  rebuilds, and the cache directory is shared across jj workspaces
  while downloads use a fixed temporary name.
- `lake build`, `lake test`, `lake lint`.
- `lake build GebTests` then `lake lint -- GebTests`. The axiom
  env_linter (`GebMeta.detectNonstandardAxiom`) runs under both
  `lake lint` invocations (`Geb` and `GebTests`), failing when a
  declaration depends on an axiom outside `{propext, Quot.sound}`,
  except that modules in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only that).
- `lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests`.

then the Markdown and project-rule checks:

- `scripts/lint-imports.sh` (the subtree import rules; see
  `docs/rules/upstream-eligible.md`).
- `scripts/check-commit-msg.sh` over the branch's commit subjects.
- `doctoc --dryrun --update-only .` (TOC freshness; skipped when
  `doctoc` is absent) and `markdownlint-cli2 '**/*.md'`.
- `scripts/check-md-links.sh` (every internal Markdown link target
  exists; see `docs/rules/markdown-writing.md` § Link conventions).
- `scripts/lake-update-warning.sh` (warns on a `lake-manifest.json`
  change outside a `bump/*` or `chore/bootstrap` branch).
- Docs-coverage reminder: Lean changes under an upstream-eligible
  or the `Geb/Internal/` subtree without a `docs/index.md` change.

`scripts/test-tooling.sh` runs the script and hook self-tests. Each
exercises the tool named in its own filename against staged
fixtures:

- `scripts/tests/test-lint-imports.sh`,
  `scripts/tests/test-lake-shake.sh`,
  `scripts/tests/test-extract-pr.sh`,
  `scripts/tests/test-axiom-linter.sh`,
  `scripts/tests/test-lint-driver.sh`,
  `scripts/tests/test-check-md-links.sh`,
  `scripts/tests/test-check-commit-msg.sh`.
- `scripts/tests/test-mathlib-bump-detect.sh`,
  `scripts/tests/test-jj-bump-detect.sh`,
  `scripts/tests/test-regenerate-integration.sh`,
  `scripts/tests/test-diff-against-main.sh`.
- `scripts/hooks/tests/test-block-mutating-git.sh`.

The scripts report what the checks found and nothing else. Project
rules that bind the contributor rather than the tree, and the tool
invocations an agent is expected to make, live in the Markdown that
states them; restating either in build output addresses the reader
who runs the checklist as though they were its subject. The
docs-coverage notice above is the one printed line that does not
fail the run, because the check behind it is a heuristic over the
branch diff rather than a decision about the tree.

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

## Action pinning policy

All third-party actions in `.github/workflows/*.yml` are pinned to
a specific commit SHA, with the SHA followed by a comment naming
the corresponding tag for human readers. Dependabot
(`.github/dependabot.yml`) opens a pull request bumping the SHA and
its tag comment when an action publishes a new release; review the
upstream release notes before merging.
