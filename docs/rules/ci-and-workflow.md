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
- [Literate site build](#literate-site-build)
- [Loading modes](#loading-modes)
- [Certificates](#certificates)
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
checks repository content: the Lean sources, the Verso manual and
literate site rendered from them (§ Verso manual build and
§ Literate site build), and the Markdown that the build system acts
on. `scripts/test-tooling.sh` runs the build system's own self-tests.
`scripts/pre-push-full.sh` runs `scripts/pre-push.sh` then
`scripts/test-tooling.sh`, and is the one to run for a change
touching the build system itself; content-only changes need
`scripts/pre-push.sh` alone. Each exits non-zero on any failure.
This summary groups what they run; consult the scripts for the
exact order.

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
  required because `lake build` alone fetches only the oleans the
  root libraries `Geb` and `GebLang` import; the `lake shake` step
  injects an arbitrary mathlib import and needs that module's
  olean present, which after a toolchain bump it otherwise would
  not be. The fetch runs only when `lean-toolchain` or
  `lake-manifest.json` differs from the copy recorded at the last
  fetch (`.lake/cache-get.stamp`), and holds a lock in the cache
  directory while it runs. Both guards follow from `cache get`
  unpacking each module whose local Lake `depHash` differs from the
  archive's: part of the dependency tree disagrees on that hash
  while the artifacts are identical, so an unguarded fetch
  overwrites a locally built tree that Lake rebuilds, and the cache
  directory is shared across jj workspaces while downloads use a
  fixed temporary name.
- `lake build`, `lake test`.
- `scripts/bootstrap.sh check`: the bootstrap's committed image and
  emitted Lean regenerate byte for byte, and the compiler built from
  the emitted Lean reproduces both (the manual's Bootstrap chapter,
  § Speed and a second host); every source under `bootstrap/` is a
  fixed point of `geb-fmt` and, where the release pinned in
  `scripts/parinfer/` is installed, of both of parinfer's modes (§ Source
  documents and the formatter).
- `lake build GebTests` then `lake exe batteries/runLinter GebTests`, then
  `scripts/literate.sh build` (§ Literate site build), whose
  `lake lint` lints `Geb` and whose direct `batteries/runLinter` invocation
  lints `GebLang`, then
  `scripts/manual.sh build` (§ Verso manual build). The axiom
  env_linter (`GebMeta.detectNonstandardAxiom`) runs under every
  `batteries/runLinter` invocation (`Geb`, `GebTests`, `GebLang` and
  `GebManual`), failing when a
  declaration depends on an axiom outside `{propext, Quot.sound}`,
  except that modules in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only that).
- `lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests GebLang`.

then the Markdown and project-rule checks:

- `scripts/lint-imports.sh` (the subtree import rules; see
  `docs/rules/upstream-eligible.md`).
- `scripts/check-transitive-imports.sh` (the closure rules the
  direct-import lists cannot see). `scripts/lint-imports.sh` bounds
  each module's direct imports; this bounds the closure: a
  `Geb/Mathlib/` or `GebTests/Mathlib/` module whose `GebLang`
  dependencies reach `Cslib.*` is Cslib-track and belongs under the
  Cslib subtree.
- `scripts/check-commit-msg.sh` over the branch's commit subjects.
  This step, the branch diff behind the two checks below it, and
  the branch name `scripts/lake-update-warning.sh` reads come from
  whichever VCS the checkout uses, as `scripts/lib/vcs.sh` decides
  per `AGENTS.md` § Version control follows the checkout.
- `doctoc --dryrun --update-only .` (TOC freshness; skipped when
  `doctoc` is absent) and `markdownlint-cli2 '**/*.md'` (required:
  the run fails when it is absent).
- `scripts/check-md-links.sh` (every internal Markdown link target
  exists; see `docs/rules/markdown-writing.md` § Link conventions).
- `scripts/lake-update-warning.sh` (warns on a `lake-manifest.json`
  change outside a `bump/*` or `chore/bootstrap` branch).
- Docs-coverage reminder: Lean changes under an upstream-eligible
  subtree, `Geb/Prototypes/`, or `GebLang/` without a `docs/index.md`
  change.

`scripts/test-tooling.sh` runs the script and hook self-tests. Each
exercises the tool named in its own filename against staged
fixtures:

- `scripts/tests/test-lint-imports.sh`,
  `scripts/tests/test-check-transitive-imports.sh`,
  `scripts/tests/test-lake-shake.sh`,
  `scripts/tests/test-extract-pr.sh`,
  `scripts/tests/test-axiom-linter.sh`,
  `scripts/tests/test-lint-driver.sh`,
  `scripts/tests/test-check-md-links.sh`,
  `scripts/tests/test-check-commit-msg.sh`,
  `scripts/tests/test-eal.sh` (skipped when the `z3-solver`
  Python package is absent).
- `scripts/tests/test-mathlib-bump-detect.sh`,
  `scripts/tests/test-jj-bump-detect.sh`,
  `scripts/tests/test-regenerate-integration.sh`,
  `scripts/tests/test-diff-against-main.sh`,
  `scripts/tests/test-vcs.sh`.
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
`lake build verso/verso-literate`, `lake build GebManual`,
`lake exe batteries/runLinter GebManual`,
`lake exe geb-manual --output manual/_out`, in that order: build
precedes lint so a clean checkout lints built oleans, and the lint
runs the axiom linter over the manual
(`docs/rules/lean-coding.md` § Verso manual modules). A chapter that
includes a literate module runs `lake query +Mod:literate` in a
subprocess while it elaborates, which builds that module's literate
facet on demand. Preparing the shared `verso-literate` executable before
chapter elaboration prevents those independent Lake processes from linking
the same output concurrently. The generator step, like `doc-build.yml`'s doc-gen4
steps, runs with `--log-level=warning`: each links a dependency's C
sources (`leansqlite`'s bundled SQLite), whose compiler warnings Lake
logs, and replays on every later run, at its informational level, so
that a contributor does not take them for a warning in code of this
repository. Warnings and errors stay visible, and a Lean warning in
this repository is an error under `warningAsError`; the steps that
compile this repository's Lean run at the default level. CI runs the
script in `doc-build.yml`, for every
pull request and on a monthly schedule, and uploads the HTML as the
`geb-manual` artifact; `scripts/pre-push.sh` runs it locally.
`pages.yml` runs it on every push to `main` and deploys the HTML
to GitHub Pages at the site root, beside the literate site
(§ Literate site build).
The manual is outside `defaultTargets` and the test driver, so
`lake build` and `lake test` build no Verso;
`scripts/tests/test-lint-driver.sh` § 3 guards the workflow step.

## Literate site build

The literate site (the `Geb` and `GebLang` libraries rendered by
Verso's literate pipeline) builds only through
`scripts/literate.sh build`: `lake build`, `lake lint`,
`lake exe batteries/runLinter GebLang`, `lake build :literateHtml`,
in that order, so a clean
checkout lints built oleans. `literate.toml` scopes the site to the
two libraries; without that scoping the package facet renders and
builds every library and executable of the package. Rendering the
site builds the literate facet of every module of both libraries, so
it is the check that each module is renderable, which
`docs/rules/lean-coding.md` § Literate modules requires of every new
one. CI runs the script in `doc-build.yml`, for every pull request,
and uploads the HTML as the `geb-literate` artifact, beside
`lake build Geb:docs` and `lake build GebLang:docs` for the doc-gen4
reference; `scripts/pre-push.sh` runs it locally, and `pages.yml`
deploys it to GitHub Pages under `literate/` beside the manual
(§ Verso manual build); that workflow is derived from the one
`lake exe verso setup-literate` generates, and its header says why
it is not that file. The rendering is outside `defaultTargets`, as
the manual is; the libraries themselves are the `defaultTargets`,
so an ordinary `lake build` compiles them without Verso, which the
first Verso build compiles from source.
`scripts/tests/test-lint-driver.sh` § 3 guards the workflow step.

The pre-push and document build scripts default `LEAN_NUM_THREADS` to four,
preserving an explicit setting. Roots other than `Geb` invoke
`batteries/runLinter` directly, because `lake lint` prepends its configured
`Geb` argument. The full checklist records that single `lake lint` run in a
temporary file and passes its path as `GEB_LINT_LOG` to the lint-driver
regression test. The test validates the recorded invocation and coverage;
when run standalone it executes `lake lint` itself.

A doc-gen4 build needs `DOCGEN_SRC=file` when it is run outside CI.
doc-gen4 resolves source links by running `git remote get-url origin` in the
package directory: a secondary `jj` workspace has no `.git` directory, and in
the colocated workspace the command succeeds but returns an `ssh://` URL,
which doc-gen4 does not accept, taking `git@host:org/repo.git` and
`https://host/org/repo` alone. The variable selects the source-link scheme
(`github`, `vscode` or `file`) and changes nothing else about the generated
pages, so a local measurement of page content is unaffected by it. CI's
checkout provides an `https` remote, so the workflows set nothing.

## Loading modes

The loading of the program whose agreement with Lean is proved, the
metalogic's, declared by the modules `scripts/bootstrap.sh` generates
under `bootstrap/lean/GebMirror/Metalogic/Load/`, is
checked in one of two modes, which the environment variable
`GEB_LOADING` selects (`Geb/Prototypes/Kernel/LoadCommand.lean`). In
the mode `native`, the default, each definition's equation of types and
loading step, the facts whose proofs evaluate the checker-evaluator, are
axioms declared after the compiled checker-evaluator has loaded the
program, and the axiom linter permits the axioms of those modules
(`GebMeta.loadingAxiomModules`). In the mode `rfl` they are theorems the
kernel checks by that evaluation, which takes hours, and the linter
permits none of them. `scripts/pre-push.sh` and `scripts/pre-push-full.sh`
take `--loading=native` or `--loading=rfl`; every other workflow builds in
the mode `native`. Lake does not track the variable, so a module built in
one mode is reused in the other: the mode `rfl` of `scripts/pre-push.sh`
deletes the outputs of the modules declaring the loading and of those
depending on them, and `slow-checks.yml` builds without the GitHub cache.
A stale module built in the mode `native` that is left in an `rfl` build
depends on an axiom of the loading, which the linter then rejects.
`slow-checks.yml` builds and lints `GebTests` in the mode `rfl` daily and
on demand.

## Certificates

The developments the internal language proves about the bootstrap's
programs (the fundamental lemma of the evaluator, weakening, substitution,
the expansion of kernel forms and the lemmas of trees) are found by
searches for derivations, which take tens of minutes compiled, and are
committed as certificates, `bootstrap/certificates/*.cert`, as the
bootstrap's image is. A certificate stores a development's declarations,
each theorem with its derivation, as the table of the distinct nodes of
their tree (`GebTests/Prototypes/FreeTopos/Stored.lean`). The modules of
`GebTests/Prototypes/FreeTopos/Certified/` read each certificate and state
that the development proves its theorem in the program it is about. The
check is decided by Lean's evaluator and declared by the command
`evaluation_axiom` as an axiom in either loading mode, the kernel's
reduction of a check of that size being out of reach. The axiom linter
permits an axiom so declared only where the modules of
`GebMeta.evaluationAxiomModules` declare it, and `#print axioms` lists it
for every declaration that depends on it.

`scripts/certificates.sh regen` runs the searches, by the executable
`geb-certify`, and writes the certificates; `scripts/certificates.sh
check` writes them into a temporary directory and compares them with the
committed ones. A change to a development's proofs, or to a program it is
about, is followed by `regen`. `slow-checks.yml` runs `check` daily and on
demand; the pre-push checklist and the other workflows check the committed
certificates and do not search.

## Action pinning policy

All third-party actions in `.github/workflows/*.yml` are pinned to
a specific commit SHA, with the SHA followed by a comment naming
the corresponding tag for human readers. Dependabot
(`.github/dependabot.yml`) opens a pull request bumping the SHA and
its tag comment when an action publishes a new release; review the
upstream release notes before merging.
