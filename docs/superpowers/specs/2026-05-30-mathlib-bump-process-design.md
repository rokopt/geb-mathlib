# Mathlib bump process

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [What the standard tooling does](#what-the-standard-tooling-does)
  - [mathlib-update-action (two-job)](#mathlib-update-action-two-job)
  - [lean-update](#lean-update)
  - [lean-release-tag and the LeanProject template](#lean-release-tag-and-the-leanproject-template)
- [Design decisions](#design-decisions)
  - [Cadence: mathlib release tags](#cadence-mathlib-release-tags)
  - [CSLib and doc-gen4 are version-locked to mathlib](#cslib-and-doc-gen4-are-version-locked-to-mathlib)
- [End-state architecture](#end-state-architecture)
  - [Standing lakefile.toml change](#standing-lakefiletoml-change)
  - [create-release.yml (self-tagging)](#create-releaseyml-self-tagging)
  - [update.yml job 1: detect](#updateyml-job-1-detect)
  - [update.yml job 2: apply with lockstep](#updateyml-job-2-apply-with-lockstep)
  - [Validation and merge](#validation-and-merge)
- [Bootstrapping the first project version tag](#bootstrapping-the-first-project-version-tag)
- [Permissions and tokens](#permissions-and-tokens)
- [Interaction with the review and tagging discipline](#interaction-with-the-review-and-tagging-discipline)
- [Non-goals](#non-goals)
- [Open questions to resolve during planning](#open-questions-to-resolve-during-planning)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc -->

## Goal

Replace the current `.github/workflows/update.yml` with a mathlib
bump process that, on a schedule, detects a newer mathlib release,
bumps mathlib together with the version-locked dependencies
(`cslib`, `doc-gen4`), regenerates `lake-manifest.json` and
`lean-toolchain`, builds and tests, and on success opens a pull
request (on failure opens an issue). A contributor reviews the pull
request line-by-line and merges it; nothing merges automatically.

The process follows the `leanprover-community/LeanProject` template
as closely as the project's additional dependencies permit, reusing
the community update, build, and release-tagging actions and
deviating only where the extra dependencies require it.

## Motivation

The shipped `update.yml` invokes only the detection half of
`mathlib-update-action`. That half runs `lake update`, uploads an
`update-metadata` artifact, and stops; it opens no pull request and
no second workflow consumes the artifact. The manual run
`26691389750` confirmed this: it logged `No releases found in the
current project; skipping all tagged versions` and targeted mathlib
`master`, then uploaded the artifact and exited. The CI therefore
detects an update and discards it.

The `LeanProject` template assembles four workflows that together
form a complete cycle. This project shipped one workflow that
performs half of one of those four, so the cycle never closes.

## What the standard tooling does

Verified 2026-05-30 against the sources cited in
[References](#references).

### mathlib-update-action (two-job)

The action is split into a detection action and an application
action, used as two jobs (the template's `update.yml`).

- Root action (`check-for-updates`) is a composite action that
  checks out the repository, configures Lean, runs
  `node dist/index.js`, and (only when an update is available)
  uploads an `update-metadata` artifact. It opens nothing.
- `dist/index.js` (source `src/index.js`) computes the candidate
  tags: it reads mathlib's `git ls-remote --tags`, keeps `v*.*`
  tags, parses them with the npm `semver` package, and compares
  them against the project's own `v*.*` git tags. If the project
  has no version tags, it skips all release tags and targets
  mathlib `master`. Unless `intermediate_releases` is `stable`, it
  appends `master` to the candidate list; `stable` excludes
  prereleases (so no mode yields "latest prerelease tag without
  also targeting master").
- `do-update` is a separate composite action that downloads the
  `update-metadata` artifact for a given tag, moves the
  precomputed `lean-toolchain` and `lake-manifest.json` into place,
  builds via `leanprover/lean-action`, and commits with
  `EndBug/add-and-commit`; `on_update_succeeds` defaults to `pr`,
  `on_update_fails` to `issue`. Because it transports a manifest
  computed by the detection job against the unmodified lakefile, it
  cannot bump dependencies other than mathlib.

### lean-update

`leanprover-community/lean-update` is a separate composite action.
It does not check out the repository itself; it operates on the
caller's working tree. It runs `lake update` directly in that tree
(respecting prior edits to the lakefile), builds and tests via
`leanprover/lean-action`, and on success opens a pull request, on
failure opens an issue (`on_update_succeeds` default `pr`,
`on_update_fails` default `issue`). Because the update is computed
in-tree rather than transported, a step that edits the lakefile
before `lean-update` runs is honoured.

### lean-release-tag and the LeanProject template

The template ships four workflows: `build-project.yml` (build and
test), `create-release.yml`, `update.yml` (the two-job
`mathlib-update-action` pattern), and `deploy-pages.yml` (docs).
`create-release.yml` triggers on a push to `main` that modifies
`lean-toolchain` and runs `leanprover-community/lean-release-tag`,
which creates a `vX.Y.Z` tag and release matching the new Lean
toolchain version. The template repository carries 62 such version
tags. Those tags are the project-tag baseline that
`check-for-updates` requires to track release tags rather than
falling back to `master`.

The four workflows form a cycle: `update.yml` opens a pull request
bumping mathlib; a contributor merges it; the `lean-toolchain`
change on `main` triggers `create-release.yml`, which tags the
repository at the new version; that tag becomes the next baseline
for `update.yml`.

## Design decisions

### Cadence: mathlib release tags

The bump targets mathlib release tags (release candidates and
stable releases), not arbitrary `master` commits. Release-tag
cadence is the template's in-practice behavior, enabled by the
self-tagging the template performs. It also gives the cleanest
form of the version lock described below: at a release tag, the
locked dependencies were built and tested against a mathlib of the
same toolchain.

The detector (`check-for-updates`) appends `master` to its
candidate list under `latest` and `all`. The application job
filters the literal `master` entry out of the candidate list, so
only release tags produce pull requests.

### CSLib and doc-gen4 are version-locked to mathlib

`cslib` is treated as load-bearing from the outset and
version-locked to mathlib: it targets the same domain
(computer-science and programming-language mathematics) that this
project draws on mathlib for, so every addition is checked against
`cslib` to avoid reimplementing what it already provides. `cslib`
publishes a tag for each Lean toolchain version (matching mathlib's
tag string; `v4.31.0-rc1` confirmed present). `doc-gen4` likewise
publishes a matching tag and is required for documentation
generation.

A bump therefore moves `mathlib`, `cslib`, and `doc-gen4` to the
same tag string in lockstep. The template's `do-update` cannot
perform this multi-dependency bump (it transports a mathlib-only
manifest), so the application step uses `lean-update` (in-tree
`lake update`) with a pre-step that sets the three revisions. This
is the sole deviation from the template.

## End-state architecture

| Workflow | Purpose | Source |
| --- | --- | --- |
| `ci.yml` | build, test, lint, shake, axiom check | existing |
| `create-release.yml` | self-tag on toolchain change | template, verbatim |
| `update.yml` | detect and apply bumps | template detect + `lean-update` apply |
| `doc-build.yml` | documentation build | existing |

### Standing lakefile.toml change

Pin `mathlib` to a `rev` tag, uniform with `cslib` and `doc-gen4`
(`mathlib` currently has no `rev` and so tracks `master`). Baseline
revision: `v4.30.0-rc2`. After this change a bump is the
substitution of one tag string into three `rev` fields followed by
`lake update`.

### create-release.yml (self-tagging)

Adopt the template's `create-release.yml` verbatim: trigger on a
push to `main` that modifies `lean-toolchain`; run
`leanprover-community/lean-release-tag` (pinned by commit SHA per
[docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
§ Action pinning policy) with `do-release: true`. This supplies
the project-tag baseline that the detector requires.

### update.yml job 1: detect

Job `check-for-updates` runs `mathlib-update-action`'s root action
(the detector), producing the `new-tags` output. This is the
template's detection, used unchanged, so the semver comparison and
release-selection logic are reused rather than reimplemented. With
the project carrying its own version tags (from
`create-release.yml`), the detector emits mathlib release tags
newer than the project's latest version tag.

### update.yml job 2: apply with lockstep

Job `apply` runs over the `new-tags` matrix with `master` filtered
out. For each release tag:

1. Set the `rev` of `mathlib`, `cslib`, and `doc-gen4` in
   `lakefile.toml` to the tag.
2. Run `lean-update`, which performs an in-tree `lake update`
   (regenerating `lake-manifest.json` and `lean-toolchain` against
   the edited revisions), builds and tests via
   `leanprover/lean-action`, and opens a pull request on success
   (`on_update_succeeds: pr`) or an issue on failure
   (`on_update_fails: issue`).

The job needs `contents: write`, `pull-requests: write`, and
`issues: write`.

### Validation and merge

`ci.yml` runs on the opened pull request and provides the full
build, test, lint, shake, and axiom-check gate. A contributor
reviews the diff line-by-line and merges. No step merges
automatically.

## Bootstrapping the first project version tag

The detector tracks release tags only when the repository already
carries a `v*.*` tag to compare against; otherwise it targets
`master`. Before the process can produce release-tag pull requests,
the repository needs an initial version tag matching the current
toolchain (`v4.30.0-rc2`). Options to resolve during planning:
create the initial tag once by hand, or merge one toolchain change
so `create-release.yml` creates it. Until an initial tag exists,
`check-for-updates` will report `master` only (which the apply job
filters out, yielding no pull request).

## Permissions and tokens

- "Allow GitHub Actions to create and approve pull requests" must
  be enabled for the repository (granted 2026-05-30).
- `create-release.yml` uses `GITHUB_TOKEN` with `contents: write`.
- The apply job opens pull requests and issues; with the
  repository setting above enabled, `GITHUB_TOKEN` suffices. If a
  later constraint requires it, substitute a dedicated token
  secret.

## Interaction with the review and tagging discipline

`create-release.yml` pushes a tag from CI. The tag only marks a
state already merged to `main` through a reviewed pull request (the
toolchain change), so it tags an already-reviewed commit rather
than introducing unreviewed content. The "no tag-pushes without
review" rule in [AGENTS.md](../../../AGENTS.md) binds an agent's
`jj git push`, not a CI workflow; this distinction is recorded so
the two are not conflated. The auto-created tag interacts with the
`main`/`integration` split (tags name commits on `main`); confirm
during planning that tag creation does not disturb integration
regeneration.

## Non-goals

- Tracking mathlib `master` continuously (the
  `downstream-reports` LKG/FKB model). Deferred; the chosen cadence
  is release tags.
- Automatic merging of bump pull requests.
- Bumping `doc-gen4` on a separate cadence from `cslib`/`mathlib`.
  All three move together on each bump.
- Changes to `check-axioms.sh`, the doctoc invocation, or CI path
  triggers (separate concern; tracked for a later branch).

## Open questions to resolve during planning

1. Whether `lean-update` behaves correctly as the application
   engine when the three revisions are pre-pinned to a tag (its
   `lake update` must keep the pinned revisions and regenerate the
   manifest, rather than advancing a branch). If it does not, the
   fallback is a bespoke apply job built from the same primitives
   (`lake update`, `leanprover/lean-action`, a pull-request action,
   an issue action).
2. Whether `cslib` at a given release tag is API-consistent with
   mathlib at the same release tag once a `Geb` module imports
   `Cslib.…` (the locked dependencies pin their own mathlib
   revision, which the top-level requirement overrides).
3. How to seed the initial project version tag
   (see [Bootstrapping the first project version tag](#bootstrapping-the-first-project-version-tag)).
4. Whether to retain a non-blocking `master` canary as a separate
   job (default: no; release tags only).

## Verification

Per the project's test-repo-first discipline, validate on a
numbered test repository before landing the workflows here:

1. A `v4.30.0-rc2` to `v4.31.0-rc1` lockstep bump regenerates the
   manifest and toolchain and produces a green build and a pull
   request.
2. The detector tracks release tags (not `master`) once an initial
   project version tag exists.
3. `create-release.yml` creates a version tag when the merged pull
   request changes `lean-toolchain`.
4. A failing build (a deliberately incompatible tag) opens an issue
   rather than a pull request.
5. Open question 2 above: a module importing `Cslib.…` builds
   against the lockstep-bumped pair.

## References

- [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  — commit-message, pre-push, and action-pinning conventions.
- [AGENTS.md](../../../AGENTS.md) — agent push and review rules.
- `https://github.com/leanprover-community/LeanProject` — template;
  workflows under `.github/workflows/`.
- `https://github.com/leanprover-community/mathlib-update-action`
  — detection and `do-update` actions; detection logic in
  `src/index.js`.
- `https://github.com/leanprover-community/lean-update` — in-tree
  update action.
- `https://github.com/leanprover-community/lean-release-tag`
  — self-tagging action.
