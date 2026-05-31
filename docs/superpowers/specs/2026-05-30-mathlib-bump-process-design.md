# Mathlib bump process

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [Background: standard tooling and cslib-downstream practice](#background-standard-tooling-and-cslib-downstream-practice)
  - [mathlib-update-action](#mathlib-update-action)
  - [lean-update](#lean-update)
  - [Survey of cslib downstreams](#survey-of-cslib-downstreams)
- [Design decisions](#design-decisions)
  - [Cadence: mathlib release tags](#cadence-mathlib-release-tags)
  - [CSLib and doc-gen4 are version-locked to mathlib](#cslib-and-doc-gen4-are-version-locked-to-mathlib)
  - [Detect against our own pin, not the action's detector](#detect-against-our-own-pin-not-the-actions-detector)
- [End-state architecture](#end-state-architecture)
  - [Standing lakefile.toml change](#standing-lakefiletoml-change)
  - [update.yml job 1: detect](#updateyml-job-1-detect)
  - [update.yml job 2: apply with lockstep](#updateyml-job-2-apply-with-lockstep)
  - [Re-runs while a bump is in flight](#re-runs-while-a-bump-is-in-flight)
  - [Validation and merge](#validation-and-merge)
  - [Post-merge: rebase topics and regenerate integration](#post-merge-rebase-topics-and-regenerate-integration)
- [Permissions and tokens](#permissions-and-tokens)
- [Non-goals](#non-goals)
- [Open questions to resolve during planning](#open-questions-to-resolve-during-planning)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc -->

## Goal

Replace the current `.github/workflows/update.yml` with a mathlib
bump process that, on a schedule, detects a newer mathlib release
tag, bumps `mathlib` together with the version-locked dependencies
`cslib` and `doc-gen4` to that tag, regenerates `lake-manifest.json`
and `lean-toolchain`, builds and tests, and on success opens a pull
request (on failure opens an issue). A contributor reviews the pull
request line-by-line and merges it; nothing merges automatically.

The process reuses the community update and build actions
(`leanprover-community/lean-update`, `leanprover/lean-action`) and
the tag-selection algorithm of `mathlib-update-action`, adding only
the small amount of project-specific glue that no community action
provides: selecting the target tag against the project's own pin
and writing it to three dependency revisions in lockstep.

## Motivation

The shipped `update.yml` invokes only the detection half of
`mathlib-update-action`. That half runs `lake update`, uploads an
`update-metadata` artifact, and stops; it opens no pull request and
no second workflow consumes the artifact. The manual run
`26691389750` confirmed this: it logged `No releases found in the
current project; skipping all tagged versions` and targeted mathlib
`master`, then uploaded the artifact and exited. The CI therefore
detects an update and discards it.

The community tooling is built for projects that depend on mathlib
alone. This project also pins `cslib` and `doc-gen4`, which no
off-the-shelf action bumps in lockstep with mathlib (see
[Survey of cslib downstreams](#survey-of-cslib-downstreams)). The
design below uses the community actions where they fit and supplies
the multi-dependency glue they do not.

## Background: standard tooling and cslib-downstream practice

Verified 2026-05-30 against the sources cited in
[References](#references).

### mathlib-update-action

The action is two composite actions used as two jobs.

- The root action (`check-for-updates`) is not a side-effect-free
  tag computation. For each candidate release it edits **only**
  mathlib's `rev` (`modifyLakefileTOMLMathlibVersion` matches the
  require whose name is `mathlib`), runs `lake update`, and emits
  the tag only if `lean-toolchain`/`lake-manifest.json` changed.
  The tag-selection itself reads mathlib's `git ls-remote --tags`,
  keeps `v*.*` tags, parses them with the npm `semver` package, and
  compares them against the project's own `v*.*` git tags; with no
  project tags it targets `master`. Because its internal
  `lake update` edits only mathlib, running it on a project that
  also pins `cslib`/`doc-gen4` performs a cross-toolchain
  `lake update`; if that fails to resolve, the action calls
  `process.exit(1)` and emits nothing (no pull request, no issue).
- `do-update` downloads the precomputed `lean-toolchain` and
  `lake-manifest.json` for a tag, moves them into place, builds,
  and commits. Because it transports a mathlib-only manifest, it
  cannot bump other dependencies.

Both halves are mathlib-only by construction, so neither is used
here. The tag-selection algorithm (`git ls-remote --tags` + npm
`semver`) is reused; see
[Detect against our own pin](#detect-against-our-own-pin-not-the-actions-detector).

### lean-update

`leanprover-community/lean-update` is a composite action that does
not check out the repository; it operates on the caller's working
tree, runs `lake update` directly there (honouring prior lakefile
edits), builds and tests via `leanprover/lean-action`, and on
success opens a pull request, on failure opens an issue
(`on_update_succeeds` default `pr`, `on_update_fails` default
`issue`). `lake update` keeps a tag-pinned `rev` fixed (it records
the tag as `inputRev` and resolves it to a commit). For a project
that already has dependencies, `lean-update` does not run its
latest-version probe (gated on the manifest having zero packages
via `findDependencies.js`), so pre-pinned revisions are honoured
rather than advanced. It opens its pull request on a fixed branch,
`auto-update-lean/patch`.

### Survey of cslib downstreams

A survey of the public repositories that pin `cslib` (2026-05-30)
found no project that bumps mathlib and cslib together in CI. The
projects with bump automation (for example using
`mathlib-update-action` or the `downstream-reports` actions) bump
mathlib only; their action never touches a sibling dependency's
pinned `rev`. The de-facto convention among cslib downstreams that
hold matching versions (for example one such project pins both
mathlib and cslib to `v4.30.0-rc2`) is to pin `cslib` to the same
release tag as mathlib by hand, relying on cslib publishing tags on
the same `vX.Y.Z` cadence as the Lean toolchain. The matching tag
is a human-maintained convention, not a CI-enforced one. cslib's
own README endorses pinning a downstream to a release tag.

This design automates that convention rather than introducing a new
concept: the bump writes one target tag to all three `rev` fields.

## Design decisions

### Cadence: mathlib release tags

The bump targets mathlib release tags (release candidates and
stable releases), not arbitrary `master` commits. Release-tag
cadence gives the cleanest form of the version lock: at a release
tag, the locked dependencies were cut against a mathlib of the same
toolchain. Each mathlib release tag ships a matching distinct
toolchain (verified 2026-05-30: `mathlib4` at `v4.30.0-rc1`,
`v4.30.0-rc2`, `v4.31.0-rc1` carries `leanprover/lean4:v4.30.0-rc1`,
`...-rc2`, `...v4.31.0-rc1`).

### CSLib and doc-gen4 are version-locked to mathlib

`cslib` is treated as load-bearing from the outset and
version-locked to mathlib: it targets the same domain
(computer-science and programming-language mathematics) that this
project draws on mathlib for, so every addition is checked against
`cslib` to avoid reimplementing what it already provides. `cslib`
(`github.com/leanprover/cslib`) publishes a tag for each Lean
toolchain version, matching mathlib's tag string (`v4.31.0-rc1`
confirmed present). `doc-gen4` (`github.com/leanprover/doc-gen4`)
likewise publishes a matching tag and is required for documentation
generation. A bump moves all three to the same tag string in
lockstep.

### Detect against our own pin, not the action's detector

Detection compares the newest mathlib release tag against the
project's **current pinned `rev`** (read from `lakefile.toml`), not
against project `v*.*` version tags. This differs from
`mathlib-update-action`'s detector, which baselines against project
version tags and runs a mathlib-only `lake update` that would fail
against the locked `cslib`/`doc-gen4` pins. Baselining against the
pin removes that failure mode, removes the need for project version
tags (and therefore a self-tagging workflow), and removes the
circular bootstrapping that a version-tag baseline would require.
The tag enumeration and ordering reuse the action's steps
(`git ls-remote --tags` filtered to `v*.*`, ordered with the npm
`semver` package, using `semver.gt` for the newer-than comparison —
not `sort -V`, which misorders prereleases such as `v4.31.0-rc1`
against `v4.31.0`, and not `compareBuild`). The design omits the
action's `master` fallback and its project-version-tag baseline,
comparing against the pin instead; so no `master` candidate is
produced and no master-filtering is needed.

## End-state architecture

| Workflow | Purpose | Source |
| --- | --- | --- |
| `ci.yml` | build, test, lint, shake, axiom check | existing |
| `update.yml` | detect and apply bumps | self-detect + `lean-update` |
| `doc-build.yml` | documentation build | existing |

### Standing lakefile.toml change

Pin `mathlib` to a `rev` tag, uniform with `cslib` and `doc-gen4`
(`mathlib` currently has no `rev` and so tracks `master`). Baseline
revision: `v4.30.0-rc2`. After this change a bump is the
substitution of one tag string into three `rev` fields followed by
`lake update`.

Adding a `rev` does not change the declaration order: `mathlib`
remains the last `[[require]]`, so the cache-hash ordering
constraint documented in `lakefile.toml` is preserved. A tag `rev`
resolves to a commit (in `lake-manifest.json`, `inputRev` holds the
tag and `rev` the resolved commit), and `lake exe cache get` keys
on the commit, so the warm mathlib cache is still hit; this is
confirmed on the test repo.

### update.yml job 1: detect

A scheduled job (daily cron plus `workflow_dispatch`) runs a step
that:

1. Reads the current `mathlib` `rev` from the `[[require]]` block
   whose `name = "mathlib"` in `lakefile.toml` — a TOML-section-aware
   read keyed on the require name (as `mathlib-update-action`'s
   `modifyLakefileTOMLMathlibVersion` matches it), not a line
   `grep`, which would also match the `cslib`/`doc-gen4` `rev`
   fields.
2. Enumerates mathlib's `v*.*` tags via `git ls-remote --tags` and
   selects the newest by npm `semver` order.
3. Emits that tag as the target only if all of:
   1. it is `semver.gt` the current pin;
   2. the same tag exists on `cslib` and `doc-gen4` (each checked
      via `git ls-remote --tags`), so the lockstep substitution
      targets tags that have been published on all three repos; and
   3. no bump is already in flight for it: neither an open pull
      request on `auto-update-lean/patch` nor an open issue carrying
      `lean-update`'s failure label (both queried via `gh`).

   Otherwise it emits nothing.

Condition 2 prevents the tag-lag race: mathlib may cut a release
tag before `cslib`/`doc-gen4` cut theirs, and writing a
not-yet-published tag to their `rev` fields would make `lake update`
fail. Withholding the target until all three tags exist keeps the
apply job from ever attempting an unpublished tag. Condition 3 is
the re-run guard described next.

### update.yml job 2: apply with lockstep

When job 1 emits a target tag, the apply job:

1. Checks out the repository (`lean-update` does no checkout of its
   own).
2. Sets the `rev` of `mathlib`, `cslib`, and `doc-gen4` in
   `lakefile.toml` to the target tag.
3. Runs `lean-update` with `update_if_modified: lake-manifest.json`
   pinned explicitly. `lean-update` performs an in-tree
   `lake update` (regenerating `lake-manifest.json` and
   `lean-toolchain` against the edited revisions), builds and tests
   via `leanprover/lean-action`, and opens a pull request on
   success (`on_update_succeeds: pr`) or an issue on failure
   (`on_update_fails: issue`). The edited revisions are honoured
   (tag pins stay fixed; the latest-version probe is skipped for a
   project with dependencies).

The job needs `contents: write`, `pull-requests: write`, and
`issues: write`.

### Re-runs while a bump is in flight

The cron re-runs daily. While a bump is in flight, the pin on
`main` is unchanged, so detection would re-select the same target
tag. Two in-flight states must be guarded (condition 3 above):

- A pending pull request. `lean-update` uses a fixed branch
  (`auto-update-lean/patch`) and would force-update the open pull
  request in place, disrupting an in-progress review.
- A failed bump. `lean-update` opens an issue (deduped by label, so
  no duplicate issues accumulate), but with no pull request to gate
  on, the apply job would otherwise re-run `lake update` and a full
  build on every tick until the cause is resolved.

Detection therefore withholds the target while either an open pull
request on `auto-update-lean/patch` or an open issue with
`lean-update`'s failure label exists. The in-flight bump is left
untouched until a contributor merges the pull request, or resolves
and closes the issue.

### Validation and merge

`ci.yml` runs on the opened pull request and provides the full
build, test, lint, shake, and axiom-check gate (`ci.yml` triggers
on `pull_request` to `main`). A contributor reviews the diff
line-by-line and merges. No step merges automatically.

### Post-merge: rebase topics and regenerate integration

[docs/process.md](../../process.md) § Mathlib bump procedure
requires that a bump end with `main` updated, active topic branches
mass-rebased, and `integration` regenerated. After the bump pull
request merges to `main`, the maintainer runs
`scripts/rebase-topics.sh main` (mass-rebases active topic branches
onto the new `main`) and `scripts/regenerate-integration.sh`
(regenerates the `integration` fan-in view). These are manual
post-merge steps, not part of the workflow. The implementation
updates `docs/process.md` § Mathlib bump procedure, whose current
text describes `update.yml` as already opening pull requests (it
does not).

## Permissions and tokens

- "Allow GitHub Actions to create and approve pull requests" is
  enabled for the repository (granted 2026-05-30).
- The apply job opens pull requests and issues; with the repository
  setting above enabled, `GITHUB_TOKEN` suffices. If a later
  constraint requires it, substitute a dedicated token secret.

## Non-goals

- Tracking mathlib `master` continuously (the `downstream-reports`
  LKG/FKB model that cslib itself uses). The chosen cadence is
  release tags; master tracking is deferred.
- Self-tagging the repository with `lean-release-tag` /
  `create-release.yml`. The template uses project version tags as
  its detector baseline; this design baselines against the pin
  instead, so no self-tagging is needed. Publishing versioned
  releases could be adopted separately later, decoupled from the
  bump; if so, the workflow watches `main` only (not `integration`,
  which `scripts/regenerate-integration.sh` force-pushes).
- Floating `cslib` to `main` (the only no-lockstep alternative). It
  is inconsistent with release-tag cadence: cslib `main` tracks
  mathlib master, so it would run ahead of a pinned-release mathlib.
- Automatic merging of bump pull requests.
- Bumping `doc-gen4` on a separate cadence; all three move together.
- Changes to `check-axioms.sh`, the doctoc invocation, or CI path
  triggers (separate concern; tracked for a later branch).

## Open questions to resolve during planning

1. Whether `cslib` at a given release tag is API-consistent with
   mathlib at the same release tag once a `Geb` module imports
   `Cslib.…`. The matching tag string (`v4.31.0-rc1` on both) is a
   naming convention, not a guarantee that `cslib` was built
   against the mathlib commit the mathlib tag names: each dependency
   is a top-level requirement, so the project's mathlib pin
   overrides `cslib`'s transitive mathlib pin. Verification item 4
   is the real check.
2. Whether to retain a non-blocking `master` canary as a separate
   job (default: no; release tags only).

## Verification

Per the project's test-repo-first discipline, validate on a
numbered test repository before landing the workflow here:

1. A `v4.30.0-rc2` to `v4.31.0-rc1` lockstep bump regenerates the
   manifest and toolchain, hits the warm mathlib cache, and produces
   a green build and a pull request.
2. Detection emits the newest release tag only when it is
   `semver.gt` the pinned `rev` and that tag also exists on `cslib`
   and `doc-gen4`; it emits nothing when the pin is current, and
   nothing when mathlib has cut a tag the siblings have not (the
   tag-lag gate).
3. A failing build (a deliberately incompatible tag present on all
   three repos) opens an issue rather than a pull request; and a
   later cron tick does not re-run the apply job while that issue —
   or an open bump pull request — remains in flight.
4. A module importing `Cslib.…` builds against the lockstep-bumped
   pair (open question 1).

## References

- [docs/process.md](../../process.md) § Mathlib bump procedure
  — the procedure this spec updates.
- [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  — commit-message, pre-push, and action-pinning conventions.
- [AGENTS.md](../../../AGENTS.md) — agent push and review rules.
- `scripts/rebase-topics.sh`, `scripts/regenerate-integration.sh`
  — post-merge mass-rebase and integration regeneration.
- `https://github.com/leanprover-community/mathlib-update-action/blob/main/src/index.js`
  — detection/tag-selection logic (reused) and `do-update`
  (mathlib-only apply, not used).
- `https://github.com/leanprover-community/lean-update/blob/main/action.yml`
  — in-tree update action used for apply.
- `https://github.com/leanprover/cslib` — README downstream-pinning
  guidance; `.github/workflows/lake-update.yml` (downstream-reports
  bump) and `release.yml` (evidence of cslib's release-tag cadence,
  which the lockstep relies on).
