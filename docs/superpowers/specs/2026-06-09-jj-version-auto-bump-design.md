# jj-version auto-bump: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Problem](#problem)
- [Goal](#goal)
- [Decisions](#decisions)
- [Components](#components)
  - [Workflow: `.github/workflows/jj-bump.yml`](#workflow-githubworkflowsjj-bumpyml)
  - [Detect script: `scripts/jj-bump-detect.sh`](#detect-script-scriptsjj-bump-detectsh)
  - [Shared helper rename: `scripts/lib/select-newest-tag.cjs`](#shared-helper-rename-scriptslibselect-newest-tagcjs)
  - [Test: `scripts/tests/test-jj-bump-detect.sh`](#test-scriptsteststest-jj-bump-detectsh)
  - [One-time setup](#one-time-setup)
- [Data flow](#data-flow)
- [Out of scope](#out-of-scope)
- [Completion](#completion)

<!-- END doctoc -->

Status: validated design (brainstorming phase). Transient process
artifact: removed in the final commits of this topic branch per
CONTRIBUTING.md § Concern shape.

## Problem

`scripts/jj-version` pins the jj release installed in CI
(`scripts/install-jj.sh`, used by `ci.yml` and
`regenerate-integration.yml`). The pin is bumped by hand.
Dependabot does not cover release-binary version pins, so the pin
lags upstream releases until a contributor notices.

## Goal

A scheduled workflow that detects a newer `jj-vcs/jj` release,
verifies it against this repository's jj-dependent scripts, and
opens a pull request bumping `scripts/jj-version`. The shape
mirrors `.github/workflows/update.yml` (the mathlib bump): a
read-only detect job feeding a write-permissioned apply job.

## Decisions

The following were settled during brainstorming:

- **Verification depth**: before opening the PR, the apply job
  runs `scripts/install-jj.sh` (proves the release asset exists
  and installs) and `scripts/tests/test-regenerate-integration.sh`
  (exercises the conflict-guard logic against the new binary).
- **Failure mode**: a failed apply step opens an issue labelled
  `jj-bump-fail`; the in-flight guard treats that open issue as a
  bump in flight, suppressing retries until a human closes it.
- **Cadence**: weekly cron plus `workflow_dispatch`. jj releases
  roughly monthly; weekly matches the dependabot interval used for
  the other CI-tooling pins.
- **PR mechanism**: `peter-evans/create-pull-request`, pinned to a
  commit SHA per the action-pinning policy
  (`docs/rules/ci-and-workflow.md`) and thereafter maintained by
  dependabot. It handles branch creation, commit, push, and PR
  open/update idempotently on a fixed branch name.

## Components

### Workflow: `.github/workflows/jj-bump.yml`

Two jobs, mirroring `update.yml`:

- Triggers: weekly `schedule` cron (`0 17 * * 1`, Mondays at the
  same hour as `update.yml`'s daily run) and `workflow_dispatch`.
- Concurrency group `jj-bump`, `cancel-in-progress: false`.
- **detect**: read-only permissions (`contents: read`,
  `pull-requests: read`, `issues: read`). Runs
  `scripts/jj-bump-detect.sh`; exposes its `target` output.
- **apply**: gated on `needs.detect.outputs.target != ''`; write
  permissions (`contents: write`, `pull-requests: write`,
  `issues: write`, `actions: write`). Steps:

  1. Write the target version to `scripts/jj-version`.
  2. `bash scripts/install-jj.sh` — the asset downloads,
     extracts, installs, and reports the expected version.
  3. `bash scripts/tests/test-regenerate-integration.sh` — the
     regeneration guard behaves correctly under the new binary.
  4. `peter-evans/create-pull-request`: branch
     `auto-update-jj/patch`, commit message
     `ci: bump jj to <version>`, machine-templated PR title and
     body.
  5. `gh workflow run ci.yml --ref auto-update-jj/patch` when the
     PR exists — pull requests created with `GITHUB_TOKEN` do not
     trigger `pull_request` workflows on their own (same idiom as
     `update.yml`).
  6. On failure of any prior step (`if: failure()`): open an
     issue labelled `jj-bump-fail` naming the target version.

### Detect script: `scripts/jj-bump-detect.sh`

Mirrors `scripts/mathlib-bump-detect.sh` in structure and idiom.
Writes `target=<version>` (empty when no bump proceeds) to stdout
and, when set, to `$GITHUB_OUTPUT`. A version is emitted only when
all of the following hold:

1. The latest release is semver-greater than the pin read from
   `scripts/jj-version`. The latest release comes from
   `gh api repos/jj-vcs/jj/releases/latest`, which excludes drafts
   and prereleases server-side, so no tag-list filtering is
   needed. The comparison reuses the shared semver helper as a
   guard against the endpoint returning an older release (e.g.
   after a yanked release).
2. The release's asset list (in the same API response) contains
   `jj-v<version>-x86_64-unknown-linux-musl.tar.gz` — the asset
   `scripts/install-jj.sh` downloads. A published tag whose
   binaries are still uploading (or whose asset naming changed)
   emits empty and waits for the next run. This is the jj
   analogue of the mathlib script's lockstep tag-lag gate: same
   emit-empty-and-wait idiom, different transient predicate.
3. No bump is in flight: no open PR with head
   `auto-update-jj/patch` and no open issue labelled
   `jj-bump-fail`.

Failure idioms carried over from `mathlib-bump-detect.sh`:

- **Fail loudly**: an API failure, empty response, or selector
  error exits 1; an outage is never reported as "already
  current".
- **Fail closed**: the in-flight check treats a `gh` failure or
  non-numeric count as an error (exit 1), never as "not in
  flight", so a transient outage cannot clobber an open,
  under-review pull request.

### Shared helper rename: `scripts/lib/select-newest-tag.cjs`

`scripts/lib/select-newest-mathlib-tag.cjs` contains no
mathlib-specific logic (newline-separated candidate tags on stdin,
pin in argv, newest strictly-greater tag on stdout). It is renamed
to `scripts/lib/select-newest-tag.cjs`; `mathlib-bump-detect.sh`,
`test-mathlib-bump-detect.sh`, and the helper's header comment
update their references. The alternative — a second copy or a
misleading name — fails the reuse rule.

### Test: `scripts/tests/test-jj-bump-detect.sh`

Mirrors `scripts/tests/test-mathlib-bump-detect.sh`: sources the
guarded detect script and exercises its pure logic — pin read,
version selection, and the asset-presence predicate fed canned
release JSON. Network-bound wrappers are covered by a live
`workflow_dispatch` run, not by the unit test. Wired into
`scripts/pre-push.sh` and CI alongside the existing script tests.

### One-time setup

The `jj-bump-fail` label is created once during implementation
(`gh label create`); `gh issue create --label` fails on a
nonexistent label.

## Data flow

```text
cron / dispatch
  └─ detect (read-only)
       └─ jj-bump-detect.sh ──► target=<version | empty>
            └─ apply (write; only when target nonempty)
                 ├─ pin edit ► install-jj.sh ► guard test
                 ├─ create-pull-request ► auto-update-jj/patch
                 ├─ gh workflow run ci.yml (on the PR branch)
                 └─ on failure: issue labelled jj-bump-fail
```

## Out of scope

- Bumping jj on contributor machines (the pin governs CI only;
  `CONTRIBUTING.md` § Setup leaves local installs to the
  contributor's package manager).
- Auto-merge. The bump PR is reviewed and merged by a
  contributor; CONTRIBUTING.md's review rules apply unchanged.
- Platforms other than x86_64 Linux (the scope of
  `scripts/install-jj.sh`).

## Completion

- `TODO.md`'s "Next up" entry for this workstream is removed in
  the implementation commits.
- This spec and its plan are removed in the final commits of the
  topic branch per CONTRIBUTING.md § Concern shape.
