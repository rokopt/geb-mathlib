# Bump pull request CI via self-dispatch

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [Design](#design)
  - [update.yml apply job](#updateyml-apply-job)
  - [docs/process.md](#docsprocessmd)
- [Non-goals](#non-goals)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc -->

## Goal

Make the automated mathlib-bump pull request carry `ci.yml` checks
(so a reviewer can gate it before merge), by having the bump
workflow dispatch `ci.yml` on the bump branch after opening the
pull request.

## Motivation

Live verification (run `26762939122`, PR #7) confirmed the bump
pipeline opens a correct lockstep pull request but with **no
`ci.yml` checks**: `lean-update` opens the pull request using
`GITHUB_TOKEN`, and "events triggered by the `GITHUB_TOKEN` will not
create a new workflow run" (GitHub docs), so `ci.yml`'s
`pull_request` trigger does not fire.

An earlier design routed a GitHub App token through `lean-update`'s
`token` input. Adversarial review found `lean-update` never passes
that input to its pull-request step (`peter-evans/create-pull-request`
runs with the default `github.token`); the `token` input reaches
only the failure-issue path. So no token — App or PAT — can change
who creates the pull request while `lean-update` creates it. That
design was inert and is abandoned.

The `GITHUB_TOKEN` suppression has documented exceptions:
`workflow_dispatch` and `repository_dispatch` always create a run.
A `workflow_dispatch` of `ci.yml` — even authenticated with
`GITHUB_TOKEN` — therefore does create a run, and its check runs
attach to the dispatched ref's head commit, so they appear on the
pull request. This was confirmed manually: a `workflow_dispatch` of
`ci.yml` on `auto-update-lean/patch` produced checks on PR #7. This
design automates that dispatch from inside the bump workflow.

## Design

### update.yml apply job

After the `lean-update` step, add a step that dispatches `ci.yml`
on the bump branch when a pull request was opened:

```yaml
- name: Trigger CI on the bump pull request
  run: |
    if [ "$(gh pr list --head auto-update-lean/patch --state open \
            --json number --jq 'length')" != "0" ]; then
      gh workflow run ci.yml --ref auto-update-lean/patch
    fi
  env:
    GH_TOKEN: ${{ github.token }}
```

- The inner `gh pr list` check is the gate: it dispatches `ci.yml`
  only when an open pull request exists on `auto-update-lean/patch`.
  On the failure path `lean-update` opens an `auto-update-lean-fail`
  issue and no pull request, so no CI is dispatched. `lean-update`
  exits 0 in both the PR and issue cases, so this step runs after
  it; the check, not the step condition, distinguishes them.
- Add `actions: write` to the apply job's `permissions` (the
  `workflow_dispatch` REST API the `gh workflow run` call uses
  requires it). The existing `contents: write`,
  `pull-requests: write`, `issues: write` stay — `lean-update`
  still creates the branch, pull request, and failure issue with
  `GITHUB_TOKEN`, which needs those. (The abandoned App-token design
  proposed reducing these to `contents: read`; that is wrong here
  and is not done.)
- `ci.yml` already has a `workflow_dispatch` trigger; no change to
  `ci.yml` is needed. The dispatched run checks out
  `auto-update-lean/patch` and runs the full gate (build, test,
  lint, shake, axiom check, markdownlint) on the bumped state.

The `detect` job is unchanged. `lean-update` is unchanged (it still
opens the pull request under `GITHUB_TOKEN`); CI is fired
separately rather than by changing who opens the pull request.

### docs/process.md

Add to § Mathlib bump procedure: the bump pull request is
`GITHUB_TOKEN`-created, so a native `pull_request` CI run is
suppressed; the apply job dispatches `ci.yml` on the bump branch
(`workflow_dispatch`, which is exempt from that suppression) so the
pull request carries the full CI gate for the reviewer.

## Non-goals

- A GitHub App token or personal access token (the earlier design;
  abandoned — `lean-update` routes no token to its pull-request
  step, and self-dispatch needs no special identity or secret).
- Opening the pull request ourselves with
  `peter-evans/create-pull-request` (unnecessary given
  self-dispatch).
- Auto-merging bump pull requests (a contributor still reviews and
  merges).
- Any change to detection, the lockstep substitution, the in-flight
  guards, or `ci.yml`.

## Verification

This is a bug-fix applied to the live repository. PR #7 is already
gated by a manual `ci.yml` dispatch and can be merged independently
of this fix.

1. Merge the fix to `main`.
2. Re-dispatch `update.yml` on `main`; confirm the apply job's
   dispatch step fires `ci.yml` on `auto-update-lean/patch`, and
   that the resulting bump pull request shows `ci.yml` checks
   (running, then green) without any manual step.
3. Confirm the failure path does not dispatch: when no open pull
   request exists on the bump branch (for example after a failing
   bump that opened an issue instead), the step runs `gh pr list`,
   finds none, and dispatches nothing.

## References

- GitHub docs, "Trigger a workflow" —
  `https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow`
  (events triggered by `GITHUB_TOKEN` do not create new workflow
  runs, except `workflow_dispatch` and `repository_dispatch`).
- `https://docs.github.com/en/rest/actions/workflows#create-a-workflow-dispatch-event`
  (the `workflow_dispatch` API requires `actions: write`).
- `.github/workflows/ci.yml` — already exposes `workflow_dispatch`.
- [docs/process.md](../../process.md) § Mathlib bump procedure.
- [docs/superpowers/plans/2026-05-30-mathlib-bump-process-plan.md](../plans/2026-05-30-mathlib-bump-process-plan.md)
  — the pipeline this fixes.
