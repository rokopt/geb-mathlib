# Bump pull request CI via GitHub App token

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [Design](#design)
  - [update.yml apply job](#updateyml-apply-job)
  - [GitHub App (user-provisioned)](#github-app-user-provisioned)
  - [docs/process.md](#docsprocessmd)
- [Non-goals](#non-goals)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc -->

## Goal

Make the automated mathlib-bump pull request trigger `ci.yml`, by
opening it under a GitHub App installation token instead of the
default `GITHUB_TOKEN`.

## Motivation

Live verification (run `26762939122`, which opened PR #7) confirmed
the bump pipeline opens a correct lockstep pull request
(`mathlib`/`cslib`/`doc-gen4` all to `v4.31.0-rc1`, toolchain and
manifest regenerated) but with **no `ci.yml` checks**:
`gh run list --branch auto-update-lean/patch` is empty. The cause
is documented GitHub behavior — "When you use the repository's
`GITHUB_TOKEN` to perform tasks, events triggered by the
`GITHUB_TOKEN` will not create a new workflow run" (exceptions:
`workflow_dispatch`, `repository_dispatch`). `lean-update` opens the
PR using `GITHUB_TOKEN`, so `ci.yml`'s `pull_request` trigger never
fires. The documented workaround is a personal access token or a
GitHub App installation access token; `cslib`'s own
`lake-update.yml` uses the latter (via `actions/create-github-app-token`).

The bump itself is not unverified: `lean-update`'s apply-job build
ran against the bumped state and passed (which is why it opened a
PR, not an issue). What is missing is the fuller `ci.yml` gate
(build, test, lint, shake, axiom check, markdownlint) re-running on
the pull request for the reviewer. This fix restores that gate.

## Design

### update.yml apply job

- Add a step before `lean-update` that mints an installation token
  with `actions/create-github-app-token` (SHA-pinned per
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Action pinning policy), with inputs
  `app-id: ${{ secrets.BUMP_APP_ID }}` and
  `private-key: ${{ secrets.BUMP_APP_PRIVATE_KEY }}`.
- Pass that token to `lean-update`:
  `token: ${{ steps.app-token.outputs.token }}`. `lean-update` uses
  it to push the `auto-update-lean/patch` branch and open the pull
  request (or the `auto-update-lean-fail` issue), so those are
  created under the App identity and do trigger `ci.yml`.
- Reduce the apply job's `GITHUB_TOKEN` permissions to
  `contents: read`. The App token now carries the
  `contents`/`pull-requests`/`issues` writes; `GITHUB_TOKEN` is left
  with only what `actions/checkout` and `lean-action`'s mathlib
  cache fetch require (read).

The `detect` job is unchanged: its in-flight `gh pr list` /
`gh issue list` reads work with `github.token`, and it can see a
pull request or issue created under the App identity.

### GitHub App (user-provisioned)

The user creates a GitHub App, installs it on `rokopt/geb-mathlib`,
and stores its credentials as repository secrets. This is a
GitHub-account action outside the workflow:

- App repository permissions: `Contents: write`,
  `Pull requests: write`, `Issues: write`. No `workflows`
  permission — the bump never edits `.github/`.
- Secrets: `BUMP_APP_ID` (the App's numeric id) and
  `BUMP_APP_PRIVATE_KEY` (a generated private key).

### docs/process.md

Add one sentence to § Mathlib bump procedure: the bump pull request
is opened under the bump App (not `GITHUB_TOKEN`) so `ci.yml` runs
on it. The merged design spec is point-in-time and is not edited;
the live procedure carries the operational note.

## Non-goals

- A fine-grained personal access token (considered; the App was
  chosen for scoping, automatic rotation, bot attribution, and
  parity with `cslib`).
- Auto-merging bump pull requests (a contributor still reviews and
  merges).
- Any change to detection, the lockstep substitution, or the
  in-flight guards.

## Verification

This is a bug-fix applied to the live repository.

1. Merge the fix to `main`.
2. Re-dispatch `update.yml` on `main`; confirm the new bump pull
   request now shows `ci.yml` checks running and green (not "no
   checks reported"), and that the diff still bumps all three deps
   to the newest release tag.
3. Close PR #7 unmerged; review and merge the new, CI-gated bump
   pull request.

## References

- GitHub docs, "Trigger a workflow" —
  `https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow`
  (events triggered by `GITHUB_TOKEN` do not create new workflow
  runs; PAT or GitHub App token is the workaround).
- `https://github.com/actions/create-github-app-token` — the
  token-minting action.
- `https://github.com/leanprover/cslib/blob/main/.github/workflows/lake-update.yml`
  — App-token precedent in a sibling project.
- [docs/process.md](../../process.md) § Mathlib bump procedure.
- [docs/superpowers/plans/2026-05-30-mathlib-bump-process-plan.md](../plans/2026-05-30-mathlib-bump-process-plan.md)
  — the pipeline this fixes.
