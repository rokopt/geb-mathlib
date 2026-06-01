# Bump pull request CI via self-dispatch — Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure](#file-structure)
- [Task 1: Dispatch CI on the bump branch from update.yml](#task-1-dispatch-ci-on-the-bump-branch-from-updateyml)
- [Task 2: Document the self-dispatch in process.md](#task-2-document-the-self-dispatch-in-processmd)
- [Task 3: Verify on the live repository](#task-3-verify-on-the-live-repository)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the automated mathlib-bump pull request carry visible
`ci.yml` checks for the reviewer, by having `update.yml`'s apply job
dispatch `ci.yml` on the bump branch after `lean-update` opens the
pull request.

**Architecture:** `lean-update` opens the bump PR under
`GITHUB_TOKEN`, whose events do not trigger workflow runs. Add a
final step to the apply job that runs `gh workflow run ci.yml --ref
auto-update-lean/patch` (guarded on an open PR existing);
`workflow_dispatch` is exempt from the suppression, so `ci.yml` runs
on the bump branch and its check-runs show on the PR. Adds
`actions: write` to the apply job. No App, PAT, or secret;
`lean-update` and `ci.yml` are unchanged.

**Tech Stack:** GitHub Actions (`workflow_dispatch`), `gh` CLI,
`jj`.

**Working branch:** `fix/bump-pr-ci` (off `main`; already carries
the design spec). Continue committing there.

**Commit convention:** This repo uses `jj`, not raw mutating `git`
(a PreToolUse hook blocks the latter). Each commit step is
`jj commit -m "<msg>"` then
`jj bookmark set fix/bump-pr-ci -r @-`. All commit messages end with
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`,
omitted below for brevity.

**Reference:** design spec at
[docs/superpowers/specs/2026-06-01-bump-pr-ci-design.md](../specs/2026-06-01-bump-pr-ci-design.md).

---

## File structure

- `.github/workflows/update.yml` (modify) — add `actions: write` to
  the `apply` job and a final CI-dispatch step.
- `docs/process.md` (modify) — one sentence in § Mathlib bump
  procedure noting the self-dispatch.

---

## Task 1: Dispatch CI on the bump branch from update.yml

**Files:**

- Modify: `.github/workflows/update.yml` (the `apply` job)

- [ ] **Step 1: Add `actions: write` to the apply job's permissions**

In `.github/workflows/update.yml`, the `apply` job's permissions
currently read:

```yaml
    permissions:
      contents: write
      pull-requests: write
      issues: write
```

Change to (add the one line; keep the others — `lean-update` still
creates the branch, PR, and failure issue with `GITHUB_TOKEN`):

```yaml
    permissions:
      contents: write
      pull-requests: write
      issues: write
      actions: write
```

- [ ] **Step 2: Append the CI-dispatch step after the lean-update step**

The `apply` job's last step is currently:

```yaml
      - name: lean-update (lake update, build, PR or issue)
        uses: leanprover-community/lean-update@926dc957637414948c317588eb14899cddf1fe11  # v0.7.0
        with:
          on_update_succeeds: pr
          on_update_fails: issue
          update_if_modified: lake-manifest.json
```

Add a new step immediately after it (same indentation):

```yaml
      - name: Trigger CI on the bump pull request
        run: |
          if [ "$(gh pr list --head auto-update-lean/patch \
                  --state open --json number --jq 'length')" != "0" ]; then
            gh workflow run ci.yml --ref auto-update-lean/patch
          fi
        env:
          GH_TOKEN: ${{ github.token }}
```

This dispatches `ci.yml` only when an open PR exists on the bump
branch (so it no-ops on the failure-issue path and any no-PR path).
`workflow_dispatch` is exempt from the `GITHUB_TOKEN` trigger
suppression, so the dispatched run's check-runs attach to the bump
branch head and appear on the PR.

- [ ] **Step 3: Validate the YAML**

Run: `npx --yes js-yaml .github/workflows/update.yml >/dev/null && echo "YAML OK"`
Expected: `YAML OK`.

- [ ] **Step 4: Confirm the guard command is well-formed**

Run (read-only; needs a token — use `GH_TOKEN=$(gh auth token)` if
not already authenticated):

```bash
gh pr list --head auto-update-lean/patch --state open --json number --jq 'length'
```

Expected: a non-negative integer (`0` if no bump PR is open). This
confirms the `gh` invocation in the step is valid; it does not test
the dispatch (that is Task 3, live).

- [ ] **Step 5: Commit**

```bash
jj commit -m "ci: dispatch ci.yml on the bump PR branch (workflow_dispatch)

lean-update opens the bump PR with GITHUB_TOKEN, whose events do not
trigger workflow runs, so the PR got no CI. workflow_dispatch is
exempt from that suppression: after lean-update opens the PR, the
apply job dispatches ci.yml on auto-update-lean/patch (guarded on an
open PR existing), putting visible CI check-runs on the PR. Adds
actions: write; no App/PAT/secret."
jj bookmark set fix/bump-pr-ci -r @-
```

---

## Task 2: Document the self-dispatch in process.md

**Files:**

- Modify: `docs/process.md` (the `## Mathlib bump procedure` section)

- [ ] **Step 1: Insert the operational sentence**

In `docs/process.md` § Mathlib bump procedure, find the sentence
ending `…opens a pull request on success or an issue on failure;
nothing merges automatically.` Immediately after it (same
paragraph), insert:

```text
The bump pull request is created with `GITHUB_TOKEN`, whose events
do not trigger workflow runs, so the apply job dispatches `ci.yml`
on the bump branch (`workflow_dispatch`, which is exempt from that
suppression) to put visible CI checks on the pull request for the
reviewer.
```

- [ ] **Step 2: Regenerate the TOC and lint**

Run:

```bash
doctoc --update-only docs/process.md
markdownlint-cli2 docs/process.md
```

Expected: doctoc `Everything is OK` (the heading is unchanged, so
the TOC does not change); markdownlint `0 error(s)` for
`docs/process.md`.

- [ ] **Step 3: Commit**

```bash
jj commit -m "doc: note the bump-PR CI self-dispatch in process.md

Record that the bump PR is GITHUB_TOKEN-created (so a native
pull_request CI run is suppressed) and the apply job dispatches
ci.yml on the bump branch to put visible CI checks on the PR."
jj bookmark set fix/bump-pr-ci -r @-
```

---

## Task 3: Verify on the live repository

This is a bug-fix verified directly on the live repo. Several steps
need the user (push authorization, PR authoring, merge) per the
no-push-without-review rule; the agent pauses at those.

- [ ] **Step 1: Push the fix branch and open its PR (user-gated)**

Run `scripts/pre-push.sh` (normalize `.remember` first if its
markdownlint check flags the live buffer), have the user review the
diff line-by-line, then push `fix/bump-pr-ci` and let the user
author and open its PR against `main`.

- [ ] **Step 2: Merge the fix PR to `main`**

The user merges the fix PR. After merge, run
`scripts/rebase-topics.sh main` (no-op if no other topic branches)
and `scripts/regenerate-integration.sh`.

- [ ] **Step 3: Close PR #7 without merging**

Close PR #7 (the pre-Option-D bump PR) without merging, so `main`
stays on `v4.30.0-rc2` (keeping the `v4.31.0-rc1` bump available)
and the `detect` in-flight guard does not block. Optionally delete
the `auto-update-lean/patch` branch for a clean re-create:

```bash
gh pr close 7 --delete-branch
```

- [ ] **Step 4: Re-dispatch the bump on `main`**

Run:

```bash
gh workflow run "Mathlib bump" --ref main
gh run watch "$(gh run list --workflow='Mathlib bump' --limit 1 --json databaseId --jq '.[0].databaseId')" --exit-status
```

Expected: `detect` emits `target=v4.31.0-rc1`; `apply` sets the
three revs, runs `lean-update` (opens a new bump PR), and the new
`Trigger CI` step dispatches `ci.yml` on `auto-update-lean/patch`.

- [ ] **Step 5: Confirm CI now appears on the new bump PR automatically**

Run:

```bash
NEWPR=$(gh pr list --head auto-update-lean/patch --state open --json number --jq '.[0].number')
gh pr view "$NEWPR" --json number,title
gh api "repos/rokopt/geb-mathlib/commits/$(gh pr view "$NEWPR" --json headRefOid --jq .headRefOid)/check-runs" --jq '.total_count'
```

Expected: a new bump PR exists; the check-runs total is non-zero
(the `ci.yml` jobs, dispatched automatically — no manual step), and
they go green. This is the spec's Verification item 2.

- [ ] **Step 6: Confirm the failure-path guard (inspection)**

Confirm by reading the dispatch step that, had `lean-update` opened
an `auto-update-lean-fail` issue instead of a PR, `gh pr list` would
return `0` and the step would dispatch nothing. (No code to run; the
spec's Verification item 3 is satisfied by the guard's structure,
exercised whenever a bump build fails.)

- [ ] **Step 7: Merge the new bump PR (user-gated)**

The user reviews the new bump PR (now with visible CI checks) and
merges it — the actual `v4.31.0-rc1` bump. After merge, run
`scripts/rebase-topics.sh main` and `scripts/regenerate-integration.sh`.
