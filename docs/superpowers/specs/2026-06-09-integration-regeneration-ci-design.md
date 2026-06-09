# CI integration regeneration and conflict detection

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Context](#context)
- [Goals](#goals)
- [Non-goals](#non-goals)
- [Trigger and rationale](#trigger-and-rationale)
- [Workflow: regenerate-integration.yml](#workflow-regenerate-integrationyml)
- [Script hardening: conflicts() guard](#script-hardening-conflicts-guard)
- [Conflict surfaces](#conflict-surfaces)
- [jj version tracking](#jj-version-tracking)
- [Permissions, concurrency, and preconditions](#permissions-concurrency-and-preconditions)
- [References](#references)

<!-- END doctoc -->

## Context

`scripts/regenerate-integration.sh` rebuilds the `integration`
bookmark as a `jj` fan-in merge of `main` plus the tips of every
active topic branch (the bookmark globs in
`scripts/lib/topic-revset.sh`). At present the script runs only by
manual invocation. Conflicts between active developments —
textual merge conflicts or semantic breakage that fails the build
— surface only when a contributor regenerates `integration` by
hand.

`.github/workflows/conflict-check.yml` already gates committed
content: it rejects `.jjconflict-*` directories and column-zero
git merge markers on every push and pull request. It does not
construct the fan-in, so it cannot detect a conflict between two
branches that nobody has yet combined.

This spec adds CI that regenerates the fan-in automatically and
makes both conflict classes visible through ordinary check
status.

## Goals

- Detect conflicts that a merge to `main` introduces against
  active topic branches — textual and build-level — without
  manual fan-in regeneration.
- Tie detection to the event that makes a conflict binding on
  active branches: a merge to `main`.
- Reuse existing machinery (the regeneration script, the existing
  `ci.yml` build, the cron-bump-PR shape from `update.yml`) rather
  than duplicating it.
- Keep `integration` a regenerated view only; never let a fan-in
  failure affect `main`.

## Non-goals

- No periodic (cron) regeneration. A scheduled fan-in would flag
  conflicts in exploratory branches that no merge to `main` has
  yet made binding.
- No tracking issue, pull request, or other notification surface
  beyond check status (see Conflict surfaces).
- No second build implementation inside the new workflow; the
  build signal is the existing `ci.yml` running on `integration`.
- No automatic maintenance of the `jj` pin. This branch bumps
  `scripts/jj-version` by hand; a cron-bump-PR pipeline is a
  separate concern (see jj version tracking).
- No change to how `main` is produced or reviewed.

## Trigger and rationale

The regeneration workflow runs on `push` to `main` and on
`workflow_dispatch`. A merge to `main` is the point at which any
conflict it introduces with an active branch becomes binding:
that branch must resolve the conflict before it can land. A push
to `main` therefore both warrants and bounds the check. The
workflow does not fire on topic-branch pushes, so a conflict
introduced solely by a new or updated topic branch is surfaced to
that branch's author when they next rebase onto `main`, not here;
that asymmetry is deliberate, since exploratory topic work should
not raise a conflict signal before a `main` merge makes it
binding.

Publishing `integration` is a reasoned exception to the standing
"no `jj git push` without line-by-line review" rule. The exception
rests on trunk isolation: `integration` is never used to rebase
`main`, so a defective or conflicted fan-in cannot reach the
trunk. The fan-in also introduces no new public content — its
parents are `main` and topic-branch tips already pushed to
`origin` — so publishing it only combines existing public
commits.

## Workflow: regenerate-integration.yml

```yaml
on:
  push:
    branches: [main]
  workflow_dispatch:

concurrency:
  group: regenerate-integration
  cancel-in-progress: true

permissions:
  contents: write
  actions: write
```

Job steps:

1. `actions/checkout` with `fetch-depth: 0` (all branch tips are
   required for the fan-in), pinned by commit SHA per the
   action-pinning policy.
2. Install `jj` at the pinned version (read from
   `scripts/jj-version`, added by this branch) by direct download
   of the release binary (no setup action), then
   `jj git init --colocate` and set the commit identity to the
   Actions bot (`github-actions[bot]`), matching commits made
   under `GITHUB_TOKEN`.
3. Run `bash scripts/regenerate-integration.sh`. The script
   fetches, promotes the fetched remote bookmarks to local
   tracking bookmarks (so the topic-branch revset matches them; CI
   lacks the per-developer auto-track configuration), builds the
   fan-in, applies the conflict guard (below), and on a clean
   fan-in pushes `integration`.
4. A push made with the default `GITHUB_TOKEN` does not re-trigger
   other workflows, so the workflow then runs
   `gh workflow run ci.yml --ref integration` to obtain the build
   signal on the combined tree — the same explicit-trigger pattern
   `update.yml` uses for the bump pull request.

Regeneration is unconditional: the workflow does not short-circuit
when no topic branch is active. In that case the fan-in resolves to
`main` alone, which still exercises the mechanism end to end and
keeps `integration` current with `main`. Each `main` push
therefore force-pushes a fresh `integration` and dispatches a full
`ci.yml` run, including on pushes that do not change the fan-in
tree; this CI cost is accepted as the price of continuous
validation.

## Script hardening: conflicts() guard

`jj new $parents` succeeds on a textual conflict, recording the
conflict in the commit rather than failing. CI does not carry the
local `git.private-commits = 'conflicts()'` configuration that
would make the subsequent push refuse. Without a guard the script
would publish a conflicted `integration`.

`scripts/regenerate-integration.sh` gains an explicit check
immediately after the fan-in `jj new $parents` and before
`jj bookmark set integration` — the only window in which `@` is the
fan-in, so the `@`-scoping is valid:

```bash
# After the fan-in `jj new`, @ is the candidate integration commit;
# scope to @ so an unrelated conflicted commit cannot trip the guard.
if [ -n "$(jj log -r 'conflicts() & @' --no-graph \
            -T 'commit_id ++ "\n"')" ]; then
  echo "::error::fan-in has textual conflicts; not publishing" >&2
  jj resolve --list || true
  exit 1
fi
```

The guard also protects manual runs of the script, independent of
CI. The published `integration` is therefore always textually
clean.

## Conflict surfaces

The two conflict classes surface on two different check-status
surfaces, consistent with the minimal-notification decision
(branch status only, no tracking issue). Neither surface actively
notifies the topic-branch author who must resolve the conflict;
that author discovers it by watching these checks or when they next
rebase onto `main`. This is the accepted cost of the minimal
posture.

- Textual conflict: the guard fails the regeneration job before
  the bookmark is moved or pushed, so `integration` does not move.
  Because the job is triggered by the `push` to `main`, the failed
  check is recorded against that `main` commit (visible to anyone
  viewing `main`'s checks), though it does not name the conflicting
  topic branch. A failed regeneration check on `main` means either
  a textual conflict or an operational error (fetch, push, or the
  `ci.yml` dispatch); only the conflict path emits the
  `::error::fan-in has textual conflicts` annotation, so the job
  log distinguishes them.
- Semantic or build conflict: the fan-in is textually clean and is
  pushed; the dispatched `ci.yml` runs the full suite on the
  combined tree, and a failure shows as a red `integration` build.
  This signal is observable only through the `integration` branch's
  run history (the Actions tab filtered to that branch), not as a
  check on any `main` commit, and it sits on a fan-in commit that
  the next regeneration orphans and force-pushes away — so a given
  fan-in's status is short-lived. The dispatch also targets the
  moving `integration` ref, so under back-to-back `main` pushes the
  signal is best-effort: concurrency may cancel or supersede a
  build, and a regeneration whose guard fails (no push) can leave
  the live `integration` without a fresh build status. The next
  `main` push regenerates and rebuilds, so a missed signal is
  transient. This limited, transient visibility is the deliberate
  cost of the minimal-notification posture; a durable surface (a
  tracking issue) was considered and declined.

## jj version tracking

This branch establishes the `jj` version pin as a tracked file
(`scripts/jj-version`) read by the workflow, and bumps it by hand.
Keeping the pin current automatically is a separate concern: a
scheduled cron-bump-PR workflow mirroring `update.yml`, recorded
in `TODO.md`. Dependabot is not used for it — its ecosystems are
package manifests, and a release-binary version pin is not among
them.

## Permissions, concurrency, and preconditions

- `contents: write` to push `integration`; `actions: write` is the
  documented minimum for dispatching `ci.yml` via
  `gh workflow run`. The regeneration job runs only repository
  scripts and `jj` merge/push operations; it does not build or
  execute fan-in content, so the write tokens are not exposed to
  unreviewed topic-branch code. The build that does execute the
  combined tree runs under `ci.yml`'s default read-only token.
- `concurrency.group: regenerate-integration` with
  `cancel-in-progress: true`: the latest `main` supersedes any
  in-flight regeneration, and a superseded run is cancelled before
  it can post a misleading status.
- `timeout-minutes: 15` bounds the job — sufficient for a full
  fetch, the fan-in, and a single push, none of which build — so a
  hung fetch or push cannot consume the default six-hour ceiling.
- `ci.yml` must retain its `workflow_dispatch` trigger: the build
  signal reaches `integration` only through the explicit dispatch,
  because a `GITHUB_TOKEN` push to `integration` does not fire
  `ci.yml`'s `push` trigger.
- The no-re-trigger reasoning is specific to `GITHUB_TOKEN` pushes.
  No workflow pushes `main` directly — the bump pipeline opens a
  pull request — and the bot's `integration` push uses
  `GITHUB_TOKEN`, so regeneration neither re-enters itself nor
  cascades into other workflows.
- Precondition: `integration` branch protection must permit the
  Actions bot to force-push (no required reviews, no
  linear-history bar on the bot). The script force-pushes a
  sibling fan-in on every run; a protected `integration` would
  fail every regeneration with a permissions error unrelated to
  any conflict. Configure this before enabling the workflow.
- `conflict-check.yml` is `on: push: [integration]`, but a
  `GITHUB_TOKEN` push does not re-trigger workflows, so it does not
  run on the bot-pushed `integration`. The in-script `conflicts()`
  guard subsumes its committed-marker scan for the fan-in — no
  textual conflict is ever published — so the gate is not lost.

## References

- `scripts/regenerate-integration.sh` — fan-in regeneration.
- `scripts/lib/topic-revset.sh` — topic-branch bookmark globs.
- `.github/workflows/ci.yml` — build/test/lint/shake suite,
  triggered on `push` to `integration`.
- `.github/workflows/update.yml`,
  `scripts/mathlib-bump-detect.sh` — cron-bump-PR precedent and the
  explicit `gh workflow run` re-trigger pattern.
- `.github/workflows/conflict-check.yml` — committed-content
  conflict gate (distinct from fan-in construction).
