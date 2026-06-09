# Integration regeneration CI Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** On every push to `main`, regenerate the `integration`
fan-in and surface textual and build-level conflicts among active
topic branches through ordinary CI check status.

**Architecture:** A `push: [main]` workflow installs a pinned `jj`,
runs a hardened `regenerate-integration.sh` that refuses to publish
a conflicted fan-in, force-pushes `integration`, and explicitly
dispatches `ci.yml` on `integration` (the `GITHUB_TOKEN` push does
not re-trigger workflows). The build/semantic-conflict signal is
the existing `ci.yml` running on the combined tree.

**Tech Stack:** GitHub Actions, `jj` (Jujutsu) v0.42.0, Bash,
`gh` CLI.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [VCS note (jj)](#vcs-note-jj)
- [File structure](#file-structure)
- [Task 1: Pin the jj version](#task-1-pin-the-jj-version)
- [Task 2: Add the jj installer](#task-2-add-the-jj-installer)
- [Task 3: Harden the regeneration script and test the guard](#task-3-harden-the-regeneration-script-and-test-the-guard)
- [Task 4: Add the regeneration workflow](#task-4-add-the-regeneration-workflow)
- [Task 5: Run the guard test in CI](#task-5-run-the-guard-test-in-ci)
- [Task 6: Run the guard test in the pre-push checklist](#task-6-run-the-guard-test-in-the-pre-push-checklist)
- [Task 7: Record the jj-version auto-bump follow-on](#task-7-record-the-jj-version-auto-bump-follow-on)
- [Task 8: Final verification and bookmark advance](#task-8-final-verification-and-bookmark-advance)
- [Deployment note](#deployment-note)
- [Self-review](#self-review)

<!-- END doctoc -->

## VCS note (jj)

This repository uses `jj`, not raw `git`. "Commit" means: with the
finished work in the working copy `@`, run
`jj describe -m "<message>"` then `jj new` to start the next
change. After the final task, advance the branch bookmark to the
tip with `jj bookmark set feat/integration-regeneration-ci -r @-`
before the pre-push review. Do not push; pushing is a separate,
user-reviewed step.

Commit messages follow the repository convention
(`docs/rules/ci-and-workflow.md`): `<type>(<scope>): <subject>`,
imperative, no trailing period.

The `shellcheck` and `doctoc` steps below require those tools on
PATH (`apt-get install -y shellcheck`; `npm install -g doctoc`).
Install them before executing the plan if they are absent.

## File structure

- `scripts/jj-version` (create) — single-line pinned `jj` version
  (no leading `v`), read by the installer.
- `scripts/install-jj.sh` (create) — download and install the
  pinned `jj` release binary on an x86_64 Linux runner. Shared by
  both workflows that need `jj`.
- `scripts/regenerate-integration.sh` (modify) — refactor into a
  sourceable form (`working_copy_has_conflicts` plus a guarded
  `main`), track fetched remote bookmarks locally, and refuse to
  publish a conflicted fan-in.
- `scripts/tests/test-regenerate-integration.sh` (create) — source
  the script and assert the conflict guard fires on a constructed
  conflicted fan-in and stays silent on a clean commit.
- `.github/workflows/regenerate-integration.yml` (create) — the
  `push: [main]` regeneration workflow.
- `.github/workflows/ci.yml` (modify) — add a job that installs
  `jj` and runs the guard test.
- `scripts/pre-push.sh` (modify) — add the guard test to the
  checklist.
- `TODO.md` (modify) — record the jj-version auto-bump follow-on
  concern.

---

## Task 1: Pin the jj version

**Files:**

- Create: `scripts/jj-version`

- [ ] **Step 1: Create the pin file**

`scripts/jj-version`:

```text
0.42.0
```

- [ ] **Step 2: Verify the pinned release asset exists**

Run:

```bash
V="$(cat scripts/jj-version)"
curl -fsSL -o /dev/null -w '%{http_code}\n' \
  "https://github.com/jj-vcs/jj/releases/download/v${V}/jj-v${V}-x86_64-unknown-linux-musl.tar.gz"
```

Expected: `200` (curl follows the GitHub release redirect to the
asset and reports the final status). A plain `-I`/`head -1` would
print the `302` redirect instead and is not a reliable check.

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci(integration): pin jj version for CI"
jj new
```

---

## Task 2: Add the jj installer

**Files:**

- Create: `scripts/install-jj.sh`

- [ ] **Step 1: Write the installer**

`scripts/install-jj.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/install-jj.sh
#
# Install the pinned `jj` release binary into /usr/local/bin for
# CI. The version is read from scripts/jj-version (no leading `v`);
# the GitHub release tag and asset name add the `v` prefix.
#
# Target is the GitHub Actions ubuntu-latest runner: x86_64 Linux.
# A different platform fails loudly rather than installing a
# mismatched binary.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
version="$(tr -d '[:space:]' < "$here/jj-version")"

if [ -z "$version" ]; then
  echo "install-jj: scripts/jj-version is empty" >&2
  exit 1
fi

arch="$(uname -m)"
kernel="$(uname -s)"
if [ "$arch" != "x86_64" ] || [ "$kernel" != "Linux" ]; then
  echo "install-jj: unsupported platform ${kernel}/${arch};" \
       "this installer targets x86_64 Linux runners" >&2
  exit 1
fi

asset="jj-v${version}-x86_64-unknown-linux-musl.tar.gz"
url="https://github.com/jj-vcs/jj/releases/download/v${version}/${asset}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "install-jj: downloading ${url}" >&2
curl -fsSL "$url" -o "$tmp/jj.tar.gz"
tar -xzf "$tmp/jj.tar.gz" -C "$tmp"
sudo install -m 0755 "$tmp/jj" /usr/local/bin/jj

installed="$(jj --version)"
case "$installed" in
  *"$version"*) echo "install-jj: installed ${installed}" >&2 ;;
  *)
    echo "install-jj: version mismatch: wanted ${version}," \
         "got '${installed}'" >&2
    exit 1
    ;;
esac
```

- [ ] **Step 2: Make it executable**

Run: `chmod +x scripts/install-jj.sh`

- [ ] **Step 3: Lint the script**

Run: `shellcheck -x scripts/install-jj.sh`
Expected: no output (exit 0).

- [ ] **Step 4: Commit**

```bash
jj describe -m "ci(integration): add pinned jj installer for CI"
jj new
```

---

## Task 3: Harden the regeneration script and test the guard

This task is test-driven: write the failing test, confirm it
fails, refactor the script, confirm it passes.

**Files:**

- Create: `scripts/tests/test-regenerate-integration.sh`
- Modify: `scripts/regenerate-integration.sh`

- [ ] **Step 1: Write the failing test**

`scripts/tests/test-regenerate-integration.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-regenerate-integration.sh
#
# Smoke test for scripts/regenerate-integration.sh. Sources the
# script (whose `main` is guarded) and exercises the pure conflict
# check `working_copy_has_conflicts` against constructed jj repos:
# a fan-in with a textual conflict (the guard must fire) and a
# clean commit (the guard must stay silent). The network IO
# (fetch, push, ci dispatch) is covered by the live workflow run,
# not here.
#
# Requires `jj` on PATH (the project's working VCS).

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/regenerate-integration.sh
source "$repo_root/scripts/regenerate-integration.sh"

failed=0
checked=0

assert() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [ "$actual" != "$expected" ]; then
    echo "FAIL: $name: expected [$expected], got [$actual]" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

jj git init "$work/repo" >/dev/null 2>&1
jjr() {
  jj -R "$work/repo" \
     --config user.name=test \
     --config user.email=test@example.invalid "$@"
}

# Two children of `base` edit the same line differently; their
# fan-in is a two-sided conflict on f.txt.
printf 'base\n' > "$work/repo/f.txt"
jjr describe -m base >/dev/null
jjr bookmark create base -r @ >/dev/null
jjr new base -m side-a >/dev/null
printf 'a\n' > "$work/repo/f.txt"
jjr bookmark create side-a -r @ >/dev/null
jjr new base -m side-b >/dev/null
printf 'b\n' > "$work/repo/f.txt"
jjr bookmark create side-b -r @ >/dev/null
jjr new side-a side-b -m fanin >/dev/null 2>&1

# working_copy_has_conflicts evaluates the ambient `jj` against the
# current directory, so call it from inside the repo.
conflicted=no
( cd "$work/repo" && working_copy_has_conflicts ) && conflicted=yes
assert "conflicted fan-in is detected" "yes" "$conflicted"

jjr new base -m clean >/dev/null
clean=no
( cd "$work/repo" && working_copy_has_conflicts ) && clean=yes
assert "clean commit is not flagged" "no" "$clean"

echo ""
echo "test-regenerate-integration.sh: $checked case(s) checked," \
     "$failed failure(s)"
exit "$failed"
```

- [ ] **Step 2: Confirm the test cannot pass against the current
  script**

Do not run the test against the current script: its un-refactored
body runs at top level, so `source` would execute
`jj git fetch --remote origin` against the real `origin` as a side
effect, and then abort on the `$0`-relative `topic-revset.sh`
source path before defining `working_copy_has_conflicts`. Instead
confirm statically that the function the test calls does not yet
exist:

Run:

```bash
grep -n 'working_copy_has_conflicts' \
  scripts/regenerate-integration.sh || echo absent
```

Expected: `absent` — the function does not exist in the current
script, so the test (which sources the script and calls it) cannot
pass until the refactor in Step 3.

- [ ] **Step 3: Refactor the script to be sourceable with a guard**

Replace the entire contents of
`scripts/regenerate-integration.sh` with:

```bash
#!/usr/bin/env bash
#
# scripts/regenerate-integration.sh
#
# Regenerate the `integration` bookmark as a fan-in merge of `main`
# plus the tips of all currently-active topic branches whose
# changes are not already reachable from `main`.
#
# The integration bookmark is force-pushed to origin; main is never
# touched.
#
# Each run regenerates an equivalent fan-in (same parents) and
# force-pushes it; the published commit_id differs every run.
#
# Sourceable: `working_copy_has_conflicts` is defined above the
# `main` guard so scripts/tests/test-regenerate-integration.sh can
# exercise the conflict check without running the network IO.

# Return 0 if the working-copy commit (@) records any conflict.
# After the fan-in `jj new`, @ is the candidate integration commit;
# a textual conflict in any merged path makes @ a member of the
# `conflicts()` revset.
working_copy_has_conflicts() {
  [ -n "$(jj log -r 'conflicts() & @' --no-graph \
           -T 'commit_id ++ "\n"')" ]
}

main() {
  set -euo pipefail

  # Refresh lease state before touching the remote. Requires the
  # `origin` remote to be configured; without it, the fetch fails
  # loudly and the script aborts before any local rewrite.
  jj git fetch --remote origin

  # Promote fetched remote bookmarks to local tracking bookmarks so
  # the topic-branch revset (bookmarks(glob:"feat/*"), local)
  # matches them. CI does not carry the per-developer auto-track
  # configuration; an untracked feat/x@origin would otherwise
  # collapse the fan-in to `main` alone. Idempotent: already-tracked
  # bookmarks are left unchanged (jj warns and exits 0).
  jj bookmark track 'glob:*' --remote=origin

  # Guard against unborn `main` (e.g., on a freshly init'd repo
  # before any commits land on main). The fan-in revset's
  # `~ ::main` clauses depend on `::main` being a non-empty set;
  # if main is unborn, this script's behaviour is undefined.
  if [ -z "$(jj log -r main --no-graph -T 'change_id ++ "\n"' \
             2>/dev/null)" ]; then
    echo "regenerate-integration: 'main' bookmark unborn or" \
         "missing; nothing to fan in" >&2
    exit 1
  fi

  # Revset contract: topic-branch tips whose changes are not yet
  # reachable from `main`. See scripts/lib/topic-revset.sh.
  # shellcheck source=scripts/lib/topic-revset.sh
  . "$(dirname "${BASH_SOURCE[0]}")/lib/topic-revset.sh"

  revset="main | $TOPIC_TIPS_NOT_ON_MAIN_REVSET"

  # Resolve the revset to commit IDs to pass to `jj new`
  # (commit_id is stable for scripts that may be retried).
  parents=$(jj log -r "$revset" -T 'commit_id ++ " "' --no-graph)

  if [ -z "$(echo "$parents" | tr -d '[:space:]')" ]; then
    echo "regenerate-integration: empty revset (no main?" \
         "misconfiguration)" >&2
    exit 1
  fi

  # Fan-in merge into a new commit.
  # shellcheck disable=SC2086  # parents must word-split into args
  jj new $parents -m "integration: fan-in @ $(date -I)"

  # Refuse to publish a conflicted fan-in. `jj new` succeeds on a
  # textual conflict, recording it in @ rather than failing; CI
  # does not carry the local `git.private-commits = 'conflicts()'`
  # configuration that would otherwise make the push refuse. The
  # red check on this job is the textual-conflict signal.
  if working_copy_has_conflicts; then
    echo "::error::fan-in has textual conflicts; not publishing" \
         "integration" >&2
    jj resolve --list || true
    exit 1
  fi

  # Move the bookmark to the new fan-in commit. Each regeneration
  # produces a new fan-in that is a sibling of the previous one
  # (the old fan-in is intentionally orphaned and
  # garbage-collected). `--allow-backwards` permits jj to move the
  # bookmark to a non-descendant revision.
  jj bookmark set integration -r @ --allow-backwards

  # Move @ off the fan-in commit. Without this, the working copy is
  # integration: jj's snapshot-on-every-command would amend the
  # fan-in in place, and the bookmark (anchored to @) would
  # silently follow.
  jj new main

  # Push (lease-protected; jj uses git's force-with-lease semantics
  # and has no separate --force flag). First-time push auto-tracks
  # `integration` via the -b <name> form.
  jj git push --remote origin -b integration
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  main "$@"
fi
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `bash scripts/tests/test-regenerate-integration.sh`
Expected: PASS — two cases checked, 0 failures.

- [ ] **Step 5: Lint both scripts**

Run:

```bash
shellcheck -x scripts/regenerate-integration.sh \
  scripts/tests/test-regenerate-integration.sh
```

Expected: no output (exit 0). The `-x` flag lets shellcheck follow
the `# shellcheck source=` directives; without it, SC1091 ("Not
following") makes shellcheck exit 1 on the runtime-computed source
paths.

- [ ] **Step 6: Make the test executable and commit**

```bash
chmod +x scripts/tests/test-regenerate-integration.sh
jj describe -m "fix(integration): refuse to publish a conflicted fan-in"
jj new
```

---

## Task 4: Add the regeneration workflow

**Files:**

- Create: `.github/workflows/regenerate-integration.yml`

- [ ] **Step 1: Write the workflow**

`.github/workflows/regenerate-integration.yml`:

```yaml
name: Regenerate integration

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

jobs:
  regenerate:
    runs-on: ubuntu-latest
    timeout-minutes: 15
    steps:
      - uses: actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10  # v6.0.3
        with:
          fetch-depth: 0

      - name: Install pinned jj
        run: bash scripts/install-jj.sh

      - name: Configure jj (colocate + Actions bot identity)
        run: |
          jj git init --colocate
          jj config set --repo user.name "github-actions[bot]"
          jj config set --repo user.email \
            "41898282+github-actions[bot]@users.noreply.github.com"
          # Topic-branch tracking is handled inside the script
          # (jj bookmark track after fetch), so it works regardless
          # of any per-developer auto-track configuration.

      - name: Regenerate and publish integration
        run: bash scripts/regenerate-integration.sh

      - name: Trigger CI on the integration branch
        run: gh workflow run ci.yml --ref integration
        env:
          GH_TOKEN: ${{ github.token }}
```

- [ ] **Step 2: Validate YAML parses**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/regenerate-integration.yml'))"`
Expected: no output (exit 0).

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci(integration): regenerate integration on push to main"
jj new
```

---

## Task 5: Run the guard test in CI

**Files:**

- Modify: `.github/workflows/ci.yml`

- [ ] **Step 1: Add a job that installs jj and runs the guard
  test**

Append this job to the `jobs:` map in
`.github/workflows/ci.yml` (after the existing `hooks_test` job,
matching its indentation):

```yaml
  regenerate_guard_test:
    name: Integration regeneration guard test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10  # v6.0.3
      - name: Install pinned jj
        run: bash scripts/install-jj.sh
      - name: scripts/tests/test-regenerate-integration.sh
        run: bash scripts/tests/test-regenerate-integration.sh
```

- [ ] **Step 2: Validate YAML parses**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/ci.yml'))"`
Expected: no output (exit 0).

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci(integration): run the regeneration guard test in CI"
jj new
```

---

## Task 6: Run the guard test in the pre-push checklist

**Files:**

- Modify: `scripts/pre-push.sh`

- [ ] **Step 1: Add the test step**

In `scripts/pre-push.sh`, immediately after the existing block:

```bash
step "scripts/tests/test-mathlib-bump-detect.sh"
bash scripts/tests/test-mathlib-bump-detect.sh
```

insert:

```bash
step "scripts/tests/test-regenerate-integration.sh"
bash scripts/tests/test-regenerate-integration.sh
```

- [ ] **Step 2: Lint the script**

Run: `shellcheck -x scripts/pre-push.sh`
Expected: no new findings introduced by this change.

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci(integration): add the regeneration guard test to pre-push"
jj new
```

---

## Task 7: Record the jj-version auto-bump follow-on

**Files:**

- Modify: `TODO.md`

- [ ] **Step 1: Add the follow-on workstream**

In `TODO.md`, under `## Next up`, after the existing
`### Begin first mathematical workstream brainstorming` block,
add:

```markdown
### Automate the jj version pin bump

`feat/integration-regeneration-ci` introduces `scripts/jj-version`,
bumped by hand. Add a scheduled cron-bump-PR workflow mirroring
`update.yml`: query the latest `jj-vcs/jj` release, and when it is
newer than the pin, edit `scripts/jj-version` and open a pull
request. Depends on `scripts/jj-version` existing (this branch).
Dependabot does not cover release-binary version pins.
```

- [ ] **Step 2: Regenerate the TOC and lint**

Run:

```bash
doctoc --update-only TODO.md
markdownlint-cli2 'TODO.md'
```

Expected: `doctoc` updates (or leaves) the TOC; markdownlint
reports `0 error(s)` for `TODO.md`.

- [ ] **Step 3: Commit**

```bash
jj describe -m "doc(todo): record jj-version auto-bump follow-on"
jj new
```

---

## Task 8: Final verification and bookmark advance

**Files:** none (verification only).

- [ ] **Step 1: Run the new test directly**

Run: `bash scripts/tests/test-regenerate-integration.sh`
Expected: PASS — 2 cases checked, 0 failures.

- [ ] **Step 2: Lint every shell script touched**

Run:

```bash
shellcheck -x scripts/install-jj.sh \
  scripts/regenerate-integration.sh \
  scripts/tests/test-regenerate-integration.sh \
  scripts/pre-push.sh
```

Expected: no output (exit 0). `-x` lets shellcheck follow the
sourced files via their `# shellcheck source=` directives.

- [ ] **Step 3: Markdownlint the tree**

Run: `markdownlint-cli2 '**/*.md'`
Expected: `0 error(s)`.

- [ ] **Step 4: Advance the branch bookmark to the tip**

The last `jj new` left `@` empty; the implemented work is at `@-`.

Run: `jj bookmark set feat/integration-regeneration-ci -r @-`
Then: `jj log -r 'feat/integration-regeneration-ci'` and confirm
the bookmark sits on the `doc(todo)` commit.

- [ ] **Step 5: Hand off for review**

The regeneration workflow's live behaviour (fetch, fan-in, push,
ci dispatch) cannot run pre-merge from a topic branch; it is
exercised by the first push to `main` after merge, and can be
dry-run earlier via `workflow_dispatch` once an authorised push
exists. Note this in the pre-push review. Per
`CONTRIBUTING.md`, the spec and plan are removed in the branch's
final commits before merge.

## Deployment note

The regeneration workflow pushes the `integration` branch with
`GITHUB_TOKEN` (`contents: write`) and dispatches `ci.yml`
(`actions: write`). The repository's branch-protection settings
must permit the Actions bot to force-push `integration`. This is a
repository-settings prerequisite, not a code change; confirm it
before relying on the workflow.

## Self-review

- Spec coverage: trigger and concurrency (Task 4); direct pinned
  `jj` download (Tasks 1, 2); script hardening / `conflicts()`
  guard (Task 3); both conflict surfaces — textual via the guard
  (Task 3), build via the `ci.yml` dispatch (Task 4); unconditional
  regeneration (Task 4, no short-circuit); `scripts/jj-version`
  pin and the auto-bump follow-on (Tasks 1, 7); permissions and
  identity (Task 4).
- Type/name consistency: `working_copy_has_conflicts` and
  `scripts/jj-version` are named identically across the test
  (Task 3), the script (Task 3), and the installer (Task 2).
- No placeholders: every step carries the exact file content or
  command.
