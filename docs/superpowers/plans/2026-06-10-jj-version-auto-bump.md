# jj-version auto-bump implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Execution conventions](#execution-conventions)
- [File structure](#file-structure)
  - [Task 1: Generalise the semver tag-selection helper name](#task-1-generalise-the-semver-tag-selection-helper-name)
  - [Task 2: Detect script with unit test (TDD)](#task-2-detect-script-with-unit-test-tdd)
  - [Task 3: Wire the test into pre-push, CI, and the checklist doc](#task-3-wire-the-test-into-pre-push-ci-and-the-checklist-doc)
  - [Task 4: The jj-bump workflow](#task-4-the-jj-bump-workflow)
  - [Task 5: One-time label and TODO entry removal](#task-5-one-time-label-and-todo-entry-removal)
  - [Task 6: Branch-completion verification](#task-6-branch-completion-verification)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A scheduled workflow that detects a newer `jj-vcs/jj`
release, verifies it installs and passes the regeneration guard
test, and opens a pull request bumping `scripts/jj-version`.

**Architecture:** Mirrors `.github/workflows/update.yml`: a
read-only detect job runs a fail-loudly script emitting
`target=<version>`; a write-permissioned apply job, gated on a
nonempty target, edits the pin, verifies, and opens the PR via
`peter-evans/create-pull-request`. Spec:
`docs/superpowers/specs/2026-06-09-jj-version-auto-bump-design.md`.

**Tech stack:** bash, jq, `gh` CLI, npm `semver` (via the shared
`scripts/lib` helper), GitHub Actions.

---

## Execution conventions

- **Version control is jj, not git.** Mutating `git` subcommands
  are blocked by a PreToolUse hook. The working copy `@` sits
  empty on top of the `feat/jj-version-auto-bump` bookmark. Each
  task's commit step is:

  ```bash
  jj describe -m "<message>"
  jj bookmark move feat/jj-version-auto-bump --to @
  jj new
  ```

  Changes land in `@` automatically (jj snapshots the working
  copy); there is no staging step.
- **No pushes.** The user reviews the diff line-by-line and
  authorises any push; this plan ends before any push.
- Run all commands from the repository root.

---

## File structure

| File | Action | Responsibility |
| --- | --- | --- |
| `scripts/lib/select-newest-tag.cjs` | rename from `select-newest-mathlib-tag.cjs` | generic semver tag selection (stdin tags, argv pin) |
| `scripts/mathlib-bump-detect.sh` | modify (helper path) | existing mathlib detect script |
| `scripts/jj-bump-detect.sh` | create | jj bump detection: pin read, latest-release query, asset gate, in-flight guard |
| `scripts/tests/test-jj-bump-detect.sh` | create | unit test for the detect script's pure logic |
| `scripts/pre-push.sh` | modify | run the new test in the checklist |
| `.github/workflows/ci.yml` | modify | new job running both detect-script tests |
| `docs/rules/ci-and-workflow.md` | modify | checklist enumeration lists the script tests |
| `.github/workflows/jj-bump.yml` | create | the scheduled detect/apply workflow |
| `TODO.md` | modify | remove the completed "Next up" entry |

---

### Task 1: Generalise the semver tag-selection helper name

The helper contains no mathlib-specific logic; the jj detect
script reuses it. Rename it and update the two references.

**Files:**

- Rename: `scripts/lib/select-newest-mathlib-tag.cjs` →
  `scripts/lib/select-newest-tag.cjs`
- Modify: `scripts/lib/select-newest-tag.cjs:1` (header comment)
- Modify: `scripts/mathlib-bump-detect.sh:69` (helper path)

- [ ] **Step 1: Rename the file**

```bash
mv scripts/lib/select-newest-mathlib-tag.cjs scripts/lib/select-newest-tag.cjs
```

(jj detects renames from the snapshot; no VCS command needed.)

- [ ] **Step 2: Update the helper's header comment**

In `scripts/lib/select-newest-tag.cjs`, change line 1 from:

```javascript
// scripts/lib/select-newest-mathlib-tag.cjs
```

to:

```javascript
// scripts/lib/select-newest-tag.cjs
```

- [ ] **Step 3: Update the caller in mathlib-bump-detect.sh**

In `scripts/mathlib-bump-detect.sh` (inside `select_target`),
change:

```bash
  helper="$(dirname "${BASH_SOURCE[0]}")/lib/select-newest-mathlib-tag.cjs"
```

to:

```bash
  helper="$(dirname "${BASH_SOURCE[0]}")/lib/select-newest-tag.cjs"
```

- [ ] **Step 4: Run the existing test to verify the rename**

Run: `bash scripts/tests/test-mathlib-bump-detect.sh`
Expected: `5 case(s) checked, 0 failure(s)`, exit 0.

- [ ] **Step 5: Commit**

```bash
jj describe -m "refactor(ci): generalise the semver tag-selection helper name"
jj bookmark move feat/jj-version-auto-bump --to @
jj new
```

---

### Task 2: Detect script with unit test (TDD)

**Files:**

- Test: `scripts/tests/test-jj-bump-detect.sh`
- Create: `scripts/jj-bump-detect.sh`

- [ ] **Step 1: Write the failing test**

Create `scripts/tests/test-jj-bump-detect.sh` (mode 0755):

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-jj-bump-detect.sh
#
# Smoke test for scripts/jj-bump-detect.sh. Sources the script
# (whose main is guarded) and exercises its pure logic: pin read
# (read_jj_pin), version selection and v-strip normalization
# (select_target, strip_v), and the latest-release predicates fed
# canned JSON (release_tag, release_has_asset). The network-bound
# IO wrappers are covered by a live workflow_dispatch run, not
# here.
#
# select_target uses `npx semver`, so this test requires network.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/jj-bump-detect.sh
source "$repo_root/scripts/jj-bump-detect.sh"

failed=0
checked=0

assert_eq() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL: $name: expected [$expected], got [$actual]" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

assert_status() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [[ "$actual" -ne "$expected" ]]; then
    echo "FAIL: $name: expected status $expected, got $actual" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

# Version selection: bare pin against the v-prefixed release tag.
assert_eq "newer release is selected" "v0.43.0" \
  "$(printf 'v0.43.0\n' | select_target 0.42.0)"
assert_eq "equal release yields empty" "" \
  "$(printf 'v0.42.0\n' | select_target 0.42.0)"
assert_eq "older release yields empty" "" \
  "$(printf 'v0.41.0\n' | select_target 0.42.0)"

# v-strip normalization: scripts/jj-version stores the bare
# version and scripts/install-jj.sh prepends the v itself.
assert_eq "strip_v drops a leading v" "0.43.0" "$(strip_v v0.43.0)"
assert_eq "strip_v passes bare versions through" "0.43.0" \
  "$(strip_v 0.43.0)"

# Pin read: whitespace-tolerant, matching install-jj.sh.
fixture="$(mktemp)"
trap 'rm -f "$fixture"' EXIT
printf '0.42.0\n' > "$fixture"
assert_eq "reads the bare pin" "0.42.0" "$(read_jj_pin "$fixture")"

# Canned latest-release JSON for the stdin-fed predicates.
release_json='{
  "tag_name": "v0.43.0",
  "assets": [
    {"name": "jj-v0.43.0-aarch64-apple-darwin.tar.gz"},
    {"name": "jj-v0.43.0-x86_64-unknown-linux-musl.tar.gz"}
  ]
}'

assert_eq "release_tag extracts tag_name" "v0.43.0" \
  "$(release_tag <<<"$release_json")"

release_has_asset 0.43.0 <<<"$release_json"
assert_status "musl asset present" 0 "$?"
release_has_asset 0.44.0 <<<"$release_json"
assert_status "musl asset absent for other version" 1 "$?"

echo ""
echo "test-jj-bump-detect.sh: $checked case(s) checked, $failed failure(s)"
exit "$failed"
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `bash scripts/tests/test-jj-bump-detect.sh`
Expected: FAIL — `source` errors with
`scripts/jj-bump-detect.sh: No such file or directory`; the test
runs on (the suite sets `-uo pipefail`, not `-e`, mirroring the
script it sources). Cases calling the missing functions FAIL
with `command not found`, except the two select_target
"yields empty" cases, which PASS vacuously (a failed command
substitution also yields the expected empty string). Expected
total: `9 case(s) checked, 7 failure(s)`, exit 7.

- [ ] **Step 3: Write the detect script**

Create `scripts/jj-bump-detect.sh` (mode 0755):

```bash
#!/usr/bin/env bash
#
# scripts/jj-bump-detect.sh
#
# Decide whether a jj release-binary bump should proceed, and to
# which version. Writes `target=<version>` (empty when no bump)
# to stdout and, when set, to $GITHUB_OUTPUT. Versions are bare
# (e.g. 0.43.0), matching scripts/jj-version; the GitHub release
# tag and asset name add the `v` prefix (scripts/install-jj.sh
# prepends it, so an unstripped emission would build a
# jj-vv<version> asset URL).
#
# A version is emitted only when all hold:
#   1. the latest jj release is semver-greater than the pin in
#      scripts/jj-version. `GET /releases/latest` excludes drafts
#      and prereleases server-side; the semver comparison guards
#      against the endpoint surfacing an older release (e.g.
#      after a yanked release);
#   2. the release carries the x86_64 musl asset that
#      scripts/install-jj.sh downloads (a published tag whose
#      binaries are still uploading must not produce a broken
#      bump PR);
#   3. no bump is in flight (no open PR on auto-update-jj/patch,
#      no open issue labelled jj-bump-fail).
#
# Detection needs network (gh, `npx` fetching semver). Failures
# fail loudly (exit 1) rather than emitting an empty target, so
# an outage is never mistaken for "already current".

set -uo pipefail
# -e is intentionally omitted: bump_in_flight returns 1 on the
# common "not in flight" success path, which set -e would treat
# as fatal. All real failures are handled explicitly (if ! ...,
# || return 2, and the flight=$? capture in main).

JJ_REPO="jj-vcs/jj"
BUMP_BRANCH="auto-update-jj/patch"
FAIL_LABEL="jj-bump-fail"

# Read the bare pinned version, whitespace-stripped (same read as
# scripts/install-jj.sh).
read_jj_pin() {
  tr -d '[:space:]' < "$1"
}

# Print the latest-release JSON for jj.
fetch_latest_release() {
  gh api "repos/${JJ_REPO}/releases/latest"
}

# Print the release's tag name (e.g. v0.43.0); release JSON on
# stdin.
release_tag() {
  jq -r '.tag_name // empty'
}

# True iff the release JSON on stdin carries the asset
# scripts/install-jj.sh downloads for the bare version $1.
release_has_asset() {
  local asset="jj-v$1-x86_64-unknown-linux-musl.tar.gz"
  jq -e --arg name "$asset" \
    '[.assets[].name] | index($name) != null' >/dev/null
}

# Given the current pin ($1) and candidate tags (newline-separated
# on stdin), print the newest tag semver-greater than the pin, or
# nothing. Same npx/NODE_PATH arrangement as
# mathlib-bump-detect.sh; the helper emits the tag as given
# (v-prefixed), so callers strip the v afterwards.
select_target() {
  local pin="$1" helper
  helper="$(dirname "${BASH_SOURCE[0]}")/lib/select-newest-tag.cjs"
  # _ becomes $0 inside the -c script; $1=helper, $2=pin.
  npx --yes -p semver@7 bash -c '
    node_modules="$(cd "$(dirname "$(command -v semver)")/.." && pwd)"
    NODE_PATH="$node_modules" node "$1" "$2"
  ' _ "$helper" "$pin"
}

# Strip a leading v, passing bare versions through.
strip_v() {
  printf '%s\n' "${1#v}"
}

# Return 0 if a bump is in flight, 1 if not, 2 on error. Fails
# closed: a `gh` failure or non-numeric count is treated as an
# error (return 2), never as "not in flight" — otherwise a
# transient `gh` outage would let the apply job clobber an open,
# under-review pull request.
bump_in_flight() {
  local open_pr open_issue
  open_pr=$(gh pr list --state open --head "$BUMP_BRANCH" \
    --json number --jq 'length') || return 2
  open_issue=$(gh issue list --state open --label "$FAIL_LABEL" \
    --json number --jq 'length') || return 2
  [[ "$open_pr" =~ ^[0-9]+$ ]] || return 2
  [[ "$open_issue" =~ ^[0-9]+$ ]] || return 2
  [[ "$open_pr" != "0" || "$open_issue" != "0" ]]
}

# Emitting an empty target= is intentional protocol: the
# downstream workflow gates on `if: ... outputs.target != ''`, so
# the key must always be written (present-but-empty vs absent are
# different).
emit() {
  echo "target=$1"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    echo "target=$1" >> "$GITHUB_OUTPUT"
  fi
}

main() {
  local pin_file="${1:-$(dirname "${BASH_SOURCE[0]}")/jj-version}"
  local pin release_json tag target version flight
  pin=$(read_jj_pin "$pin_file")
  if [[ -z "$pin" ]]; then
    echo "error: no jj version pin in $pin_file" >&2
    exit 1
  fi

  if ! release_json=$(fetch_latest_release); then
    echo "error: failed to fetch the latest jj release" >&2
    exit 1
  fi
  tag=$(release_tag <<<"$release_json")
  if [[ -z "$tag" ]]; then
    echo "error: no tag_name in the latest-release response" >&2
    exit 1
  fi

  if ! target=$(printf '%s\n' "$tag" | select_target "$pin"); then
    echo "error: version selection failed" >&2
    exit 1
  fi
  if [[ -z "$target" ]]; then
    echo "No jj release newer than $pin." >&2
    emit ""
    return 0
  fi
  version=$(strip_v "$target")

  if ! release_has_asset "$version" <<<"$release_json"; then
    echo "Release $tag lacks the x86_64 musl asset; waiting." >&2
    emit ""
    return 0
  fi

  bump_in_flight
  flight=$?
  if [[ "$flight" -eq 2 ]]; then
    echo "error: in-flight check failed (gh)" >&2
    exit 1
  fi
  if [[ "$flight" -eq 0 ]]; then
    echo "Bump in flight (open PR or $FAIL_LABEL issue); skipping." >&2
    emit ""
    return 0
  fi

  echo "Target jj bump: $version (from $pin)." >&2
  emit "$version"
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  main "$@"
fi
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `bash scripts/tests/test-jj-bump-detect.sh`
Expected: `9 case(s) checked, 0 failure(s)`, exit 0.

- [ ] **Step 5: Run the script live as an end-to-end smoke check**

Run: `bash scripts/jj-bump-detect.sh`
Expected (while the pin equals the latest release): stderr
`No jj release newer than 0.42.0.`, stdout `target=`, exit 0.
(If jj has published a newer release by execution time, expected
instead: `Target jj bump: <version> (from 0.42.0).` and
`target=<version>` — both are passes; what matters is a clean
exit and a coherent message.)

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(ci): add jj-bump-detect.sh with unit test"
jj bookmark move feat/jj-version-auto-bump --to @
jj new
```

---

### Task 3: Wire the test into pre-push, CI, and the checklist doc

**Files:**

- Modify: `scripts/pre-push.sh:53-54` (insert after the
  mathlib-bump-detect step)
- Modify: `.github/workflows/ci.yml` (new job at the end)
- Modify: `docs/rules/ci-and-workflow.md` (checklist enumeration)

- [ ] **Step 1: Add the pre-push step**

In `scripts/pre-push.sh`, after:

```bash
step "scripts/tests/test-mathlib-bump-detect.sh"
bash scripts/tests/test-mathlib-bump-detect.sh
```

insert:

```bash
step "scripts/tests/test-jj-bump-detect.sh"
bash scripts/tests/test-jj-bump-detect.sh
```

- [ ] **Step 2: Add the CI job**

Append to `.github/workflows/ci.yml` (after the
`regenerate_guard_test` job, same indentation level). Both detect
tests run here; `test-mathlib-bump-detect.sh` previously ran only
in pre-push:

```yaml
  bump_detect_tests:
    name: Bump detect-script tests
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10  # v6.0.3
      - name: install jq
        run: sudo apt-get install -y jq
      - name: scripts/tests/test-mathlib-bump-detect.sh
        run: bash scripts/tests/test-mathlib-bump-detect.sh
      - name: scripts/tests/test-jj-bump-detect.sh
        run: bash scripts/tests/test-jj-bump-detect.sh
```

- [ ] **Step 3: Update the checklist enumeration**

In `docs/rules/ci-and-workflow.md` § Pre-push checklist, replace:

```text
7. `scripts/tests/test-lint-imports.sh` passes.
8. `scripts/hooks/tests/test-block-mutating-git.sh` passes.
9. `markdownlint-cli2 '**/*.md'` quiet.
```

with:

```text
7. `scripts/tests/test-lint-imports.sh` passes.
8. `scripts/tests/test-mathlib-bump-detect.sh`,
   `scripts/tests/test-jj-bump-detect.sh`, and
   `scripts/tests/test-regenerate-integration.sh` pass.
9. `scripts/hooks/tests/test-block-mutating-git.sh` passes.
10. `markdownlint-cli2 '**/*.md'` quiet.
```

and renumber the remaining items (old 10–14 become 11–15; the
`(item 5)` cross-reference inside item 1 is unaffected).

- [ ] **Step 4: Verify the edited files**

Run:

```bash
bash -n scripts/pre-push.sh
markdownlint-cli2 docs/rules/ci-and-workflow.md
```

Expected: both exit 0 (for markdownlint, `Summary: 0 error(s)`
over the full file set).

- [ ] **Step 5: Commit**

```bash
jj describe -m "ci: wire jj-bump detect test into pre-push, CI, and checklist doc"
jj bookmark move feat/jj-version-auto-bump --to @
jj new
```

---

### Task 4: The jj-bump workflow

**Files:**

- Create: `.github/workflows/jj-bump.yml`

- [ ] **Step 1: Write the workflow**

Create `.github/workflows/jj-bump.yml`:

```yaml
name: jj bump

on:
  schedule:
    - cron: '0 17 * * 1'
  workflow_dispatch:

concurrency:
  group: jj-bump
  cancel-in-progress: false

jobs:
  detect:
    runs-on: ubuntu-latest
    timeout-minutes: 10
    permissions:
      contents: read
      pull-requests: read
      issues: read
    outputs:
      target: ${{ steps.detect.outputs.target }}
    steps:
      - uses: actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10  # v6.0.3
      - name: scripts/jj-bump-detect.sh
        id: detect
        run: bash scripts/jj-bump-detect.sh
        env:
          GH_TOKEN: ${{ github.token }}

  apply:
    needs: detect
    if: ${{ needs.detect.outputs.target != '' }}
    runs-on: ubuntu-latest
    timeout-minutes: 30
    permissions:
      contents: write
      pull-requests: write
      issues: write
      actions: write
    steps:
      - uses: actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10  # v6.0.3
      - name: Set scripts/jj-version to the target version
        id: set-pin
        run: printf '%s\n' "${TARGET}" > scripts/jj-version
        env:
          TARGET: ${{ needs.detect.outputs.target }}
      - name: Install the bumped jj
        id: install
        run: bash scripts/install-jj.sh
      - name: Run the regeneration guard test under the bumped jj
        id: guard
        run: bash scripts/tests/test-regenerate-integration.sh
      - name: Open or update the bump pull request
        id: pr
        uses: peter-evans/create-pull-request@5f6978faf089d4d20b00c7766989d076bb2fc7f1  # v8.1.1
        with:
          base: main
          branch: auto-update-jj/patch
          commit-message: "ci: bump jj to ${{ needs.detect.outputs.target }}"
          title: "ci: bump jj to ${{ needs.detect.outputs.target }}"
          body: |
            Automated bump of `scripts/jj-version` to jj
            ${{ needs.detect.outputs.target }}.

            Upstream release notes:
            https://github.com/jj-vcs/jj/releases/tag/v${{ needs.detect.outputs.target }}
      - name: Trigger CI on the bump pull request
        id: dispatch
        if: ${{ steps.pr.outputs.pull-request-number != '' }}
        run: gh workflow run ci.yml --ref auto-update-jj/patch
        env:
          GH_TOKEN: ${{ github.token }}
      - name: Open a failure issue
        if: ${{ failure() }}
        run: |
          body_file="$(mktemp)"
          cat > "$body_file" <<EOF
          Automated jj bump to ${TARGET} failed.

          Step outcomes: set-pin=${SET_PIN}, install=${INSTALL},
          guard=${GUARD}, open-PR=${PR}, dispatch-CI=${DISPATCH}.

          A failure here can coexist with a successfully opened
          bump PR (e.g. only the CI dispatch failed). This issue
          suppresses scheduled bumps while open; close it to
          re-enable them.

          Run: ${RUN_URL}
          EOF
          gh issue create --label jj-bump-fail \
            --title "jj bump to ${TARGET} failed" \
            --body-file "$body_file"
        env:
          GH_TOKEN: ${{ github.token }}
          TARGET: ${{ needs.detect.outputs.target }}
          SET_PIN: ${{ steps.set-pin.outcome }}
          INSTALL: ${{ steps.install.outcome }}
          GUARD: ${{ steps.guard.outcome }}
          PR: ${{ steps.pr.outcome }}
          DISPATCH: ${{ steps.dispatch.outcome }}
          RUN_URL: ${{ github.server_url }}/${{ github.repository }}/actions/runs/${{ github.run_id }}
```

Notes for the implementer:

- The `actions/checkout` SHA matches the pin used across
  `.github/workflows/*.yml`; the `create-pull-request` SHA is
  release v8.1.1's commit, verified against
  `gh api repos/peter-evans/create-pull-request/git/ref/tags/v8.1.1`.
- In the heredoc, `${TARGET}` etc. are shell expansions of the
  step's `env:` block, not `${{ }}` expression injections; do not
  inline `${{ }}` into the script body.
- The heredoc's closing `EOF` must sit at the same indentation as
  the `cat` line within the YAML block scalar (the block strips
  the common indentation, leaving `EOF` at column 0 of the
  script).

- [ ] **Step 2: Validate the YAML parses**

Run:

```bash
python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/jj-bump.yml')); print('ok')"
```

Expected: `ok`.

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci: add scheduled jj-version bump workflow"
jj bookmark move feat/jj-version-auto-bump --to @
jj new
```

---

### Task 5: One-time label and TODO entry removal

**Files:**

- Modify: `TODO.md:17-23` (remove the completed entry)
- Repository side effect: create the `jj-bump-fail` label.

- [ ] **Step 1: Create the failure label (idempotent)**

```bash
gh label list --search jj-bump-fail --json name --jq 'length'
```

If the output is `0`, create it:

```bash
gh label create jj-bump-fail \
  --description "An automated jj version bump failed; an open issue with this label suppresses scheduled bumps" \
  --color D93F0B
```

Verify: `gh label list --search jj-bump-fail` lists the label.
(Without it, the workflow's failure-issue step itself fails:
`gh issue create --label` errors on a nonexistent label.)

- [ ] **Step 2: Remove the completed TODO entry**

In `TODO.md`, delete this subsection (under "## Next up"):

```text
### Automate the jj version pin bump

`scripts/jj-version` (the pinned jj version for CI) is bumped by
hand. Add a scheduled cron-bump-PR workflow mirroring `update.yml`:
query the latest `jj-vcs/jj` release, and when it is newer than the
pin, edit `scripts/jj-version` and open a pull request. Dependabot
does not cover release-binary version pins.
```

The "Begin first mathematical workstream brainstorming" entry
remains.

- [ ] **Step 3: Verify markdown cleanliness**

Run: `markdownlint-cli2 '**/*.md'`
Expected: `Summary: 0 error(s)`.

- [ ] **Step 4: Commit**

```bash
jj describe -m "doc: remove completed jj-version bump TODO entry"
jj bookmark move feat/jj-version-auto-bump --to @
jj new
```

---

### Task 6: Branch-completion verification

No new files; this task gates the hand-back to the user.

- [ ] **Step 1: Run the script-level checks**

```bash
bash scripts/tests/test-mathlib-bump-detect.sh
bash scripts/tests/test-jj-bump-detect.sh
bash scripts/tests/test-regenerate-integration.sh
bash -n scripts/pre-push.sh
bash -n scripts/jj-bump-detect.sh
markdownlint-cli2 '**/*.md'
doctoc --dryrun --update-only .
```

Expected: every command exits 0.

- [ ] **Step 2: Review the branch shape**

```bash
jj log -r 'main..feat/jj-version-auto-bump'
jj diff -r 'main..feat/jj-version-auto-bump' --stat
```

Expected: spec commit, spec revision, plan commit(s), then the
five implementation commits from Tasks 1–5; diff touches only the
files in the file-structure table plus the spec/plan documents.

- [ ] **Step 3: Hand back to the user**

Report completion. Remaining steps outside this plan's scope, in
order:

1. The user runs `scripts/pre-push.sh` (full checklist, including
   the lake build/test/lint steps this plan does not repeat) and
   reviews the diff line-by-line.
2. Spec and plan removal commit
   (`doc(ci): remove transient jj-bump spec and plan`) as the
   branch's final commit, per CONTRIBUTING.md § Concern shape.
3. Push and PR (user-authored description), merge.
4. Post-merge live verification: `gh workflow run jj-bump.yml`,
   then confirm the detect job logs
   `No jj release newer than <pin>.` and the apply job is
   skipped. The apply path gets its live exercise at jj's next
   release.
