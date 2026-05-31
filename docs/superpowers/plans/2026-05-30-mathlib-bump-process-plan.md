# Mathlib bump process Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [File structure](#file-structure)
- [Task 1: Pin mathlib to a rev in lakefile.toml](#task-1-pin-mathlib-to-a-rev-in-lakefiletoml)
- [Task 2: Detection script](#task-2-detection-script)
- [Task 3: Rewrite update.yml as a two-job detect+apply workflow](#task-3-rewrite-updateyml-as-a-two-job-detectapply-workflow)
- [Task 4: Update docs/process.md § Mathlib bump procedure](#task-4-update-docsprocessmd--mathlib-bump-procedure)
- [Task 5: Verify the pipeline on the live repository](#task-5-verify-the-pipeline-on-the-live-repository)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the non-functional `.github/workflows/update.yml`
with a scheduled workflow that self-detects the newest mathlib
release tag against the project's own pin and, when one is
available and published on all three pinned dependencies, opens a
reviewed pull request bumping `mathlib`, `cslib`, and `doc-gen4` to
it in lockstep (an issue on build failure).

**Architecture:** A detection shell script
(`scripts/mathlib-bump-detect.sh`) reuses `mathlib-update-action`'s
tag-selection (`git ls-remote --tags` + npm `semver`) but baselines
against the lakefile pin, gates on the tag existing on cslib and
doc-gen4 and on no bump being in flight, and emits a target tag. A
two-job `update.yml` runs the script (job 1) then, when a target is
emitted, edits the three `rev` fields and applies via
`leanprover-community/lean-update` (job 2), which runs an in-tree
`lake update`, builds via `leanprover/lean-action`, and opens the
pull request or issue.

**Tech Stack:** GitHub Actions; `bash`; `python3` (`tomllib`) for
the TOML-aware pin read; the npm `semver` package via `npx` for
version ordering; `gh` CLI for in-flight queries; `jj` for commits;
`leanprover-community/lean-update` and `leanprover/lean-action`.

**Working branch:** `feat/mathlib-bump-pipeline` (already carries
the design spec). Continue committing here.

**Commit convention:** This repo uses `jj`, not raw mutating `git`
(a PreToolUse hook blocks the latter). Each commit step is
`jj commit -m "<msg>"` followed by
`jj bookmark set feat/mathlib-bump-pipeline -r @-`. All commit
messages end with the trailer
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`,
omitted from the commands below for brevity.

**Reference:** Design spec at
[docs/superpowers/specs/2026-05-30-mathlib-bump-process-design.md](../specs/2026-05-30-mathlib-bump-process-design.md).

---

## File structure

- `lakefile.toml` (modify) — pin `mathlib` to a `rev` tag, uniform
  with `cslib`/`doc-gen4`; `mathlib` stays the last `[[require]]`.
- `scripts/mathlib-bump-detect.sh` (create) — detection: emit a
  target tag or nothing. One responsibility: decide whether a bump
  should proceed and to which tag.
- `scripts/tests/test-mathlib-bump-detect.sh` (create) — smoke test
  for the script's pure logic (tag selection, pin read).
- `scripts/pre-push.sh` (modify) — run the new smoke test.
- `.github/workflows/update.yml` (replace) — two-job detect+apply.
- `docs/process.md` (modify) — rewrite § Mathlib bump procedure to
  match the implemented flow.

---

## Task 1: Pin mathlib to a rev in lakefile.toml

**Files:**

- Modify: `lakefile.toml` (the `name = "mathlib"` require block)

- [ ] **Step 1: Add the `rev` pin to the mathlib require**

In `lakefile.toml`, the mathlib require currently reads:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
```

Change it to (keep the block last; add only the `rev` line):

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.30.0-rc2"
```

- [ ] **Step 2: Regenerate the manifest and confirm the build**

Run: `lake update && lake exe cache get && lake build`
Expected: `lake update` rewrites `lake-manifest.json` with the
mathlib entry now carrying `"inputRev": "v4.30.0-rc2"` (previously
`null`); `lean-toolchain` remains `leanprover/lean4:v4.30.0-rc2`;
`lake build` succeeds.

- [ ] **Step 3: Verify the pin is readable and the toolchain is unchanged**

Run:

```bash
python3 -c "import tomllib; d=tomllib.load(open('lakefile.toml','rb')); print([r['rev'] for r in d['require'] if r.get('name')=='mathlib'])"
cat lean-toolchain
```

Expected: `['v4.30.0-rc2']` and `leanprover/lean4:v4.30.0-rc2`.

- [ ] **Step 4: Commit**

```bash
jj commit -m "chore: pin mathlib to v4.30.0-rc2 for lockstep bumping

Uniform with cslib and doc-gen4; mathlib stays the last require so
the cache-hash ordering constraint holds. Enables detection to
baseline against the pin."
jj bookmark set feat/mathlib-bump-pipeline -r @-
```

---

## Task 2: Detection script

**Files:**

- Create: `scripts/mathlib-bump-detect.sh`
- Test: `scripts/tests/test-mathlib-bump-detect.sh`
- Modify: `scripts/pre-push.sh`

- [ ] **Step 1: Write the failing smoke test**

Create `scripts/tests/test-mathlib-bump-detect.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-mathlib-bump-detect.sh
#
# Smoke test for scripts/mathlib-bump-detect.sh. Sources the script
# (whose main is guarded) and exercises its pure logic: tag
# selection (select_target, via the npm semver package) and the
# TOML-aware pin read (read_mathlib_pin). The network-bound IO
# wrappers are covered by the live workflow_dispatch run, not here.
#
# select_target uses `npx semver`, so this test requires network.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/mathlib-bump-detect.sh
source "$repo_root/scripts/mathlib-bump-detect.sh"

failed=0
checked=0

assert_eq() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL: $name: expected [$expected], got [$actual]" >&2
    failed=$((failed + 1))
  fi
}

assert_eq "newer rc is selected" "v4.31.0-rc1" \
  "$(printf 'v4.30.0-rc2\nv4.31.0-rc1\n' | select_target v4.30.0-rc2)"
assert_eq "no newer tag yields empty" "" \
  "$(printf 'v4.30.0-rc1\nv4.30.0-rc2\n' | select_target v4.30.0-rc2)"
assert_eq "stable outranks its rc" "v4.31.0" \
  "$(printf 'v4.31.0-rc1\nv4.31.0\n' | select_target v4.31.0-rc1)"
assert_eq "pin already newest yields empty" "" \
  "$(printf 'v4.31.0-rc1\n' | select_target v4.31.0-rc1)"

fixture="$(mktemp)"
trap 'rm -f "$fixture"' EXIT
cat > "$fixture" <<'TOML'
[[require]]
name = "cslib"
rev = "v4.29.0"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.30.0-rc2"
TOML
assert_eq "reads the mathlib pin, not cslib" "v4.30.0-rc2" \
  "$(read_mathlib_pin "$fixture")"

if [[ "$failed" -ne 0 ]]; then
  echo "$failed/$checked checks failed" >&2
  exit 1
fi
echo "all $checked checks passed"
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `bash scripts/tests/test-mathlib-bump-detect.sh`
Expected: FAIL — `scripts/mathlib-bump-detect.sh` does not exist, so
`source` errors (`No such file or directory`).

- [ ] **Step 3: Write the detection script**

Create `scripts/mathlib-bump-detect.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/mathlib-bump-detect.sh
#
# Decide whether a mathlib release-tag bump should proceed, and to
# which tag. Writes `target=<tag>` (empty when no bump) to stdout
# and, when set, to $GITHUB_OUTPUT.
#
# A tag is emitted only when all hold:
#   1. it is semver-greater than the current mathlib pin (read from
#      the name="mathlib" require in lakefile.toml);
#   2. the same tag exists on cslib and doc-gen4 (lockstep tag-lag
#      gate: writing an unpublished tag would fail `lake update`);
#   3. no bump is in flight (no open PR on auto-update-lean/patch,
#      no open issue labelled auto-update-lean-fail).
#
# Tag selection reuses mathlib-update-action's algorithm: the v*.*
# tags from `git ls-remote --tags`, ordered by the npm `semver`
# package via `semver.gt` (not `sort -V`, which misorders
# prereleases such as v4.31.0-rc1 against v4.31.0).

set -uo pipefail

MATHLIB_REPO="https://github.com/leanprover-community/mathlib4.git"
CSLIB_REPO="https://github.com/leanprover/cslib.git"
DOCGEN_REPO="https://github.com/leanprover/doc-gen4.git"
BUMP_BRANCH="auto-update-lean/patch"
FAIL_LABEL="auto-update-lean-fail"

# Read the mathlib `rev` from the name="mathlib" require block
# (TOML-aware; a plain grep would also match cslib/doc-gen4 revs).
read_mathlib_pin() {
  python3 - "$1" <<'PY'
import sys, tomllib
with open(sys.argv[1], "rb") as f:
    data = tomllib.load(f)
for req in data.get("require", []):
    if req.get("name") == "mathlib":
        print(req.get("rev", ""))
        break
PY
}

# List a repo's vMAJOR.MINOR(.PATCH)(-rcN) tags, one per line,
# dropping the ^{} dereference lines for annotated tags.
list_version_tags() {
  git ls-remote --tags "$1" \
    | grep -v '\^{}$' \
    | sed -n 's#.*refs/tags/\(v[0-9].*\)$#\1#p'
}

# Pure: given the current pin ($1) and candidate tags (newline-
# separated on stdin), print the newest tag semver-greater than the
# pin, or nothing. Uses the npm `semver` package (semver.gt /
# semver.compare), parsing the v-stripped tag without coercion so
# prerelease components are preserved.
select_target() {
  npx --yes -p semver@7 node -e '
    const semver = require("semver");
    const pin = process.argv[1].replace(/^v/, "");
    const fs = require("fs");
    const clean = (t) => t.replace(/^v/, "");
    const tags = fs.readFileSync(0, "utf8").split("\n")
      .map((s) => s.trim()).filter(Boolean)
      .filter((t) => semver.valid(clean(t)));
    const newer = tags
      .filter((t) => semver.gt(clean(t), pin))
      .sort((a, b) => semver.compare(clean(a), clean(b)));
    process.stdout.write(newer.length ? newer[newer.length - 1] : "");
  ' "$1"
}

tag_exists() {
  git ls-remote --tags "$1" "refs/tags/$2" | grep -q .
}

bump_in_flight() {
  local open_pr open_issue
  open_pr=$(gh pr list --state open --head "$BUMP_BRANCH" \
    --json number --jq 'length')
  open_issue=$(gh issue list --state open --label "$FAIL_LABEL" \
    --json number --jq 'length')
  [[ "${open_pr:-0}" != "0" || "${open_issue:-0}" != "0" ]]
}

emit() {
  echo "target=$1"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    echo "target=$1" >> "$GITHUB_OUTPUT"
  fi
}

main() {
  local lakefile="${1:-lakefile.toml}"
  local pin target
  pin=$(read_mathlib_pin "$lakefile")
  if [[ -z "$pin" ]]; then
    echo "error: no mathlib rev pin in $lakefile" >&2
    exit 1
  fi

  target=$(list_version_tags "$MATHLIB_REPO" | select_target "$pin")
  if [[ -z "$target" ]]; then
    echo "No mathlib release newer than $pin." >&2
    emit ""
    return 0
  fi

  if bump_in_flight; then
    echo "Bump in flight (open PR or $FAIL_LABEL issue); skipping." >&2
    emit ""
    return 0
  fi

  if ! tag_exists "$CSLIB_REPO" "$target" \
    || ! tag_exists "$DOCGEN_REPO" "$target"; then
    echo "Target $target not yet on cslib and/or doc-gen4; waiting." >&2
    emit ""
    return 0
  fi

  echo "Target mathlib bump: $target (from $pin)." >&2
  emit "$target"
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  main "$@"
fi
```

- [ ] **Step 4: Make the script executable**

Run: `chmod +x scripts/mathlib-bump-detect.sh`

- [ ] **Step 5: Run the smoke test to verify it passes**

Run: `bash scripts/tests/test-mathlib-bump-detect.sh`
Expected: `all 5 checks passed` (requires network for `npx`).

- [ ] **Step 6: Sanity-run against the live repo**

Run: `bash scripts/mathlib-bump-detect.sh`
Expected: with the repo behind, stderr reports the target and
stdout prints `target=v4.31.0-rc1` (assuming `v4.31.0-rc1` is the
newest mathlib release present on cslib and doc-gen4 and no bump is
in flight). If a newer release has since appeared, expect that tag.

- [ ] **Step 7: Wire the smoke test into pre-push**

In `scripts/pre-push.sh`, after the existing block:

```bash
step "scripts/tests/test-lint-imports.sh"
bash scripts/tests/test-lint-imports.sh
```

add:

```bash
step "scripts/tests/test-mathlib-bump-detect.sh"
bash scripts/tests/test-mathlib-bump-detect.sh
```

- [ ] **Step 8: Commit**

```bash
jj commit -m "feat(ci): add mathlib-bump detection script

Self-detect the newest mathlib release tag against the lakefile
pin (reusing mathlib-update-action's git-ls-remote + npm semver
selection); gate on the tag existing on cslib and doc-gen4 and on
no bump being in flight. Add a smoke test and wire it into
pre-push."
jj bookmark set feat/mathlib-bump-pipeline -r @-
```

---

## Task 3: Rewrite update.yml as a two-job detect+apply workflow

**Files:**

- Replace: `.github/workflows/update.yml`

- [ ] **Step 1: Replace the workflow**

Overwrite `.github/workflows/update.yml` with:

```yaml
name: Mathlib bump

on:
  schedule:
    - cron: '0 17 * * *'
  workflow_dispatch:

jobs:
  detect:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      pull-requests: read
      issues: read
    outputs:
      target: ${{ steps.detect.outputs.target }}
    steps:
      - uses: actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd  # v6.0.2
      - name: scripts/mathlib-bump-detect.sh
        id: detect
        run: bash scripts/mathlib-bump-detect.sh
        env:
          GH_TOKEN: ${{ github.token }}

  apply:
    needs: detect
    if: ${{ needs.detect.outputs.target != '' }}
    runs-on: ubuntu-latest
    permissions:
      contents: write
      pull-requests: write
      issues: write
    steps:
      - uses: actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd  # v6.0.2
      - name: Set mathlib, cslib, doc-gen4 revs to the target tag
        run: |
          sed -i -E 's/^rev = "[^"]*"/rev = "'"${TARGET}"'"/' lakefile.toml
          echo "lakefile.toml require revisions set to ${TARGET}:"
          grep -nE '^rev = ' lakefile.toml
        env:
          TARGET: ${{ needs.detect.outputs.target }}
      - name: lean-update (lake update, build, PR or issue)
        uses: leanprover-community/lean-update@926dc957637414948c317588eb14899cddf1fe11  # v0.7.0
        with:
          on_update_succeeds: pr
          on_update_fails: issue
          update_if_modified: lake-manifest.json
```

- [ ] **Step 2: Lint the workflow YAML**

Run:

```bash
python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/update.yml')); print('YAML OK')"
```

Expected: `YAML OK`.

- [ ] **Step 3: Confirm the sed targets exactly the three rev lines**

Run:

```bash
TARGET=v4.31.0-rc1
sed -E 's/^rev = "[^"]*"/rev = "'"${TARGET}"'"/' lakefile.toml | grep -nE '^rev = '
```

Expected: three lines, each `rev = "v4.31.0-rc1"` (mathlib, cslib,
doc-gen4). Do not save this; it is a dry check of the substitution.

- [ ] **Step 4: Commit**

```bash
jj commit -m "ci: rewrite update.yml as detect + lean-update apply

Job 1 runs the detection script; job 2 (only when a target is
emitted) sets the three dependency revs to the target tag and runs
lean-update, which performs an in-tree lake update, builds via
lean-action, and opens a PR on success or an issue on failure.
Pins lean-update to v0.7.0."
jj bookmark set feat/mathlib-bump-pipeline -r @-
```

---

## Task 4: Update docs/process.md § Mathlib bump procedure

**Files:**

- Modify: `docs/process.md` (the `## Mathlib bump procedure` section)

- [ ] **Step 1: Replace the section body**

The current `## Mathlib bump procedure` section reads:

```markdown
## Mathlib bump procedure

Two flows: cron-driven (`update.yml` runs `mathlib-update-action`,
opens a PR against `main`); user-initiated (manual
`bump/<lean-version>` branch). Both end with `main` updated, topic
branches mass-rebased via `scripts/rebase-topics.sh`,
`integration` regenerated. Tracking mathlib closely (rather than
batching bumps) keeps adaptation cost amortised; the cron is the
default, the manual flow handles the cases the cron cannot
(toolchain bumps, breaking changes).
```

Replace the body (keep the `## Mathlib bump procedure` heading)
with:

```markdown
## Mathlib bump procedure

`update.yml` (daily cron plus manual dispatch) self-detects the
newest mathlib release tag against the project's pin via
`scripts/mathlib-bump-detect.sh`, which reuses
`mathlib-update-action`'s tag-selection (`git ls-remote --tags` +
npm `semver`) but baselines against the `lakefile.toml` pin. It
emits a target only when the tag is newer, exists on `cslib` and
`doc-gen4` (the version-locked dependencies bump in lockstep), and
no bump is in flight. The apply job sets all three `rev` fields to
the target and runs `leanprover-community/lean-update`, which does
an in-tree `lake update`, builds via `leanprover/lean-action`, and
opens a pull request on success or an issue on failure; nothing
merges automatically. A contributor reviews the diff line-by-line
and merges. After merge to `main`, the maintainer mass-rebases
active topic branches with `scripts/rebase-topics.sh main` and
regenerates `integration` with `scripts/regenerate-integration.sh`.
The detector tracks release tags, not `master`; design and
rationale are in
`docs/superpowers/specs/2026-05-30-mathlib-bump-process-design.md`.
```

- [ ] **Step 2: Regenerate the TOC and lint**

Run:

```bash
doctoc --update-only docs/process.md
markdownlint-cli2 docs/process.md
```

Expected: doctoc reports `Everything is OK`; markdownlint reports
`0 error(s)` for `docs/process.md`.

- [ ] **Step 3: Commit**

```bash
jj commit -m "doc: update Mathlib bump procedure to the implemented flow

Describe the self-detect + lean-update apply pipeline, the
three-way lockstep, the in-flight guards, and the post-merge
rebase/integration steps, replacing the stale text that described
update.yml as already opening PRs."
jj bookmark set feat/mathlib-bump-pipeline -r @-
```

---

## Task 5: Verify the pipeline on the live repository

This is a bug-fix on the live repo (the test-repo-first discipline
governs repository creation only). The repo is currently behind
mathlib, so the first run exercises a real bump.

- [ ] **Step 1: Confirm detection emits the expected target**

Run: `GH_TOKEN=$(gh auth token) bash scripts/mathlib-bump-detect.sh`
Expected: `target=v4.31.0-rc1` (or the current newest mathlib
release tag that is also on cslib and doc-gen4 with no bump in
flight). Spec Verification item 2.

- [ ] **Step 2: Push the branch for review, then trigger the workflow**

The workflow lives on the branch; trigger it after the branch is
pushed and reviewed per the project's no-push-without-review rule.
Once pushed, run:

```bash
gh workflow run "Mathlib bump" --ref feat/mathlib-bump-pipeline
gh run watch "$(gh run list --workflow='Mathlib bump' --limit 1 --json databaseId --jq '.[0].databaseId')"
```

Expected: the `detect` job emits the target; the `apply` job runs
`lean-update`, which opens a pull request bumping `mathlib`,
`cslib`, and `doc-gen4` to the target tag with a regenerated
`lake-manifest.json` and `lean-toolchain`. Spec Verification item 1.

- [ ] **Step 3: Confirm the bump pull request is green**

Run: `gh pr checks auto-update-lean/patch`
Expected: `ci.yml` (build/test/lint/shake/axiom) passes on the bump
pull request. If it fails, that is a real incompatibility to fix on
the branch — fix it there (the process itself is what is being
validated; defects in the process are fixed in the process).

- [ ] **Step 4: Confirm the in-flight guard**

Re-run the detection while the bump pull request is open:
Run: `GH_TOKEN=$(gh auth token) bash scripts/mathlib-bump-detect.sh`
Expected: `target=` (empty) with stderr "Bump in flight"; the open
pull request is not disturbed. Spec Verification item 3.

- [ ] **Step 5: Record completion**

The bump pull request is reviewed and merged by a contributor (not
by the workflow). After merge, run `scripts/rebase-topics.sh main`
and `scripts/regenerate-integration.sh` per § Mathlib bump
procedure. Spec Verification items 1-3 are then satisfied on the
live repo; item 4 (a `Cslib.…` import building against the bumped
pair) is exercised when the first cslib-importing module lands.
