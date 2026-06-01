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
#
# Detection needs network (git ls-remote, `npx` fetching semver,
# gh). Failures fail loudly (exit 1) rather than emitting an empty
# target, so an outage is never mistaken for "already current".

set -uo pipefail
# -e is intentionally omitted: bump_in_flight returns 1 on the common
# "not in flight" success path, which set -e would treat as fatal.
# All real failures are handled explicitly (if ! ..., || return 2, and
# the flight=$? capture in main).

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

# Given the current pin ($1) and candidate tags (newline-separated
# on stdin), print the newest tag semver-greater than the pin, or
# nothing. Delegates the comparison to the .cjs helper, run under
# `npx -p semver@7` with NODE_PATH set to the npx-installed module
# root so the helper's `require("semver")` resolves (the `-p` flag
# only adds the bin to PATH, not to node's require path). Exits
# non-zero if the helper errors, so callers can fail loudly.
select_target() {
  local pin="$1" helper
  helper="$(dirname "${BASH_SOURCE[0]}")/lib/select-newest-mathlib-tag.cjs"
  # _ becomes $0 inside the -c script; $1=helper, $2=pin.
  npx --yes -p semver@7 bash -c '
    node_modules="$(cd "$(dirname "$(command -v semver)")/.." && pwd)"
    NODE_PATH="$node_modules" node "$1" "$2"
  ' _ "$helper" "$pin"
}

# True iff the tag exists on the repo. Captures output rather than
# piping to `grep -q`: under `set -o pipefail`, `grep -q` closes the
# pipe on first match and the upstream `git` exits with SIGPIPE
# (141), which pipefail would surface as failure even on a match.
tag_exists() {
  local out
  out=$(git ls-remote --tags "$1" "refs/tags/$2")
  [[ -n "$out" ]]
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

# Emitting an empty target= is intentional protocol: the downstream
# workflow gates on `if: ... outputs.target != ''`, so the key must
# always be written (present-but-empty vs absent are different).
emit() {
  echo "target=$1"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    echo "target=$1" >> "$GITHUB_OUTPUT"
  fi
}

main() {
  local lakefile="${1:-lakefile.toml}"
  local pin tags target flight
  pin=$(read_mathlib_pin "$lakefile")
  if [[ -z "$pin" ]]; then
    echo "error: no mathlib rev pin in $lakefile" >&2
    exit 1
  fi

  # Fail loudly rather than silently reporting "no bump": an empty
  # tag list or a selector error must not be mistaken for "already
  # current" (the detect-and-discard failure of the old workflow).
  tags=$(list_version_tags "$MATHLIB_REPO")
  if [[ -z "$tags" ]]; then
    echo "error: no mathlib version tags fetched" >&2
    exit 1
  fi
  if ! target=$(printf '%s\n' "$tags" | select_target "$pin"); then
    echo "error: tag selection failed" >&2
    exit 1
  fi

  if [[ -z "$target" ]]; then
    echo "No mathlib release newer than $pin." >&2
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
