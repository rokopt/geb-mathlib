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
# leanprover-community/lean-update labels its failure issue with this
# exact name and deduplicates by it, creating the label on first use
# (its `ensureLabel`). The in-flight suppression here queries the same
# label, so the two agree without any setup on our side; `gh issue
# list --label <absent>` returns 0 (not an error) before the first
# failure ever creates it.
FAIL_LABEL="auto-update-lean-fail"

# select_target, bump_in_flight (reads BUMP_BRANCH/FAIL_LABEL above),
# and emit are shared with jj-bump-detect.sh.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/bump-common.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/bump-common.sh"

# Read the mathlib `rev` from the name="mathlib" require block
# (TOML-aware; a plain grep would also match cslib/doc-gen4 revs).
# Uses tomllib (Python 3.11+) when available, falling back to tomli,
# then to a minimal scan of the [[require]] array-of-tables so the
# script works on older system Pythons without a TOML library.
read_mathlib_pin() {
  python3 - "$1" <<'PY'
import sys, re

try:
    import tomllib
except ModuleNotFoundError:
    try:
        import tomli as tomllib
    except ModuleNotFoundError:
        tomllib = None

path = sys.argv[1]

if tomllib is not None:
    with open(path, "rb") as f:
        data = tomllib.load(f)
    for req in data.get("require", []):
        if req.get("name") == "mathlib":
            print(req.get("rev", ""))
            break
    sys.exit(0)

# Fallback: walk [[require]] blocks, recording name and rev per block,
# and print the rev of the block whose name is "mathlib".
name = rev = None
with open(path, encoding="utf-8") as f:
    for line in f:
        s = line.strip()
        if s == "[[require]]":
            name = rev = None
            continue
        if s.startswith("[") and s != "[[require]]":
            # Left the require array-of-tables.
            name = rev = None
            continue
        m = re.match(r'name\s*=\s*"([^"]*)"', s)
        if m:
            name = m.group(1)
        m = re.match(r'rev\s*=\s*"([^"]*)"', s)
        if m:
            rev = m.group(1)
        if name == "mathlib" and rev is not None:
            print(rev)
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

# True iff the tag exists on the repo. Captures output rather than
# piping to `grep -q`: under `set -o pipefail`, `grep -q` closes the
# pipe on first match and the upstream `git` exits with SIGPIPE
# (141), which pipefail would surface as failure even on a match.
tag_exists() {
  local out
  out=$(git ls-remote --tags "$1" "refs/tags/$2")
  [[ -n "$out" ]]
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
