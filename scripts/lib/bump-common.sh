#!/usr/bin/env bash
#
# scripts/lib/bump-common.sh
#
# Helpers shared by the bump-detect scripts (jj-bump-detect.sh and
# mathlib-bump-detect.sh). Source this file; it defines select_target,
# bump_in_flight, and emit. bump_in_flight reads the BUMP_BRANCH and
# FAIL_LABEL variables, which the sourcing script sets before calling.
#
# Not meant to be executed directly.

# Given the current pin ($1) and candidate tags (newline-separated on
# stdin), print the newest tag semver-greater than the pin, or
# nothing. Delegates the comparison to select-newest-tag.cjs (a
# sibling of this file), run under `npx -p semver@7` with NODE_PATH
# set to the npx-installed module root so the helper's
# `require("semver")` resolves (the `-p` flag only adds the bin to
# PATH, not to node's require path). Exits non-zero if the helper
# errors, so callers can fail loudly. The helper emits the tag as
# given (v-prefixed when the input tags are), so callers strip the v
# afterwards if a bare version is needed.
select_target() {
  local pin="$1" helper
  helper="$(dirname "${BASH_SOURCE[0]}")/select-newest-tag.cjs"
  # _ becomes $0 inside the -c script; $1=helper, $2=pin. The inner
  # script intentionally uses single quotes (it expands under the
  # nested bash, not here).
  # shellcheck disable=SC2016
  npx --yes -p semver@7 bash -c '
    node_modules="$(cd "$(dirname "$(command -v semver)")/.." && pwd)"
    NODE_PATH="$node_modules" node "$1" "$2"
  ' _ "$helper" "$pin"
}

# Return 0 if a bump is in flight, 1 if not, 2 on error. Fails
# closed: a `gh` failure or non-numeric count is treated as an error
# (return 2), never as "not in flight" — otherwise a transient `gh`
# outage would let the apply job clobber an open, under-review pull
# request. Reads BUMP_BRANCH and FAIL_LABEL from the sourcing script.
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
