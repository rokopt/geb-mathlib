#!/usr/bin/env bash
#
# scripts/tests/test-vcs.sh
#
# Regression test for scripts/lib/vcs.sh: vcs_in_use answers `git`
# in a plain git repository and in a git worktree, whether the
# worktree sits outside a colocated jj repository or nested inside
# it (the case a bare .jj/ lookup gets wrong), and `jj` at the root
# of a colocated repository and in a workspace added with
# `jj workspace add`.
#
# The jj cases skip cleanly when jj is unavailable (e.g. a CI job
# that does not install jj); the plain-git case always runs.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source-path=SCRIPTDIR
# shellcheck source=../lib/vcs.sh
source "$here/../lib/vcs.sh"

failed=0
checked=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# assert_vcs <name> <expected> <directory>: vcs_in_use run from the
# directory prints the expected answer.
assert_vcs() {
  local name="$1" expected="$2" dir="$3" got
  checked=$((checked + 1))
  got="$(cd "$dir" && vcs_in_use)"
  if [ "$got" != "$expected" ]; then
    echo "FAIL: $name: expected $expected, got $got"
    failed=1
  fi
}

git_commit() {
  git -c user.name=test -c user.email=test@example.com \
    commit -q --allow-empty -m base
}

mkdir "$tmp/plain"
(cd "$tmp/plain" && git init -q -b main && git_commit)
assert_vcs "plain git repository" git "$tmp/plain"

if command -v jj >/dev/null 2>&1; then
  export JJ_USER="test" JJ_EMAIL="test@example.com"

  mkdir "$tmp/colo"
  (cd "$tmp/colo" && git init -q -b main && git_commit \
     && jj git init --colocate >/dev/null 2>&1)
  assert_vcs "colocated jj repository root" jj "$tmp/colo"

  (cd "$tmp/colo" && git worktree add -q wt-inside >/dev/null 2>&1)
  assert_vcs "git worktree nested inside the jj repository" git \
    "$tmp/colo/wt-inside"

  (cd "$tmp/colo" && git worktree add -q "$tmp/wt-outside" >/dev/null 2>&1)
  assert_vcs "git worktree outside the jj repository" git "$tmp/wt-outside"

  (cd "$tmp/colo" && jj workspace add "$tmp/ws" >/dev/null 2>&1)
  assert_vcs "jj workspace" jj "$tmp/ws"
else
  echo "SKIP: jj not available; plain-git case only"
fi

if [ "$failed" -ne 0 ]; then
  echo "test-vcs.sh: failures ($checked checked)"
  exit 1
fi
echo "test-vcs.sh: all $checked checks passed"
