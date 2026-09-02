#!/usr/bin/env bash
#
# scripts/tests/test-diff-against-main.sh
#
# Regression test for scripts/lib/diff-against-main.sh. Under jj,
# asserts that the primary merge-base revset parses under the active
# jj — a renamed or removed revset function would otherwise fall
# through to the fallback silently (the defect this test exists to
# catch) — and that diff_against_main lists a file changed on a
# branch off main. Under git, asserts the latter alone.
#
# The jj checks skip cleanly when jj is unavailable (e.g. a CI job
# that does not install jj); the git checks always run.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source-path=SCRIPTDIR
# shellcheck source=../lib/diff-against-main.sh
source "$here/../lib/diff-against-main.sh"

failed=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# A throwaway git repo: a `main` commit, then a branch adding a file.
mkdir "$tmp/git-repo"
cd "$tmp/git-repo" || exit 1
git init -q -b main
git -c user.name=test -c user.email=test@example.com \
  commit -q --allow-empty -m base
git checkout -q -b topic
echo changed > changed.txt
git add changed.txt

out="$(diff_against_main)"
if ! printf '%s\n' "$out" | grep -qx 'changed.txt'; then
  echo "FAIL: under git, diff_against_main missing changed.txt; got: $out"
  failed=1
fi

if command -v jj >/dev/null 2>&1; then
  # jj reads the committer identity from these environment variables.
  export JJ_USER="test" JJ_EMAIL="test@example.com"

  # A throwaway jj repo: a `main` commit, then a child @ adding a
  # file, so fork_point(main | @) has a non-trivial answer.
  mkdir "$tmp/jj-repo"
  cd "$tmp/jj-repo" || exit 1
  jj git init >/dev/null 2>&1
  echo base > base.txt
  jj describe -m base >/dev/null 2>&1
  jj bookmark create main -r @ >/dev/null 2>&1
  jj new >/dev/null 2>&1
  echo changed > changed.txt

  # 1. The primary revset must parse (rc 0) under the active jj.
  if ! jj log --no-graph -r "$DIFF_AGAINST_MAIN_PRIMARY_REVSET" \
         -T 'change_id.short() ++ "\n"' >/dev/null 2>&1; then
    echo "FAIL: primary revset does not parse under $(jj --version)"
    failed=1
  fi

  # 2. diff_against_main lists the file added on the branch.
  out="$(diff_against_main)"
  if ! printf '%s\n' "$out" | grep -qx 'changed.txt'; then
    echo "FAIL: under jj, diff_against_main missing changed.txt; got: $out"
    failed=1
  fi
else
  echo "SKIP: jj not available; git checks only"
fi

if [ "$failed" -ne 0 ]; then
  echo "test-diff-against-main.sh: failures"
  exit 1
fi
echo "test-diff-against-main.sh: all checks passed"
