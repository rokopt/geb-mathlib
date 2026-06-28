#!/usr/bin/env bash
#
# scripts/tests/test-diff-against-main.sh
#
# Regression test for scripts/lib/diff-against-main.sh. Asserts that
# the primary merge-base revset parses under the active jj — a
# renamed or removed revset function would otherwise fall through to
# the fallback silently (the defect this test exists to catch) — and
# that diff_against_main lists a file changed on a branch off main.
#
# Skips cleanly when jj is unavailable (e.g. a CI job that does not
# install jj).

set -uo pipefail

if ! command -v jj >/dev/null 2>&1; then
  echo "SKIP: jj not available"
  exit 0
fi

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source-path=SCRIPTDIR
# shellcheck source=../lib/diff-against-main.sh
source "$here/../lib/diff-against-main.sh"

failed=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# jj reads the committer identity from these environment variables.
export JJ_USER="test" JJ_EMAIL="test@example.com"

# Build a throwaway repo: a `main` commit, then a child @ adding a
# file, so fork_point(main | @) has a non-trivial answer.
cd "$tmp" || exit 1
jj git init >/dev/null 2>&1
echo base > base.txt
jj describe -m base >/dev/null 2>&1
jj bookmark create main -r @ >/dev/null 2>&1
jj new >/dev/null 2>&1
echo changed > changed.txt

# 1. The primary revset must parse (rc 0) under the active jj.
if jj log --no-graph -r "$DIFF_AGAINST_MAIN_PRIMARY_REVSET" \
     -T 'change_id.short() ++ "\n"' >/dev/null 2>&1; then
  echo "PASS: primary revset parses ($DIFF_AGAINST_MAIN_PRIMARY_REVSET)"
else
  echo "FAIL: primary revset does not parse under $(jj --version)"
  failed=1
fi

# 2. diff_against_main lists the file added on the branch.
out="$(diff_against_main)"
if printf '%s\n' "$out" | grep -qx 'changed.txt'; then
  echo "PASS: diff_against_main lists the changed file"
else
  echo "FAIL: diff_against_main missing changed.txt; got: $out"
  failed=1
fi

if [ "$failed" -ne 0 ]; then
  echo "test-diff-against-main.sh: failures"
  exit 1
fi
echo "test-diff-against-main.sh: all checks passed"
