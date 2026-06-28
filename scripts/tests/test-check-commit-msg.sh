#!/usr/bin/env bash
#
# scripts/tests/test-check-commit-msg.sh
#
# Tests scripts/check-commit-msg.sh against conforming and
# non-conforming commit subjects.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="$here/../check-commit-msg.sh"

failed=0

accept() { # name subject
  if printf '%s\n' "$2" | bash "$SCRIPT" >/dev/null 2>&1; then
    echo "PASS [accept]: $1"
  else
    echo "FAIL [accept]: $1 -- '$2' rejected"
    failed=1
  fi
}
reject() { # name subject
  if printf '%s\n' "$2" | bash "$SCRIPT" >/dev/null 2>&1; then
    echo "FAIL [reject]: $1 -- '$2' accepted"
    failed=1
  else
    echo "PASS [reject]: $1"
  fi
}

# Conforming.
accept "type only"            'feat: add presheaf functor'
accept "type with scope"      'fix(scripts): close git-hook bypasses'
accept "ci type"              'ci: harden workflows'
accept "doc type"            'doc: explain the floodgate test'
# shellcheck disable=SC2016  # backticks here are literal test data
accept "backtick-initial subject" 'refactor: `lake` glob handling'
accept "scope with slash"     'chore(ci/workflow): pin action'
accept "colon in subject"     'fix(scripts): handle a: b correctly'

# Skipped lines (treated as conforming — not our commits to gate).
accept "merge commit skipped" 'Merge pull request #46 from rokopt/fix/x'
accept "bot commit skipped"   '[create-pull-request] automated change'

# Non-conforming.
reject "no type"              'add presheaf functor'
reject "capitalised subject"  'feat: Add presheaf functor'
reject "trailing period"      'feat: add presheaf functor.'
reject "unknown type"         'feature: add presheaf functor'
reject "missing colon-space"  'feat add presheaf functor'
reject "empty subject"        'feat: '
reject "capitalised no-type (PR #45 regression)" 'Rename polynomial positions to directions'

# A multi-line batch with one bad subject fails overall.
if printf '%s\n%s\n' 'feat: ok one' 'Bad two' | bash "$SCRIPT" >/dev/null 2>&1; then
  echo "FAIL [batch]: a batch containing a violation was accepted"
  failed=1
else
  echo "PASS [batch]: batch with a violation rejected"
fi

if [ "$failed" -ne 0 ]; then
  echo "test-check-commit-msg.sh: failures"
  exit 1
fi
echo "test-check-commit-msg.sh: all checks passed"
