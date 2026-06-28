#!/usr/bin/env bash
#
# scripts/check-commit-msg.sh
#
# Validate commit subject lines against the project's mathlib-derived
# convention (docs/rules/ci-and-workflow.md § Commit-message
# convention): `<type>(<optional-scope>): <subject>` with type in the
# allowed set, a subject that does not start with a capital letter and
# does not end with a period. Reads subjects one per line from stdin;
# merge commits (`Merge ...`) and the create-pull-request bot subject
# are skipped. Exits non-zero if any subject violates the convention.
#
# jj does not run git commit hooks, so this is invoked over a commit
# range by pre-push.sh and by CI rather than as a per-commit hook.
# Imperative mood is not machine-checkable and is left to review; an
# over-72-character subject warns but does not fail (the convention
# states a target, not a hard limit).

set -uo pipefail

types='feat|fix|doc|style|refactor|test|chore|perf|ci'
failed=0
checked=0

while IFS= read -r subject; do
  [ -z "$subject" ] && continue
  case "$subject" in
    "Merge "*) continue ;;
    "[create-pull-request]"*) continue ;;
  esac
  checked=$((checked + 1))
  if ! printf '%s' "$subject" | grep -qE "^(${types})(\([^)]+\))?: .+"; then
    echo "FAIL: not '<type>(<scope>): <subject>' with type in {${types}}: $subject" >&2
    failed=1
    continue
  fi
  body="${subject#*: }"
  case "$body" in
    [A-Z]*)
      echo "FAIL: subject must not start with a capital letter: $subject" >&2
      failed=1
      ;;
  esac
  case "$body" in
    *.)
      echo "FAIL: subject must not end with a period: $subject" >&2
      failed=1
      ;;
  esac
  if [ "${#subject}" -gt 72 ]; then
    echo "WARN: subject exceeds 72 characters (${#subject}): $subject" >&2
  fi
done

if [ "$failed" -ne 0 ]; then
  echo "check-commit-msg: $checked subject(s) checked, violations found" >&2
  exit 1
fi
echo "check-commit-msg: $checked subject(s) checked, all conform"
