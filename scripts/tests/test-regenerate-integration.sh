#!/usr/bin/env bash
#
# scripts/tests/test-regenerate-integration.sh
#
# Smoke test for scripts/regenerate-integration.sh. Sources the
# script (whose `main` is guarded) and exercises the pure conflict
# check `working_copy_has_conflicts` against constructed jj repos:
# a fan-in with a textual conflict (the guard must fire) and a
# clean commit (the guard must stay silent). The network IO
# (fetch, push, ci dispatch) is covered by the live workflow run,
# not here.
#
# Requires `jj` on PATH (the project's working VCS).

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/regenerate-integration.sh
source "$repo_root/scripts/regenerate-integration.sh"

failed=0
checked=0

assert() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [ "$actual" != "$expected" ]; then
    echo "FAIL: $name: expected [$expected], got [$actual]" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

jj git init "$work/repo" >/dev/null 2>&1
jjr() {
  jj -R "$work/repo" \
     --config user.name=test \
     --config user.email=test@example.invalid "$@"
}

# Two children of `base` edit the same line differently; their
# fan-in is a two-sided conflict on f.txt.
printf 'base\n' > "$work/repo/f.txt"
jjr describe -m base >/dev/null
jjr bookmark create base -r @ >/dev/null
jjr new base -m side-a >/dev/null
printf 'a\n' > "$work/repo/f.txt"
jjr bookmark create side-a -r @ >/dev/null
jjr new base -m side-b >/dev/null
printf 'b\n' > "$work/repo/f.txt"
jjr bookmark create side-b -r @ >/dev/null
jjr new side-a side-b -m fanin >/dev/null 2>&1

# working_copy_has_conflicts evaluates the ambient `jj` against the
# current directory, so call it from inside the repo.
conflicted=no
( cd "$work/repo" && working_copy_has_conflicts ) && conflicted=yes
assert "conflicted fan-in is detected" "yes" "$conflicted"

jjr new base -m clean >/dev/null
clean=no
( cd "$work/repo" && working_copy_has_conflicts ) && clean=yes
assert "clean commit is not flagged" "no" "$clean"

echo ""
echo "test-regenerate-integration.sh: $checked case(s) checked," \
     "$failed failure(s)"
exit "$failed"
