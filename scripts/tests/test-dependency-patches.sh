#!/usr/bin/env bash
#
# scripts/tests/test-dependency-patches.sh
#
# Regression test for scripts/lib/dependency-patches.sh against a
# fixture dependency under .lake/packages/: apply_dependency_patches
# applies a patch, skips it once applied, and fails, leaving the
# dependency unchanged, when the dependency's patched lines differ
# from the patch's context.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source-path=SCRIPTDIR
# shellcheck source=../lib/dependency-patches.sh
source "$here/../lib/dependency-patches.sh"

failed=0
checked=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

dep="$tmp/.lake/packages/dep"
mkdir -p "$dep" "$tmp/scripts/patches/dep"
(cd "$dep" && git init -q -b main && echo one > file \
   && git add file \
   && git -c user.name=test -c user.email=test@example.com \
        commit -q -m base \
   && echo two > file && git diff > "$tmp/scripts/patches/dep/fix.patch" \
   && git checkout -q -- file)

# assert_run <name> <expected status> <expected file contents>:
# apply_dependency_patches run from the fixture root exits with the
# expected status and leaves the dependency's file as expected.
assert_run() {
  local name="$1" status="$2" contents="$3" got_status got_contents
  checked=$((checked + 1))
  (cd "$tmp" && apply_dependency_patches) >/dev/null 2>&1
  got_status=$?
  got_contents="$(cat "$dep/file")"
  if [ "$got_status" -ne "$status" ] || [ "$got_contents" != "$contents" ]; then
    echo "FAIL: $name: expected status $status and '$contents'," \
      "got status $got_status and '$got_contents'"
    failed=1
  fi
}

assert_run "patch applies" 0 two
assert_run "applied patch is skipped" 0 two
(cd "$dep" && echo three > file)
assert_run "changed dependency fails the run" 1 three

if [ "$failed" -ne 0 ]; then
  echo "test-dependency-patches.sh: failures ($checked checked)"
  exit 1
fi
echo "test-dependency-patches.sh: all $checked checks passed"
