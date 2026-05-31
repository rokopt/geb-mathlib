#!/usr/bin/env bash
#
# scripts/tests/test-mathlib-bump-detect.sh
#
# Smoke test for scripts/mathlib-bump-detect.sh. Sources the script
# (whose main is guarded) and exercises its pure logic: tag
# selection (select_target, via the npm semver package) and the
# TOML-aware pin read (read_mathlib_pin). The network-bound IO
# wrappers are covered by the live workflow_dispatch run, not here.
#
# select_target uses `npx semver`, so this test requires network.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/mathlib-bump-detect.sh
source "$repo_root/scripts/mathlib-bump-detect.sh"

failed=0
checked=0

assert_eq() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL: $name: expected [$expected], got [$actual]" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

assert_eq "newer rc is selected" "v4.31.0-rc1" \
  "$(printf 'v4.30.0-rc2\nv4.31.0-rc1\n' | select_target v4.30.0-rc2)"
assert_eq "no newer tag yields empty" "" \
  "$(printf 'v4.30.0-rc1\nv4.30.0-rc2\n' | select_target v4.30.0-rc2)"
assert_eq "stable outranks its rc" "v4.31.0" \
  "$(printf 'v4.31.0-rc1\nv4.31.0\n' | select_target v4.31.0-rc1)"
assert_eq "pin already newest yields empty" "" \
  "$(printf 'v4.31.0-rc1\n' | select_target v4.31.0-rc1)"

fixture="$(mktemp)"
trap 'rm -f "$fixture"' EXIT
cat > "$fixture" <<'TOML'
[[require]]
name = "cslib"
rev = "v4.29.0"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.30.0-rc2"
TOML
assert_eq "reads the mathlib pin, not cslib" "v4.30.0-rc2" \
  "$(read_mathlib_pin "$fixture")"

echo ""
echo "test-mathlib-bump-detect.sh: $checked case(s) checked, $failed failure(s)"
exit "$failed"
