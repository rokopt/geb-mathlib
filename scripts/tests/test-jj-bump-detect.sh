#!/usr/bin/env bash
#
# scripts/tests/test-jj-bump-detect.sh
#
# Smoke test for scripts/jj-bump-detect.sh. Sources the script
# (whose main is guarded) and exercises its pure logic: pin read
# (read_jj_pin), version selection and v-strip normalization
# (select_target, strip_v), and the latest-release predicates fed
# canned JSON (release_tag, release_has_asset). The network-bound
# IO wrappers are covered by a live workflow_dispatch run, not
# here.
#
# select_target uses `npx semver`, so this test requires network.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=scripts/jj-bump-detect.sh
source "$repo_root/scripts/jj-bump-detect.sh"

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

assert_status() {
  local name="$1" expected="$2" actual="$3"
  checked=$((checked + 1))
  if [[ "$actual" -ne "$expected" ]]; then
    echo "FAIL: $name: expected status $expected, got $actual" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

# Version selection: bare pin against the v-prefixed release tag.
assert_eq "newer release is selected" "v0.43.0" \
  "$(printf 'v0.43.0\n' | select_target 0.42.0)"
assert_eq "equal release yields empty" "" \
  "$(printf 'v0.42.0\n' | select_target 0.42.0)"
assert_eq "older release yields empty" "" \
  "$(printf 'v0.41.0\n' | select_target 0.42.0)"

# v-strip normalization: scripts/jj-version stores the bare
# version and scripts/install-jj.sh prepends the v itself.
assert_eq "strip_v drops a leading v" "0.43.0" "$(strip_v v0.43.0)"
assert_eq "strip_v passes bare versions through" "0.43.0" \
  "$(strip_v 0.43.0)"

# Pin read: whitespace-tolerant, matching install-jj.sh.
fixture="$(mktemp)"
trap 'rm -f "$fixture"' EXIT
printf '0.42.0\n' > "$fixture"
assert_eq "reads the bare pin" "0.42.0" "$(read_jj_pin "$fixture")"

# Canned latest-release JSON for the stdin-fed predicates.
release_json='{
  "tag_name": "v0.43.0",
  "assets": [
    {"name": "jj-v0.43.0-aarch64-apple-darwin.tar.gz"},
    {"name": "jj-v0.43.0-x86_64-unknown-linux-musl.tar.gz"}
  ]
}'

assert_eq "release_tag extracts tag_name" "v0.43.0" \
  "$(release_tag <<<"$release_json")"

release_has_asset 0.43.0 <<<"$release_json"
assert_status "musl asset present" 0 "$?"
release_has_asset 0.44.0 <<<"$release_json"
assert_status "musl asset absent for other version" 1 "$?"

echo ""
echo "test-jj-bump-detect.sh: $checked case(s) checked, $failed failure(s)"
exit "$failed"
