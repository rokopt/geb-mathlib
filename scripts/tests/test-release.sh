#!/usr/bin/env bash
#
# scripts/tests/test-release.sh
#
# Test of the release of the host executables (scripts/release.sh) and of
# its use by a client (examples/client/fetch-geb.sh). Packages a release
# of this checkout, serves it from a directory as the releases of the Geb
# repository are served, and makes a client from the template that pins
# it. Asserts that the client's fetch places the release at geb/, that the
# client's check.sh compiles, proves and replays with the release's
# executables, that the editor's launcher runs them with no Lake on the
# path, that a digest the archive does not have and a geb/ that is no
# release are refused, leaving geb/ in place, and that a platform the pin
# omits is reported.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

# expect NAME STATUS COMMAND...: the command exits with STATUS.
expect() {
  local name=$1 status=$2
  shift 2
  checked=$((checked + 1))
  "$@" > "$test_dir/$name.out" 2> "$test_dir/$name.err"
  local actual=$?
  [ "$actual" -eq "$status" ] ||
    fail_case "$name" "exit $actual, expected $status: $(tail -3 "$test_dir/$name.err")"
}

version=test-1
platform="$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)"
archive="geb-$version-$platform.tar.gz"
releases="$test_dir/releases"
bash "$repo_root/scripts/release.sh" package "$version" "$releases/$version" \
  > "$test_dir/package.log" 2>&1 || {
  cat "$test_dir/package.log" >&2
  echo "FAIL: scripts/release.sh does not package" >&2
  exit 1
}
export GEB_RELEASE_URL="file://$releases"

client="$test_dir/client λ"
cp -R "$repo_root/examples/client" "$client"
cp "$releases/$version/$archive.sha256" "$client/geb-release.sha256"

expect fetch 0 bash "$client/fetch-geb.sh"
checked=$((checked + 1))
grep -q "\"version\": \"$version\"" "$client/geb/geb-release.json" ||
  fail_case fetch "geb/geb-release.json names no version $version"
expect check 0 bash "$client/check.sh"

# The launcher runs a release's executable in place: a Lake on the path fails if it is run.
mkdir "$test_dir/no-lake"
printf '#!/bin/sh\necho lake was run >&2\nexit 1\n' > "$test_dir/no-lake/lake"
chmod +x "$test_dir/no-lake/lake"
expect launcher 0 env PATH="$test_dir/no-lake:$PATH" \
  bash -c 'cd "$1/geb" && python3 "$2" run geb-kernel entries ../client.manifest' \
  _ "$client" "$repo_root/editors/vscode/tools.py"
checked=$((checked + 1))
entries='Client.mirror\nClient.run\nCopy.step\nSettings.choose\nSettings.apply\nUpgrade.migrate'
[ "$(cat "$test_dir/launcher.out")" = "$(printf "$entries")" ] ||
  fail_case launcher "listed $(cat "$test_dir/launcher.out")"

# A pin whose digest the archive does not have is refused, and geb/ is left in place.
before=$(cat "$client/geb/geb-release.json")
sed -i -E "s/^[0-9a-f]{64}/$(printf '0%.0s' $(seq 64))/" "$client/geb-release.sha256"
expect tampered 1 bash "$client/fetch-geb.sh"
checked=$((checked + 1))
[ "$(cat "$client/geb/geb-release.json")" = "$before" ] || fail_case tampered "geb/ changed"

# A pin naming no archive of this platform is reported.
sed "s/-$platform\.tar\.gz/-elsewhere.tar.gz/" "$releases/$version/$archive.sha256" \
  > "$client/geb-release.sha256"
expect platform 1 bash "$client/fetch-geb.sh"
checked=$((checked + 1))
grep -q "pins no release for $platform" "$test_dir/platform.err" ||
  fail_case platform "$(cat "$test_dir/platform.err")"

# A geb/ that is no release, a checkout or a submodule, is left in place.
cp "$releases/$version/$archive.sha256" "$client/geb-release.sha256"
rm -rf "$client/geb"
ln -s "$repo_root" "$client/geb"
expect checkout 1 bash "$client/fetch-geb.sh"
checked=$((checked + 1))
[ -L "$client/geb" ] || fail_case checkout "geb/ was replaced"

if [ "$failed" -ne 0 ]; then
  echo "test-release: $failed of $checked checks failed" >&2
  exit "$failed"
fi
echo "test-release: $checked checks passed"
