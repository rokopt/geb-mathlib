#!/usr/bin/env bash
#
# scripts/tests/test-requests.sh
#
# Test of the requests a program makes of its host (geb-kernel interact,
# geb-author interact) on the program of examples/requests/, which reads the
# file an index names and writes it to an output. Asserts that the output is
# the file's bytes; that a missing file is a result the program handles, and
# a missing index ends it with its status 1; that a run without arguments
# ends with the program's status 2; that a step returning no action, and a
# name the program does not define, end the run with status 1 and a message;
# that geb-author runs the program from its manifest alike, and runs an
# entry on a file (geb-author run); and that geb-kernel entries lists the
# manifest's entry points.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build geb-kernel geb-author > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: geb-kernel and geb-author do not build" >&2
  exit 1
}
kernel="$repo_root/.lake/build/bin/geb-kernel"
author="$repo_root/.lake/build/bin/geb-author"
manifest="$repo_root/examples/requests/requests.manifest"

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
  [ "$actual" -eq "$status" ] || fail_case "$name" "exit $actual, expected $status"
}

# same NAME FILE EXPECTED: FILE holds the bytes EXPECTED.
same() {
  checked=$((checked + 1))
  cmp -s "$2" "$3" || fail_case "$1" "$2 differs from $3"
}

cd "$test_dir" || exit 1
"$author" compile "$manifest" program.img || { echo "FAIL: the program does not compile" >&2; exit 1; }

printf 'target λ.txt\nignored\n' > index
printf 'the target\n\0\377' > 'target λ.txt'
expect found 0 "$kernel" interact program.img Index.step index found
same found found 'target λ.txt'

printf 'absent\n' > missing-index
printf 'missing\n' > expected.missing
expect missing 0 "$kernel" interact program.img Index.step missing-index missing
same missing missing expected.missing

expect no-index 1 "$kernel" interact program.img Index.step absent out
checked=$((checked + 1))
[ ! -e out ] || fail_case no-index "an output was written"

expect no-arguments 2 "$kernel" interact program.img Index.step

expect author 0 "$author" interact "$manifest" Index.step index author
same author author 'target λ.txt'

# The client's entry maps a file to a file, so its result is no action of the protocol.
client="$repo_root/examples/client"
mkdir client
cp "$client"/*.geb "$client/client.manifest" client/
ln -s "$repo_root" client/geb
expect no-action 1 "$author" interact client/client.manifest Client.run index
checked=$((checked + 1))
grep -q 'no action of protocol 0' no-action.err || fail_case no-action "$(cat no-action.err)"

expect undefined 1 "$kernel" interact program.img Index.nothing
checked=$((checked + 1))
grep -q 'Index.nothing is not a definition' undefined.err || fail_case undefined "$(cat undefined.err)"

printf 'abc' > input
printf 'abccba' > expected.run
expect run 0 "$author" run client/client.manifest Client.run input run
same run run expected.run

expect entries 0 "$kernel" entries "$manifest"
printf 'Index.step\n' > expected.entries
same entries entries.out expected.entries

if [ "$failed" -ne 0 ]; then
  echo "test-requests: $failed of $checked checks failed" >&2
  exit "$failed"
fi
echo "test-requests: $checked checks passed"
