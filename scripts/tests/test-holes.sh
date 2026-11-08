#!/usr/bin/env bash
#
# scripts/tests/test-holes.sh
#
# Smoke test for geb-kernel holes, the check of a program with holes.
# Asserts that a program with an open hole prints the hole's expected type
# and context and exits with status 2, from its sources and from its
# manifest; that a program without holes prints that it is complete and
# exits with status 0; and that an ill-typed program is rejected with
# status 1, naming the definition.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build geb-kernel > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: geb-kernel does not build" >&2
  exit 1
}
kernel="$repo_root/.lake/build/bin/geb-kernel"

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

cd "$test_dir" || exit 1
doc='(document (syntax authoring 0) (schema 0) (prose verso 0))'
printf '; a hole\n(def g 5)\n(def f (lam (x T) (add ?a g)))\n' > open.geb
printf '%s\n' "(program p (edition 0) $doc (sources open.geb) (entries f))" > open.manifest
printf '(?a T)\n  (x T)\n' > expected.open

for form in "open.geb" "--manifest open.manifest"; do
  checked=$((checked + 1))
  # shellcheck disable=SC2086 # the form is two words for the manifest
  "$kernel" holes $form > got.open
  status=$?
  [ "$status" -eq 2 ] || fail_case "open $form" "exit status $status is not 2"
  cmp -s got.open expected.open || fail_case "open $form" "the obligation is not displayed"
done

checked=$((checked + 1))
printf '(def f (lam (x T) x))\n' > complete.geb
"$kernel" holes complete.geb > got.complete
status=$?
[ "$status" -eq 0 ] || fail_case complete "exit status $status is not 0"
[ "$(cat got.complete)" = complete ] || fail_case complete "the program is not reported complete"

checked=$((checked + 1))
printf '(def f (lam (x T) (add ?a unit)))\n' > illtyped.geb
"$kernel" holes illtyped.geb > /dev/null 2> got.illtyped
status=$?
[ "$status" -eq 1 ] || fail_case ill-typed "exit status $status is not 1"
grep -q 'f is ill-typed' got.illtyped || fail_case ill-typed "the definition is not named"

if [ "$failed" -ne 0 ]; then
  echo "test-holes: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-holes: $checked scenario(s) passed"
