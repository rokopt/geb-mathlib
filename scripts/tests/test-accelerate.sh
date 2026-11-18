#!/usr/bin/env bash
#
# scripts/tests/test-accelerate.sh
#
# Smoke test for scripts/accelerate.py, which binds the accelerations of a
# table in emitted Lean. Stages a module of two definitions and a table
# naming one of them under a temp directory and asserts that the named
# definition is bound to the function run in its place, with the module
# declaring it imported, the other definition left as it is; that
# GEB_ACCELERATION selects the function that runs both, or no binding;
# that a file defining none of the names is untouched; and that a
# malformed table and an unknown mode are rejected.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT
bind="$repo_root/scripts/accelerate.py"

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

cd "$test_dir" || exit 1
unset GEB_ACCELERATION

printf '%s\n' 'module' '' 'public import First' '' 'namespace N' '' \
  'def «A.f» :=' '  fun (x0 : T) =>' '    x0' '' 'def «A.g» :=' '  fun (x0 : T) =>' '    x0' '' \
  'end N' '' 'end' > raw.lean
printf '%s\n' '# a comment' 'A.g Fast.g Fast.gShadow Fast.Module' > table

printf '%s\n' 'module' '' 'public import First' 'public import Fast.Module' '' 'namespace N' '' \
  'def «A.f» :=' '  fun (x0 : T) =>' '    x0' '' \
  'def «A.g$geb» :=' '  fun (x0 : T) =>' '    x0' '' \
  'def «A.g$accel» : type_of% «A.g$geb» :=' '  Fast.g «A.g$geb»' '' \
  '@[implemented_by «A.g$accel»]' 'def «A.g» :=' '  fun (x0 : T) =>' '    x0' '' \
  'end N' '' 'end' > expected.lean

checked=$((checked + 1))
cp raw.lean bound.lean
python3 "$bind" --table table bound.lean || fail_case bound "exit $?"
cmp -s bound.lean expected.lean || fail_case bound "the definition is not bound as documented"

checked=$((checked + 1))
cp raw.lean shadow.lean
GEB_ACCELERATION=shadow python3 "$bind" --table table shadow.lean || fail_case shadow "exit $?"
sed 's/  Fast\.g «/  Fast.gShadow «/' expected.lean | cmp -s - shadow.lean \
  || fail_case shadow "the function that runs both is not bound"

checked=$((checked + 1))
cp raw.lean none.lean
GEB_ACCELERATION=none python3 "$bind" --table table none.lean || fail_case none "exit $?"
cmp -s none.lean raw.lean || fail_case none "the file is changed"

checked=$((checked + 1))
printf '%s\n' 'module' '' 'public import First' '' 'def «B.h» :=' '  x' '' 'end' > other.lean
cp other.lean other.before
python3 "$bind" --table table other.lean || fail_case other "exit $?"
cmp -s other.lean other.before || fail_case other "a file defining none of the names is changed"

checked=$((checked + 1))
printf '%s\n' 'A.g Fast.g' > short
cp raw.lean malformed.lean
python3 "$bind" --table short malformed.lean 2> err && fail_case malformed "a short line is accepted"
grep -q 'malformed line' err || fail_case malformed "the reason is not reported"
cmp -s malformed.lean raw.lean || fail_case malformed "the file is changed"

checked=$((checked + 1))
cp raw.lean mode.lean
GEB_ACCELERATION=fast python3 "$bind" --table table mode.lean 2> err \
  && fail_case mode "an unknown mode is accepted"
grep -q 'GEB_ACCELERATION' err || fail_case mode "the reason is not reported"
cmp -s mode.lean raw.lean || fail_case mode "the file is changed"

if [ "$failed" -ne 0 ]; then
  echo "test-accelerate: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-accelerate: $checked scenario(s) passed"
