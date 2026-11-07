#!/usr/bin/env bash
#
# scripts/tests/test-geb-compile.sh
#
# Smoke test for the failures geb-compile reports. Stages programs under
# a temp directory that one stage of the compiler rejects, and asserts for
# each that the driver exits 1, names what rejects the program on standard
# error and leaves an existing output untouched, and that a program the
# compiler accepts is written, through both entry points.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build geb-compile > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: geb-compile does not build" >&2
  exit 1
}
compiler="$repo_root/.lake/build/bin/geb-compile"

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

# Compile the source; assert that the driver exits 1, that its message
# holds the substring, and that the existing output keeps its bytes.
assert_rejected() {
  local name="$1" source="$2" expected="$3"
  checked=$((checked + 1))
  printf '%s\n' "$source" > "$test_dir/$name.geb"
  printf 'kept' > "$test_dir/$name.out"
  local output exit_code
  output="$("$compiler" image "$test_dir/$name.geb" "$test_dir/$name.out" 2>&1)"
  exit_code=$?
  [ "$exit_code" -eq 1 ] || fail_case "$name" "exit $exit_code, expected 1"
  case "$output" in
    *"$name.geb: "*"$expected"*) ;;
    *) fail_case "$name" "message '$output' lacks '$expected'" ;;
  esac
  [ "$(cat "$test_dir/$name.out")" = kept ] || fail_case "$name" "the output was changed"
}

# Compile the source through an entry point; assert that the driver exits
# 0, reports nothing and writes a nonempty output.
assert_compiled() {
  local name="$1" mode="$2" source="$3"
  checked=$((checked + 1))
  printf '%s\n' "$source" > "$test_dir/$name.geb"
  local output exit_code
  output="$("$compiler" "$mode" "$test_dir/$name.geb" "$test_dir/$name.out" 2>&1)"
  exit_code=$?
  [ "$exit_code" -eq 0 ] || fail_case "$name" "exit $exit_code, expected 0"
  [ -z "$output" ] || fail_case "$name" "unexpected message '$output'"
  [ -s "$test_dir/$name.out" ] || fail_case "$name" "the output is empty"
}

nat='(data Nat (zero) (succ Nat))'

assert_rejected unbalanced '(def f (lam ((x T)) x)' 'parentheses do not balance'
assert_rejected reserved '(def "%x" (lam ((x T)) x))' 'begins with %'
assert_rejected exports '(module M (export nope) (def f (lam ((x T)) x)))' 'the export nope'
assert_rejected duplicate '(def f (lam ((x T)) x)) (def f (lam ((x T)) x))' 'f is reserved'
assert_rejected typing "$nat (def g (lam ((t T)) (succ t)))" 'g does not check'
assert_rejected unresolved '(def f (lam ((x T)) y))' 'f does not check'
assert_rejected template \
  '(module M (parameter A) (export f) (def f (lam ((x A)) (label x))))' \
  "M.f does not check at its template's opaque parameters"
assert_rejected expansion "(data N (z)) (def f (lam ((x N)) (case x ((z) 0) (else))))" \
  'f does not expand'

assert_compiled image image '(def f (lam ((x T)) x))'
assert_compiled lean lean "$nat (def h (lam ((n Nat)) (label (rep n))))"

checked=$((checked + 1))
"$compiler" > "$test_dir/usage.log" 2>&1
[ $? -eq 2 ] || fail_case usage "exit status is not 2"
grep -q '^usage: geb-compile' "$test_dir/usage.log" || fail_case usage "no usage message"

if [ "$failed" -ne 0 ]; then
  echo "test-geb-compile: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-geb-compile: $checked scenario(s) passed"
