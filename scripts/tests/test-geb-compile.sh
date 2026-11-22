#!/usr/bin/env bash
#
# scripts/tests/test-geb-compile.sh
#
# Smoke test for the failures geb-compile reports. Stages programs under
# a temp directory that one stage of the compiler rejects, and asserts for
# each that the driver exits 1, reports on standard error the diagnostic
# FILE:LINE:COLUMN: error: MESSAGE at the occurrence that rejects the
# program and leaves an existing output untouched, and that a program the
# compiler accepts is written, through both entry points. Asserts that
# `check` reports the same diagnostics and writes nothing, and that it
# compiles the sources of the nearest manifest listing a source, up to
# that source.
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

# Compile the source; assert that the driver exits 1, that its diagnostic
# is at the line and column and holds the substring, and that the existing
# output keeps its bytes; and that `check` reports the same diagnostic.
assert_rejected() {
  local name="$1" source="$2" at="$3" expected="$4"
  checked=$((checked + 1))
  printf '%s\n' "$source" > "$test_dir/$name.geb"
  printf 'kept' > "$test_dir/$name.out"
  local output exit_code checked_output
  output="$("$compiler" image "$test_dir/$name.geb" "$test_dir/$name.out" 2>&1)"
  exit_code=$?
  [ "$exit_code" -eq 1 ] || fail_case "$name" "exit $exit_code, expected 1"
  case "$output" in
    "$test_dir/$name.geb:$at: error: "*"$expected"*) ;;
    *) fail_case "$name" "message '$output' lacks '$name.geb:$at: error: ' or '$expected'" ;;
  esac
  [ "$(cat "$test_dir/$name.out")" = kept ] || fail_case "$name" "the output was changed"
  checked_output="$("$compiler" check "$test_dir/$name.geb" 2>&1)"
  [ $? -eq 1 ] || fail_case "$name" "check does not exit 1"
  [ "$checked_output" = "$output" ] ||
    fail_case "$name" "check reports '$checked_output', not '$output'"
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

assert_rejected unbalanced '(def f (lam ((x T)) x)' 1:1 'a parenthesis is not closed'
assert_rejected closing '(def f (lam ((x T)) x)))' 1:24 'a closing parenthesis closes nothing'
assert_rejected atom "(def f (lam ((x T)) x))
(def g \"abc)" 2:8 'the text ends inside this atom'
assert_rejected reserved '(def f (lam ((x T)) x))
(def "%x" (lam ((x T)) x))' 2:6 'begins with %'
assert_rejected exports '; a comment
(module M (export nope) (def f (lam ((x T)) x)))' 2:9 'the export nope'
assert_rejected duplicate '(def f (lam ((x T)) x))
  (def f (lam ((x T)) x))' 2:8 'f is reserved'
assert_rejected typing "$nat

(def g (lam ((t T)) (succ t)))" 3:6 'g does not check'
assert_rejected unresolved '(def f (lam ((x T)) y))' 1:6 'f does not check'
assert_rejected template \
  '(module M (parameter A) (export f)
  ; a comment before the declaration
  (def f (lam ((x A)) (label x))))' 3:8 \
  "M.f does not check at its template's opaque parameters"
assert_rejected nested '(module A (export g)
  (module B (export f) (def f (lam ((x T)) x)))
  (def g (lam ((x T)) (B.f y))))' 3:8 'A.g does not check'
assert_rejected expansion "(data N (z)) (def f (lam ((x N)) (case x ((z) 0) (else))))" 1:19 \
  'f does not expand'

# Kernel typing points to the operand, with binder contexts and source desugaring respected.
assert_rejected function '(def f (lam ((x T)) (x 0)))' 1:22 'expected a function type, got T'
assert_rejected argument '(def f (label (nil T)))' 1:15 'expected T, got (List T)'
assert_rejected projection '(def f (fst 0))' 1:13 'expected a product type, got T'
assert_rejected condition '(def f (if (nil T) 0 1))' 1:12 'expected T, got (List T)'
assert_rejected branches '(def f (if 1 0 (nil T)))' 1:16 'expected T, got (List T)'
assert_rejected element '(def f (cons (nil T) (nil T)))' 1:14 'expected T, got (List T)'
assert_rejected tail '(def f (cons 0 1))' 1:16 'expected a list type, got T'
assert_rejected binding '(def f (let x T (nil T) x))' 1:17 'expected T, got (List T)'
assert_rejected shadowing '(def f (lam ((x T)) (lam ((x (List T))) (label x))))' 1:48 \
  'expected T, got (List T)'
assert_rejected signature '(defn f ((x T)) (List T) x)' 1:26 'expected (List T), got T'
assert_rejected nested-typing '(module M (export f) (def f (label (nil T))))' 1:36 \
  'expected T, got (List T)'
assert_rejected duplicate-terms '(def f (pair (label 0) (label (nil T))))' 1:31 \
  'expected T, got (List T)'
assert_rejected alias '(deftype Ts (List T))
(def f (lam ((xs Ts)) (label xs)))' 2:30 'expected T, got (List T)'
assert_rejected global '(def xs (nil T))
(def f (label xs))' 2:15 'expected T, got (List T)'
assert_rejected bytes $'; λ\r\n(def f (pair (quote (0 "λ")) (label (nil T))))' 2:38 \
  'expected T, got (List T)'

# A failure at the bottom of a deeply nested term is reported in the time of the term: each
# subterm is checked once.
deep() {
  local inner="$1" open="$2" close="$3" e="$1" i
  for i in $(seq 1 60); do e="$open$e$close"; done
  printf '%s' "$e"
}
checked=$((checked + 1))
printf '(def f %s)\n' "$(deep '(nil T)' '(add 1 ' ')')" > "$test_dir/deep-kernel.geb"
output="$(timeout 60 "$compiler" check "$test_dir/deep-kernel.geb" 2>&1)"
[ $? -eq 1 ] || fail_case deep-kernel "check does not exit 1 within a minute"
case "$output" in
  *"deep-kernel.geb:1:428: error: f does not check: expected T, got (List T)") ;;
  *) fail_case deep-kernel "message '$output' does not locate the innermost operand" ;;
esac

assert_compiled image image '(def f (lam ((x T)) x))'
assert_compiled quotation image '(def f (quote (11 (0 2) (99))))'
assert_compiled lean lean "$nat (def h (lam ((n Nat)) (label (rep n))))"

# `check` writes nothing for a program the compiler accepts.
checked=$((checked + 1))
output="$("$compiler" check "$test_dir/image.geb" 2>&1)"
[ $? -eq 0 ] || fail_case check "exit status is not 0 for an accepted program"
[ -z "$output" ] || fail_case check "unexpected message '$output'"

# A source a manifest lists is checked with the sources before it, and a
# failure is reported in the source that holds it; the sources after it
# are not read. The manifest is sought from the source's directory upward.
doc='(document (syntax authoring 0) (schema 0) (prose verso 0))'
mkdir -p "$test_dir/p/sub"
printf '(def f (lam ((x T)) x))\n' > "$test_dir/p/a.geb"
printf '(def g (lam ((x T)) (f x)))\n' > "$test_dir/p/sub/b.geb"
printf '(def h (lam ((x T)) (nope x)))\n' > "$test_dir/p/c.geb"
printf '%s\n' "(program p (edition 0) $doc (sources a.geb sub/b.geb c.geb) (entries))" \
  > "$test_dir/p/p.manifest"

checked=$((checked + 1))
output="$("$compiler" check "$test_dir/p/sub/b.geb" 2>&1)"
[ $? -eq 0 ] || fail_case prefix "a source is not checked after those before it: '$output'"

checked=$((checked + 1))
output="$("$compiler" check "$test_dir/p/c.geb" 2>&1)"
[ $? -eq 1 ] || fail_case later "exit status is not 1"
case "$output" in
  "$test_dir/p/c.geb:1:6: error: h does not check") ;;
  *) fail_case later "message '$output' does not locate h" ;;
esac

checked=$((checked + 1))
output="$("$compiler" check --manifest "$test_dir/p/p.manifest" 2>&1)"
[ $? -eq 1 ] || fail_case manifest "exit status is not 1"
case "$output" in
  "$test_dir/p/c.geb:1:6: error: h does not check") ;;
  *) fail_case manifest "message '$output' does not locate h" ;;
esac

checked=$((checked + 1))
printf '(def f (lam ((x T)) (nope x)))\n' > "$test_dir/p/a.geb"
output="$("$compiler" check "$test_dir/p/sub/b.geb" 2>&1)"
[ $? -eq 1 ] || fail_case earlier "exit status is not 1"
case "$output" in
  "$test_dir/p/a.geb:1:6: error: f does not check") ;;
  *) fail_case earlier "message '$output' does not locate f in the earlier source" ;;
esac

# An entry the program does not define has no occurrence in a source.
checked=$((checked + 1))
printf '(def f (lam ((x T)) x))\n' > "$test_dir/p/a.geb"
printf '%s\n' "(program q (edition 0) $doc (sources a.geb) (entries main))" \
  > "$test_dir/p/q.manifest"
output="$("$compiler" check --manifest "$test_dir/p/q.manifest" 2>&1)"
[ $? -eq 1 ] || fail_case entry "exit status is not 1"
case "$output" in
  "$test_dir/p/q.manifest: "*main*) ;;
  *) fail_case entry "message '$output' does not name the manifest and the entry" ;;
esac

checked=$((checked + 1))
"$compiler" > "$test_dir/usage.log" 2>&1
[ $? -eq 2 ] || fail_case usage "exit status is not 2"
grep -q '^usage: geb-compile' "$test_dir/usage.log" || fail_case usage "no usage message"

if [ "$failed" -ne 0 ]; then
  echo "test-geb-compile: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-geb-compile: $checked scenario(s) passed"
