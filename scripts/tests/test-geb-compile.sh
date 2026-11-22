#!/usr/bin/env bash
#
# scripts/tests/test-geb-compile.sh
#
# Smoke test for the failures geb-compile reports. Stages programs under
# a temp directory that one stage of the compiler rejects, and asserts for
# each that the driver exits 1, reports on standard error the diagnostic
# FILE:LINE:COLUMN: error: MESSAGE at the occurrence that rejects the
# program and leaves an existing output untouched, and that a program the
# compiler accepts is written, through both entry points. Asserts that a
# failure of the datatype language's typing is reported at the subterm
# concerned with the type required and the type found, and a hole with
# the type required of it and the variables bound around it. Asserts that
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

(def g (lam ((t T)) (succ t)))" 3:27 'g does not check: expected Nat, got T'
assert_rejected unresolved '(def f (lam ((x T)) y))' 1:21 \
  'f does not check: y is not declared before'
assert_rejected template \
  '(module M (parameter A) (export f)
  ; a comment before the declaration
  (def f (lam ((x A)) (label x))))' 3:30 \
  "M.f does not check at its template's opaque parameters: expected T, got A"
assert_rejected nested '(module A (export g)
  (module B (export f) (def f (lam ((x T)) x)))
  (def g (lam ((x T)) (B.f y))))' 3:28 'A.g does not check: y is not declared before'
assert_rejected expansion "(data N (z)) (def f (lam ((x N)) (case x ((z) 0) (else))))" 1:19 \
  'f does not expand'

# The typing of the datatype language points to the subterm whose type is not the one its form
# requires, with the two types as they are before the erasure of datatypes, through the forms
# module elaboration and the expansion write for the source's.
light='(data Light (red) (green) (amber T))'
assert_rejected branch "$light
(defn next ((l Light)) Light (case l ((red) green) ((green) 7) ((amber x) red)))" 2:61 \
  'next does not check: expected Light, got T'
assert_rejected scrutinee "$light
(defn code ((t T)) T (case t ((red) 0) ((green) 1) ((amber x) x)))" 2:28 \
  'code does not check: expected Light, got T'
assert_rejected clause-variable "$light
(defn code ((l Light)) Light (case l ((red) l) ((green) l) ((amber x) x)))" 2:71 \
  'code does not check: expected Light, got T'
assert_rejected pattern "$light
(defn code ((l Light)) T (case l ((red x) 0) ((green) 1) ((amber x) x)))" 2:7 \
  'code does not expand'
assert_rejected recursion "$nat
(defn count ((n Nat)) T (cata Nat T n ((zero) 0) ((succ r) (cons r (nil T)))))" 2:60 \
  'count does not check: expected T, got (List T)'
assert_rejected sequence "$light
(defn f ((l Light) (k T)) T
  (let* ((a T (add k 1)) (b T l)) (add a b)))" 3:31 'f does not check: expected T, got Light'
assert_rejected guarded "$light
(defn f ((l Light) (k T)) Light
  (cond ((eq k 0) l) ((eq k 1) k) (else red)))" 3:32 'f does not check: expected Light, got T'
assert_rejected argument-datatype "$light
(defn f ((l Light)) T 0)
(def g (f 3))" 3:11 'g does not check: expected Light, got T'
assert_rejected field "(data Box (box Later))" 1:11 'box does not check'
assert_rejected datum "$light
(def d (datum Light (3)))" 2:21 'the datum is not a member of the datatype'
assert_rejected invisible '(module M (export f) (def f 1) (def g 2))
(def h (M.g 1))' 2:8 'a qualified name is not visible'

# A hole has the type its form requires of it, or the one it declares, and is reported with the
# variables bound around it; the holes of the definitions after it are reported while each
# definition's type is determined, and a definition with a hole does not check.
assert_reports() {
  local name="$1" source="$2"
  shift 2
  checked=$((checked + 1))
  printf '%s\n' "$source" > "$test_dir/$name.geb"
  local output line
  output="$("$compiler" check "$test_dir/$name.geb" 2>&1)"
  [ $? -eq 1 ] || fail_case "$name" "check does not exit 1"
  for line in "$@"; do
    case "$output" in
      *"$test_dir/$name.geb:$line"*) ;;
      *) fail_case "$name" "the report '$output' lacks '$name.geb:$line'" ;;
    esac
  done
}
assert_reports hole "$light
(defn next ((l Light)) Light (case l ((red) ?todo) ((green) red) ((amber x) ?other)))" \
  '2:45: error: hole ?todo: expected Light; in scope: l : Light' \
  '2:77: error: hole ?other: expected Light; in scope: x : T, l : Light'
assert_reports hole-declared "$light
(defn f ((k T)) T (add k (hole n T)))
(defn g ((k T)) Light (hole m T))" \
  '2:26: error: hole ?n: expected T; in scope: k : T' \
  '3:23: error: g does not check: expected Light, got T'
assert_reports hole-untyped '(def f (lam ((x T)) ?h))' \
  '1:21: error: hole ?h: no type is required of it here'
assert_reports hole-later "$light
(defn pick ((b T)) Light (if b ?first ?second))
(defn other ((l Light)) T ?later)" \
  '2:32: error: hole ?first: expected Light; in scope: b : T' \
  '2:39: error: hole ?second: expected Light; in scope: b : T' \
  '3:27: error: hole ?later: expected T; in scope: l : Light'
assert_reports hole-argument "$light
(defn f ((l Light) (k T)) T k)
(def g (f ?light ?number))" \
  '3:11: error: hole ?light: expected Light' \
  '3:18: error: hole ?number: expected T'
assert_compiled hole-filled image "$light
(defn next ((l Light)) Light (case l ((red) green) ((green) red) ((amber x) red)))"

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
# subterm is checked once, by the kernel's pass and by the datatype language's.
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
checked=$((checked + 1))
printf '%s\n(defn g ((l Light)) Light %s)\n' "$light" \
  "$(deep 7 '(case l ((red) ' ') ((green) green) ((amber x) l))')" > "$test_dir/deep-case.geb"
output="$(timeout 60 "$compiler" check "$test_dir/deep-case.geb" 2>&1)"
[ $? -eq 1 ] || fail_case deep-case "check does not exit 1 within a minute"
case "$output" in
  *"deep-case.geb:2:927: error: g does not check: expected Light, got T") ;;
  *) fail_case deep-case "message '$output' does not locate the innermost branch" ;;
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
  "$test_dir/p/c.geb:1:22: error: h does not check: nope is not declared before"*) ;;
  *) fail_case later "message '$output' does not locate h" ;;
esac

checked=$((checked + 1))
output="$("$compiler" check --manifest "$test_dir/p/p.manifest" 2>&1)"
[ $? -eq 1 ] || fail_case manifest "exit status is not 1"
case "$output" in
  "$test_dir/p/c.geb:1:22: error: h does not check: nope is not declared before"*) ;;
  *) fail_case manifest "message '$output' does not locate h" ;;
esac

checked=$((checked + 1))
printf '(def f (lam ((x T)) (nope x)))\n' > "$test_dir/p/a.geb"
output="$("$compiler" check "$test_dir/p/sub/b.geb" 2>&1)"
[ $? -eq 1 ] || fail_case earlier "exit status is not 1"
case "$output" in
  "$test_dir/p/a.geb:1:22: error: f does not check: nope is not declared before"*) ;;
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
