#!/usr/bin/env bash
#
# scripts/tests/test-support.sh
#
# The compiler's typing and reading check each form against the
# declarations of its support (bootstrap/stage1/expansion.geb,
# bootstrap/support.geb), by the functions that search the lists of
# every declaration before the form (bootstrap/stage1/typing.geb,
# bootstrap/reader.geb, bootstrap/check.geb). `geb-compile agree`
# compares the two on a program: the first definition the typing rejects,
# the kernel forms the expansion writes, the bundle read, and whether the
# kernel's checker types it. This test asserts that they agree on the
# program of every manifest of bootstrap/, of the examples and of the
# library, and on programs staged under a temp directory, accepted and
# rejected, that name a declaration through the names the typing derives
# from a form's atoms: a datatype's recognizer, a marker's field types, a
# type abbreviation of a datatype, and a numeral abbreviation in a type.
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

# The two agree on the program of a source, which the compiler accepts
# (0) or rejects (1) as stated.
assert_agree() {
  local name="$1" status="$2" source="$3"
  checked=$((checked + 1))
  printf '%s\n' "$source" > "$test_dir/$name.geb"
  local output
  output="$("$compiler" agree "$test_dir/$name.geb" 2>&1)" ||
    fail_case "$name" "the stages differ: $output"
  "$compiler" check "$test_dir/$name.geb" > /dev/null 2>&1
  [ $? -eq "$status" ] || fail_case "$name" "check does not exit $status"
}

light='(data Light (red) (green))'

assert_agree case 0 '(data Light (red) (green) (amber T))
(defn next ((l Light)) Light (case l ((red) green) ((green) (amber 7)) ((amber x) red)))
(defn code ((l Light)) T (case l ((red) 0) ((green) 1) ((amber x) x)))'
assert_agree branch 1 "$light
(defn next ((l Light)) Light (case l ((red) green) ((green) 7)))"
assert_agree recognizer-numeral 1 "(defnum Light.member 5)
$light
(def r (datum Light (0)))"
assert_agree recognizer-numeral-later 1 "$light
(def r (datum Light (0)))
(defnum Light.member 5)
(def s (datum Light (1)))"
assert_agree recognizer-binder 0 "$light
(defn f ((Light.member T)) T Light.member)"
assert_agree datum 0 "$light
(data Two (two Light Light))
(def p (datum Two (0 (0) (1))))"
assert_agree datum-field 1 "$light
(data Two (two Light Light))
(def p (datum Two (0 (0) (2))))"
assert_agree alias 0 "$light
(deftype L Light)
(defn f ((l L)) L (case l ((red) green) ((green) red)))
(def d (datum L (1)))"
assert_agree decode 0 "$light
(defn dec ((t T)) Light (decode Light t (lam ((l Light)) l) red))"
assert_agree decode-numeral 1 "(defnum Light.member 3)
$light
(defn dec ((t T)) Light (decode Light t (lam ((l Light)) l) red))"
assert_agree field-later 1 '(data Box (box Later))
(data Later (later))
(defn open ((b Box)) T (case b ((box x) 0)))'
assert_agree field-datatype 0 '(data Inner (inner T))
(data Outer (outer Inner) (none2))
(defn get2 ((o Outer)) T (case o ((outer i) (case i ((inner x) x))) ((none2) 0)))
(def v (datum Outer (0 (0 (5)))))'
assert_agree duplicate 1 '(def a 1)
(def a 2)
(def b a)'
assert_agree duplicate-type 1 '(deftype A T)
(deftype A Unit)
(def x (lam ((y A)) y))'
assert_agree numeral-type 1 '(deftype 5 T)
(defnum five 5)
(def f (lam ((x five)) x))'
assert_agree numeral-quoted 0 '(defnum five 5)
(def q (quote (five 1 2)))
(def r (node five (nil T)))'
assert_agree unbound 1 '(def a (cons b (nil T)))'
assert_agree later 1 '(def a b)
(def b 1)'
assert_agree reserved 1 '(def lam 1)'
assert_agree recursion 0 '(data N (z) (s N))
(defn toT ((n N)) T (cata N T n ((z) 0) ((s r) (add r 1))))
(def three (toT (s (s (s z)))))'
assert_agree recursion-result 1 '(data N (z) (s N))
(defn toT ((n N)) T (cata N T n ((z) 0) ((s r) (cons r (nil T)))))'
assert_agree template 0 '(module Box (parameter A) (export Maybe2 nothing2 just2 orElse)
  (data Maybe2 (nothing2) (just2 A))
  (defn orElse ((d A) (m Maybe2)) A (case m ((just2 x) x) ((nothing2) d))))
(module Use (export v) (import (Box T) as B)
  (def v (B.orElse 3 (B.just2 4))))'
assert_agree template-opaque 1 '(module Box (parameter A) (export bad)
  (defn bad ((x A)) T (add x 1)))
(module Use (export v) (import (Box T) as B)
  (def v (B.bad 3)))'
assert_agree representation 0 "$light
(defn raw ((l Light)) T (rep l))
(defn same ((a Light) (b Light)) T (equal (rep a) (rep b)))"
assert_agree recognizer-applied 1 "$light
(defn isLight ((t T)) T (Light.member t))"
assert_agree shadowing 0 '(def a 1)
(def f (lam ((a T)) (let b T a (add a b))))'
assert_agree abbreviations 0 '(deftype Ts2 (List T))
(defnum k1 1)
(defnum k2 2)
(def one (cons k1 (nil T)))
(def two (cons k2 one))
(def len (lam ((xs Ts2)) (foldr T T (lam ((x T) (n T)) (add n k1)) 0 xs)))
(def n2 (len two))'

# Every manifest's program, side by side.
manifests=("$repo_root"/bootstrap/*.manifest "$repo_root/examples/authoring/pair.manifest"
  "$repo_root/examples/roundtrip/roundtrip.manifest"
  "$repo_root/examples/requests/requests.manifest" "$repo_root/library/library.manifest")
for m in "${manifests[@]}"; do
  ( "$compiler" agree --manifest "$m" > "$test_dir/$(basename "$m").log" 2>&1
    echo $? > "$test_dir/$(basename "$m").status" ) &
done
wait
for m in "${manifests[@]}"; do
  checked=$((checked + 1))
  [ "$(cat "$test_dir/$(basename "$m").status")" = 0 ] ||
    fail_case "$(basename "$m")" "the stages differ: $(cat "$test_dir/$(basename "$m").log")"
done

if [ "$failed" -ne 0 ]; then
  echo "test-support: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-support: $checked scenario(s) passed"
