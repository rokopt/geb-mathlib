#!/usr/bin/env bash
#
# scripts/tests/test-layers.sh
#
# With a directory of kept states (`--cache DIRECTORY`), geb-compile
# compiles a manifest's program a layer at a time and keeps the stages'
# states after each layer (GebHost/Layers.lean). This test stages a
# program of two layers under a temp directory and asserts that its image
# is, byte for byte, the image compiled without the directory: when no
# state is kept, when every state is kept, and after a change to the
# second layer, for which the state after the first is read and not
# computed. It asserts the same of a program whose second layer refers to
# the recognizer of a datatype of the first that the first does not refer
# to, which is compiled whole; that a program a stage rejects has the
# diagnostic it has without the directory; and that a kept state whose
# key file differs from the layers' texts is not used.
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

doc='(document (syntax authoring 0) (schema 0) (prose verso 0))'

# A program of the layers `library`, of the source lib.geb, and `application`, of app.geb,
# under the directory $1.
stage() {
  mkdir -p "$1"
  printf '%s\n' "$2" > "$1/lib.geb"
  printf '%s\n' "$3" > "$1/app.geb"
  printf '%s\n' \
    "(program p (edition 0) $doc (layers (library lib.geb) (application app.geb)) (entries))" \
    > "$1/p.manifest"
}

# The image compiled with the directory of kept states is the image compiled without it; the
# trace of the states read is left in $1.trace.
assert_same() {
  local name="$1" dir="$2"
  checked=$((checked + 1))
  "$compiler" image --manifest "$dir/p.manifest" "$test_dir/$name.plain" 2> "$test_dir/$name.err" ||
    fail_case "$name" "the program does not compile: $(cat "$test_dir/$name.err")"
  GEB_LAYERS_TRACE=1 "$compiler" image --cache "$dir/cache" --manifest "$dir/p.manifest" \
    "$test_dir/$name.kept" 2> "$test_dir/$name.trace" ||
    fail_case "$name" "the program does not compile a layer at a time"
  cmp -s "$test_dir/$name.plain" "$test_dir/$name.kept" ||
    fail_case "$name" "the image compiled a layer at a time differs"
}

lib='(data Light (red) (green))
(module Lights (export next) (defn next ((l Light)) Light (case l ((red) green) ((green) red))))'
app='(module App (export twice) (import Lights)
  (defn twice ((l Light)) Light (next (next l))))'

stage "$test_dir/a" "$lib" "$app"
assert_same none "$test_dir/a"
grep -q 'load 2 (false)' "$test_dir/none.trace" || fail_case none "a state was read before any was kept"
assert_same kept "$test_dir/a"
grep -q 'load 2 (true)' "$test_dir/kept.trace" || fail_case kept "the state after both layers was not read"

# A change to the second layer: the state after the first is read, and the second compiled.
printf '%s\n' "$app
(def one (App.twice red))" > "$test_dir/a/app.geb"
assert_same changed "$test_dir/a"
grep -q 'load 1 (true)' "$test_dir/changed.trace" ||
  fail_case changed "the state after the first layer was not read"
grep -q 'advance 2' "$test_dir/changed.trace" || fail_case changed "the second layer was not compiled"
grep -q 'advance 1' "$test_dir/changed.trace" && fail_case changed "the first layer was compiled again"

# A change to the first layer: both are compiled.
printf '%s\n' "$lib
(def start red)" > "$test_dir/a/lib.geb"
assert_same first "$test_dir/a"
grep -q 'advance 1' "$test_dir/first.trace" || fail_case first "the first layer was not compiled"

# The second layer refers to the recognizer of a datatype of the first, which the first does not
# refer to: the program is compiled whole, and has the same image.
stage "$test_dir/b" '(data Light (red) (green))' \
  '(defn dec ((t T)) Light (decode Light t (lam ((l Light)) l) red))'
assert_same recognizer "$test_dir/b"
assert_same recognizer-again "$test_dir/b"

# A program the second layer's typing rejects has the diagnostic it has compiled whole.
stage "$test_dir/c" "$lib" '(def bad (Lights.next 7))'
checked=$((checked + 1))
plain="$("$compiler" check --manifest "$test_dir/c/p.manifest" 2>&1)"
[ $? -eq 1 ] || fail_case rejected "check does not exit 1"
kept="$("$compiler" check --cache "$test_dir/c/cache" --manifest "$test_dir/c/p.manifest" 2>&1)"
[ $? -eq 1 ] || fail_case rejected "check with kept states does not exit 1"
[ "$plain" = "$kept" ] || fail_case rejected "the diagnostics differ: '$plain' and '$kept'"
case "$plain" in
  *"app.geb:1:23: error: bad does not check: expected Light, got T"*) ;;
  *) fail_case rejected "the diagnostic '$plain' does not locate the argument" ;;
esac

# A kept state whose key file is not the layers' texts is not used.
checked=$((checked + 1))
stage "$test_dir/d" "$lib" "$app"
"$compiler" check --cache "$test_dir/d/cache" --manifest "$test_dir/d/p.manifest" ||
  fail_case key "the program does not check"
for k in "$test_dir"/d/cache/layers/*.key; do printf 'x' >> "$k"; done
GEB_LAYERS_TRACE=1 "$compiler" check --cache "$test_dir/d/cache" \
  --manifest "$test_dir/d/p.manifest" 2> "$test_dir/key.trace" ||
  fail_case key "the program does not check beside a kept state of another key"
grep -q '(true)' "$test_dir/key.trace" && fail_case key "a state of another key was read"

if [ "$failed" -ne 0 ]; then
  echo "test-layers: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-layers: $checked scenario(s) passed"
