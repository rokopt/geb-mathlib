#!/usr/bin/env bash
#
# scripts/tests/test-manifest.sh
#
# Smoke test for the manifests of programs. Stages manifests under a temp
# directory and asserts that geb-kernel, geb-compile and geb-fmt read a
# program from its manifest, resolving its sources against the manifest's
# directory and erasing the notes of its sources, and that a manifest with
# an unknown edition, a profile this host does not read, a malformed field,
# a source outside its directory, a repeated source or an entry the program
# does not define, and a source with a malformed note, is rejected with its
# reason, an existing output left untouched.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build geb-kernel geb-compile geb-fmt > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: the executables do not build" >&2
  exit 1
}
kernel="$repo_root/.lake/build/bin/geb-kernel"
compiler="$repo_root/.lake/build/bin/geb-compile"
fmt="$repo_root/.lake/build/bin/geb-fmt"

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

# the profile of the current host
doc='(document (syntax authoring 0) (schema 0) (prose verso 0))'

mkdir -p "$test_dir/p/sub"
printf '(def f (lam ((x T)) x))\n' > "$test_dir/p/a.geb"
printf '(def main (lam ((x T)) (f x)))\n' > "$test_dir/p/sub/b.geb"
printf '%s\n' "(program p (edition 0) $doc" '  (sources a.geb sub/b.geb)' '  (entries main))' \
  > "$test_dir/p/p.manifest"

# The manifest is read from another directory, so that only its own
# directory can resolve its sources.
cd "$test_dir" || exit 1

checked=$((checked + 1))
"$kernel" join p/p.manifest joined.geb || fail_case join "exit $?"
printf '(def f (lam ((x T)) x))\n\n(def main (lam ((x T)) (f x)))\n\n' > expected.geb
cmp -s joined.geb expected.geb || fail_case join "the text is not the sources, each with a newline"

checked=$((checked + 1))
"$kernel" build --manifest p/p.manifest manifest.img || fail_case build "exit $?"
"$kernel" build p/a.geb p/sub/b.geb sources.img || fail_case build "the sources' build fails"
cmp -s manifest.img sources.img || fail_case build "the image is not that of the sources"

for mode in image lean; do
  checked=$((checked + 1))
  "$compiler" "$mode" --manifest p/p.manifest "manifest.$mode" || fail_case "compile $mode" "exit $?"
  "$compiler" "$mode" joined.geb "file.$mode" || fail_case "compile $mode" "the text's compile fails"
  cmp -s "manifest.$mode" "file.$mode" || fail_case "compile $mode" "not the output of the text"
done

checked=$((checked + 1))
printf '%s\n' "(program l (edition 0) $doc (layers (A a.geb) (B sub/b.geb)) (entries main))" \
  > p/l.manifest
printf 'A p/a.geb\nB p/sub/b.geb\n' > expected.layers
"$kernel" layers p/l.manifest > got.layers || fail_case layers "exit $?"
cmp -s got.layers expected.layers || fail_case layers "the layers are not named with their paths"
"$kernel" join p/l.manifest layered.geb || fail_case layers "the join fails"
cmp -s layered.geb expected.geb || fail_case layers "the text is not the layers' sources in order"
"$kernel" join p/l.manifest first.geb A || fail_case layers "the join through a layer fails"
printf '(def f (lam ((x T)) x))\n\n' > expected.first
cmp -s first.geb expected.first || fail_case layers "the text is not the first layer's sources"
output="$("$kernel" join p/l.manifest first.geb C 2>&1)"
case "$output" in
  *'l.manifest: the program has no layer C'*) ;;
  *) fail_case layers "a layer the program lacks is joined: '$output'" ;;
esac

# A source's notes are erased before it is compiled: the program with notes
# builds and compiles to the program's image without them.
checked=$((checked + 1))
mkdir -p n/sub
{
  printf '; the identity\n'
  printf '(note (example (f 1) 1) (link lean Geb.Kernel.Tree) (author someone))\n'
  printf '(def f (lam ((x T)) x))\n'
} > n/a.geb
{
  printf '(module M (export g)\n'
  printf '  (note (link geb f))\n'
  printf '  (def g (lam ((x T)) (f x))))\n'
  printf '(def main (lam ((x T)) (M.g x)))\n'
} > n/sub/b.geb
printf '(module M (export g) (def g (lam ((x T)) (f x))))\n(def main (lam ((x T)) (M.g x)))\n' \
  > plain-b.geb
printf '%s\n' "(program n (edition 0) $doc (sources a.geb sub/b.geb) (entries main))" \
  > n/n.manifest
"$kernel" build p/a.geb plain-b.geb plain.img || fail_case notes "the program without notes fails"
"$kernel" build --manifest n/n.manifest notes.img || fail_case notes "the program with notes fails"
cmp -s notes.img plain.img || fail_case notes "the image is not that of the program without notes"
"$compiler" image --manifest n/n.manifest notes.compiled || fail_case notes "the compile fails"
"$compiler" image n/a.geb a.compiled || fail_case notes "the compile of a file with notes fails"
"$kernel" join n/n.manifest notes.geb || fail_case notes "the join fails"
grep -q 'note' notes.geb && fail_case notes "the joined text holds a note"
"$fmt" --check n/a.geb || fail_case notes "a source with notes is not formatted"

# A profile's optional fields are kept by the reader and read by no host.
checked=$((checked + 1))
printf '%s\n' "(program o (edition 0) (document (syntax authoring 0) (schema 0) (prose verso 0) \
(crit schema) (generator geb-fmt 0)) (sources a.geb sub/b.geb) (entries main))" > n/o.manifest
"$kernel" build --manifest n/o.manifest optional.img || fail_case optional "exit $?"
cmp -s optional.img plain.img || fail_case optional "the image is not the program's"

# A malformed note is rejected, its source named, by every driver.
assert_note_rejected() {
  local name="$1" source="$2" expected="$3" driver output code
  checked=$((checked + 1))
  mkdir -p "b-$name"
  printf '%s\n' "$source" > "b-$name/a.geb"
  printf '%s\n' "(program b (edition 0) $doc (sources a.geb) (entries))" > "b-$name/b.manifest"
  for driver in join build compile file; do
    printf 'kept' > kept.out
    case "$driver" in
      join) output="$("$kernel" join "b-$name/b.manifest" kept.out 2>&1)" ;;
      build) output="$("$kernel" build --manifest "b-$name/b.manifest" kept.out 2>&1)" ;;
      compile) output="$("$compiler" image --manifest "b-$name/b.manifest" kept.out 2>&1)" ;;
      file) output="$("$compiler" image "b-$name/a.geb" kept.out 2>&1)" ;;
    esac
    code=$?
    [ "$code" -eq 1 ] || fail_case "$name/$driver" "exit $code, expected 1"
    case "$output" in
      *"b-$name/a.geb: "*"$expected"*) ;;
      *) fail_case "$name/$driver" "message '$output' lacks '$expected'" ;;
    esac
    [ "$(cat kept.out)" = kept ] || fail_case "$name/$driver" "the output was changed"
  done
}

assert_note_rejected link '(note (link url x)) (def f (lam ((x T)) x))' 'a note is not (note FIELD'
assert_note_rejected last '(def f (lam ((x T)) x)) (note (link geb f))' \
  'a note documents no declaration'
assert_note_rejected before '(note (link geb f)) (note (link geb f)) (def f (lam ((x T)) x))' \
  'a note documents no declaration'

checked=$((checked + 1))
"$fmt" --check --manifest p/p.manifest || fail_case fmt "a formatted program is reported"
printf '(def   g (lam ((x T)) x))\n' >> p/sub/b.geb
"$fmt" --check --manifest p/p.manifest > fmt.log
[ $? -eq 1 ] || fail_case fmt "an unformatted source is not reported"
grep -q 'sub/b.geb: not formatted' fmt.log || fail_case fmt "the source is not named"
"$fmt" --manifest p/p.manifest || fail_case fmt "the program is not formatted"
"$fmt" --check --manifest p/p.manifest || fail_case fmt "formatting does not reach a fixed point"
printf '(def f (lam ((x T)) x))\n' > p/a.geb
printf '(def main (lam ((x T)) (f x)))\n' > p/sub/b.geb

# Each driver rejects the manifest with the message and keeps the output.
assert_rejected() {
  local name="$1" manifest="$2" expected="$3" driver output code
  checked=$((checked + 1))
  printf '%s\n' "$manifest" > "p/$name.manifest"
  for driver in join build compile; do
    printf 'kept' > kept.out
    case "$driver" in
      join) output="$("$kernel" join "p/$name.manifest" kept.out 2>&1)" ;;
      build) output="$("$kernel" build --manifest "p/$name.manifest" kept.out 2>&1)" ;;
      compile) output="$("$compiler" image --manifest "p/$name.manifest" kept.out 2>&1)" ;;
    esac
    code=$?
    [ "$code" -eq 1 ] || fail_case "$name/$driver" "exit $code, expected 1"
    case "$output" in
      *"$name.manifest: "*"$expected"*) ;;
      *) fail_case "$name/$driver" "message '$output' lacks '$expected'" ;;
    esac
    [ "$(cat kept.out)" = kept ] || fail_case "$name/$driver" "the output was changed"
  done
}

assert_rejected edition "(program p (edition 1) $doc (sources a.geb) (entries))" \
  'the edition 1 is not this host'"'"'s edition 0'
assert_rejected numeral "(program p (edition x) $doc (sources a.geb) (entries))" \
  'the edition is not a numeral'
assert_rejected form "(library p (edition 0) $doc (sources a.geb) (entries))" \
  'the form is not a program'
assert_rejected order "(program p (sources a.geb) (edition 0) $doc (entries))" \
  'the field edition is expected'
assert_rejected unknown "(program p (edition 0) $doc (sources a.geb) (entries) (extra))" \
  'a program is (program NAME'
assert_rejected two "(program p (edition 0) $doc (sources a.geb) (entries)) (program q)" \
  'not one well-formed form'
assert_rejected none "(program p (edition 0) $doc (sources) (entries))" 'the program has no sources'
assert_rejected absolute "(program p (edition 0) $doc (sources /etc/passwd) (entries))" \
  'the source /etc/passwd is not a relative path'
assert_rejected parent "(program p (edition 0) $doc (sources ../a.geb) (entries))" \
  'the source ../a.geb is not a relative path'
assert_rejected repeated "(program p (edition 0) $doc (sources a.geb a.geb) (entries))" \
  'the source a.geb is listed twice'
assert_rejected entries "(program p (edition 0) $doc (sources a.geb) (entries f f))" \
  'the entry f is listed twice'
assert_rejected layer "(program p (edition 0) $doc (layers (A)) (entries))" \
  'a layer is a name followed'
# a manifest of the profile whose fields follow the head document
profiled() { printf '(program p (edition 0) (document %s) (sources a.geb) (entries))' "$1"; }
assert_rejected syntax "$(profiled '(syntax authoring 1) (schema 0) (prose verso 0)')" \
  'the syntax authoring 1 is not this host'"'"'s authoring 0'
assert_rejected schema "$(profiled '(syntax authoring 0) (schema 2) (prose verso 0)')" \
  'the schema 2 is not this host'"'"'s schema 0'
assert_rejected crit \
  "$(profiled '(syntax authoring 0) (schema 0) (prose verso 0) (crit signature) (signature x)')" \
  'the document requires the field signature, which this host does not read'
assert_rejected profile '(program p (edition 0) (document (schema 0)) (sources a.geb) (entries))' \
  'a profile is (document'

# An entry the program does not define passes the reader and is rejected
# where the program is read, which join does not do.
for driver in build compile; do
  checked=$((checked + 1))
  printf '%s\n' "(program m (edition 0) $doc (sources a.geb) (entries nope))" > p/m.manifest
  printf 'kept' > kept.out
  case "$driver" in
    build) output="$("$kernel" build --manifest p/m.manifest kept.out 2>&1)" ;;
    compile) output="$("$compiler" image --manifest p/m.manifest kept.out 2>&1)" ;;
  esac
  code=$?
  [ "$code" -eq 1 ] || fail_case "missing/$driver" "exit $code, expected 1"
  case "$output" in
    *'m.manifest: the entry nope names no definition'*) ;;
    *) fail_case "missing/$driver" "message '$output'" ;;
  esac
  [ "$(cat kept.out)" = kept ] || fail_case "missing/$driver" "the output was changed"
done

# A source the manifest names and the tree does not hold is reported as a
# failure, not as an empty program.
checked=$((checked + 1))
printf '%s\n' "(program g (edition 0) $doc (sources gone.geb) (entries))" > p/g.manifest
printf 'kept' > kept.out
"$compiler" image --manifest p/g.manifest kept.out > gone.log 2>&1
[ $? -eq 1 ] || fail_case gone "exit status is not 1"
grep -q 'gone.geb' gone.log || fail_case gone "the source is not named"
[ "$(cat kept.out)" = kept ] || fail_case gone "the output was changed"

if [ "$failed" -ne 0 ]; then
  echo "test-manifest: $failed failure(s) in $checked scenario(s)" >&2
  exit 1
fi
echo "test-manifest: $checked scenario(s) passed"
