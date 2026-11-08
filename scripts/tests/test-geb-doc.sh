#!/usr/bin/env bash
#
# scripts/tests/test-geb-doc.sh
#
# Smoke test for geb-doc, the check of comments. Stages manifests under a
# temp directory and asserts that a program whose comments and notes refer
# to a definition it declares, to a constant of the Geb library and to an
# entry of docs/references.bib is accepted, and that one referring to
# nothing in each of these, or with prose outside the recorded subset of
# Verso's markup, is rejected, each failure named with its file.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build Geb geb-doc > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: the library or geb-doc does not build" >&2
  exit 1
}

# geb-doc imports the library's modules, whose path lake env supplies.
geb_doc() { (cd "$repo_root" && lake env .lake/build/bin/geb-doc "$@"); }

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

doc='(document (syntax authoring 0) (schema 0) (prose verso 0))'

# Every reference resolves: a definition from inside its module and by its
# qualified name, a Lean constant, an entry of the bibliography, and a note's
# links.
mkdir -p "$test_dir/good"
{
  printf '; The program of {geb}`M.g`, after {cite}`RFC9804`; {lit}`anything`.\n'
  printf '(module M (export g)\n'
  printf '  ; {geb}`g`, checked by {name}`Geb.Kernel.infer`\n'
  printf '  (def g (lam ((x T)) x)))\n'
  printf '(note (link geb M.g) (link lean Geb.Kernel.infer))\n'
  printf '(def main (lam ((x T)) (M.g x)))\n'
} > "$test_dir/good/a.geb"
printf '%s\n' '; The program {geb}`main`.' "(program good (edition 0) $doc" \
  '  (sources a.geb)' '  (entries main))' > "$test_dir/good/good.manifest"

checked=$((checked + 1))
output="$(geb_doc --check "$test_dir/good/good.manifest" 2>&1)"
code=$?
[ "$code" -eq 0 ] || fail_case accepted "exit $code: $output"

# Each reference resolving to nothing, and prose outside the subset, fails,
# named with its file.
mkdir -p "$test_dir/bad"
{
  printf '; {geb}`h` and {name}`Geb.Kernel.nothing`\n'
  printf '(def f (lam ((x T)) x))\n'
  printf '; an unescaped _\n'
  printf '(note (link lean Geb.Kernel.nothing))\n'
  printf '; {cite}`Nobody2026`\n'
  printf '(def main (lam ((x T)) (f x)))\n'
} > "$test_dir/bad/a.geb"
printf '%s\n' "(program bad (edition 0) $doc (sources a.geb) (entries main))" \
  > "$test_dir/bad/bad.manifest"

checked=$((checked + 1))
output="$(geb_doc --check "$test_dir/bad/bad.manifest" 2>&1)"
code=$?
[ "$code" -eq 1 ] || fail_case rejected "exit $code, expected 1"
for expected in \
  'a.geb: the comment before f: h names no definition of the program' \
  'a.geb: the comment before f: Geb.Kernel.nothing names no Lean constant' \
  'a.geb: the comment at the top level: the character _ is written \_ in text' \
  'a.geb: the comment before main: Nobody2026 is no entry of the bibliography' \
  'a.geb: the note of main: Geb.Kernel.nothing names no Lean constant'; do
  case "$output" in
    *"$expected"*) ;;
    *) fail_case rejected "'$expected' not in '$output'" ;;
  esac
done

checked=$((checked + 1))
output="$(geb_doc 2>&1)"
code=$?
[ "$code" -eq 2 ] || fail_case usage "exit $code, expected 2"

if [ "$failed" -gt 0 ]; then
  echo "test-geb-doc: $failed of $checked scenarios failed" >&2
  exit 1
fi
echo "test-geb-doc: $checked scenarios passed"
