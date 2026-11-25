#!/usr/bin/env bash
# Check the shared library under library/ and the client template under examples/client/. The
# template is copied outside the repository, with this checkout standing in for its Geb
# submodule, and checked by its own check.sh, which its CI workflow runs.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-kernel
author=.lake/build/bin/geb-author
kernel=.lake/build/bin/geb-kernel

scratch=$(mktemp -d "${TMPDIR:-/tmp}/geb-client-test-XXXXXX")
trap 'rm -rf "$scratch"' EXIT

# The library alone: its examples and its theorems.
"$author" compile library/library.manifest "$scratch/library.img"
"$author" prove library/Bytes.proofs.geb "$scratch/library.cert"
"$author" replay library/Bytes.proofs.geb "$scratch/library.cert"

client="$scratch/client λ"
cp -R examples/client "$client"
ln -s "$PWD" "$client/geb"
bash "$client/check.sh"

# The application reverses a file's bytes after them.
printf 'abc' > "$scratch/input"
"$kernel" run "$client/.lake/client.img" Client.run "$scratch/input" "$scratch/output"
[ "$(cat "$scratch/output")" = abccba ] || { echo "test-client: Client.run gave the wrong output" >&2; exit 1; }

# The editor's three execution commands share the client's kept layers. Change only the
# application, then the library, using private sources for both edits.
author="$PWD/$author"
cp -RL library "$client/library"
sed 's|geb/library/library.manifest|library/library.manifest|' \
  "$client/client.manifest" > "$client/layered.manifest"
(
  cd "$client"
  printf 'abc' > input
  printf 'input\n' > ./--cache
  compare() {
    local action=$1 output=$2
    shift 2
    "$author" "$action" layered.manifest "$@" plain
    GEB_LAYERS_TRACE=1 "$author" "$action" --cache cache layered.manifest "$@" "$output" 2> trace
    cmp plain "$output"
  }
  compare compile program.img
  grep -q 'advance 1' trace
  grep -q 'example Lists.reverse reuse true' trace
  grep -q 'example Client.run reuse true' trace
  grep -q 'example Copy.step reuse true' trace
  for change in warm edited; do
    if [ "$change" = edited ]; then printf '\n(def clientEdit 1)\n' >> Client.geb; fi
    compare compile program.img
    if [ "$change" = edited ]; then grep -q 'load 1 (true)' trace
    else grep -q 'load 2 (true)' trace; fi
    compare run result Client.run input
    grep -q 'load 2 (true)' trace
    compare interact copied Copy.step --cache
    grep -q 'load 2 (true)' trace
    cmp input copied
  done
  # An example can be the first use of the recognizer of an earlier datatype. The
  # reader inserts the recognizer at its declaration in the saved kernel forms.
  cat >> Client.geb <<'GEB'
(data Light (red) (green))
(note (example (decode Light 0 (lam ((l Light)) 42) 42) 42))
(def exampleDecode 0)
GEB
  compare compile program.img
  grep -q 'example exampleDecode reuse true' trace
  # The library's examples still pass after its change, but its client now computes
  # a different result. Both modes reject at the same client example and preserve the image.
  sed -i 's/(k (cons x acc))/(cons x (k acc))/; s/(quote (0 (9) (8) (7)))/(quote (0 (7) (8) (9)))/' library/Lists.geb
  cp program.img previous.img
  if "$author" compile layered.manifest program.img 2> plain.err; then exit 1; fi
  if "$author" compile --cache cache layered.manifest program.img 2> cached.err; then exit 1; fi
  cmp plain.err cached.err
  grep -q 'example of Client.run differs' cached.err
  cmp previous.img program.img
)
# A failing example of the client rejects its check.
sed -i 's/(quote (0 (7) (8) (8) (7)))/(quote (0 (7) (8)))/' "$client/Client.geb"
if bash "$client/check.sh" 2>/dev/null; then
  echo "test-client: a false example was accepted" >&2
  exit 1
fi
echo "test-client: library and client template checked"
