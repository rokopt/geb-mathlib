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

# A failing example of the client rejects its check.
sed -i 's/(quote (0 (7) (8) (8) (7)))/(quote (0 (7) (8)))/' "$client/Client.geb"
if bash "$client/check.sh" 2>/dev/null; then
  echo "test-client: a false example was accepted" >&2
  exit 1
fi
echo "test-client: library and client template checked"
