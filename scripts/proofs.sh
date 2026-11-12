#!/usr/bin/env bash
# Prove and replay the developments of bootstrap/proofs/ from their Geb sources: each proof
# document that no other imports, with the documents it imports, against the program it names.
# The searches run side by side and take from minutes to tens of minutes compiled, so
# slow-checks.yml runs this script, and scripts/tests/test-proof-scripts.sh proves the
# development of tree-cases.proofs.geb alone.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

lake build geb-author
runner=.lake/build/bin/geb-author
dir=bootstrap/proofs
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

names=()
pids=()
for doc in "$dir"/*.proofs.geb; do
  name=$(basename "$doc")
  # A document that another imports is proved with it.
  if grep -qF "(import $name)" "$dir"/*.proofs.geb; then continue; fi
  (
    "$runner" prove "$doc" "$tmp/$name.cert"
    "$runner" replay "$doc" "$tmp/$name.cert"
  ) > "$tmp/$name.log" 2>&1 &
  names+=("$name")
  pids+=($!)
done

status=0
for i in "${!pids[@]}"; do
  if wait "${pids[$i]}"; then
    echo "proofs: ${names[$i]} proved and replayed"
  else
    cat "$tmp/${names[$i]}.log"
    echo "proofs: ${names[$i]} failed" >&2
    status=1
  fi
done
exit "$status"
