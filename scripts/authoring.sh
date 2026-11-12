#!/usr/bin/env bash
# Regenerate or check the proof-source runner and the recorded authoring example.
# The runner extends the existing metalogic mirror; its preceding definitions must agree.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

mode=${1:-}
case "$mode" in runtime|regen|check) ;; *) echo 'usage: scripts/authoring.sh runtime|regen|check' >&2; exit 2 ;; esac
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake build geb-compile geb-defs geb-kernel
compiler=.lake/build/bin/geb-compile
runner=.lake/build/bin/geb-author
mirror=bootstrap/lean/GebMirror/Authoring.lean
example=examples/authoring

"$compiler" lean --manifest bootstrap/authoring.manifest "$tmp/full.lean"
# Split on complete definition boundaries, as scripts/bootstrap.sh splits the metalogic's layers.
python3 - "$tmp/full.lean" "$tmp/Authoring.lean" <<'PY'
import re
import sys
from pathlib import Path

def definitions(text):
    body = text.split('\nend ', 1)[0]
    return re.findall(r'^def «.*?(?=^def «|\Z)', body, re.M | re.S)

full = Path(sys.argv[1]).read_text()
base = []
for layer in ('Checker', 'Translation', 'Prover', 'Tactics'):
    base.extend(definitions(Path(f'bootstrap/lean/GebMirror/Metalogic/{layer}.lean').read_text()))
parts = definitions(full)
if [p.strip() for p in parts[:len(base)]] != [p.strip() for p in base]:
    raise SystemExit('authoring: the compiler changed the preceding metalogic definitions')
header = re.sub(r'^public import .*$', 'public import GebMirror.Metalogic.Tactics',
                full.split('\ndef «', 1)[0], flags=re.M)
header = header.replace('namespace GebBoot', 'namespace GebMirror.Metalogic')
Path(sys.argv[2]).write_text(header + '\n' + ''.join(parts[len(base):]) +
                            '\nend GebMirror.Metalogic\n\nend\n')
PY

if [ "$mode" = check ]; then
  cmp "$tmp/Authoring.lean" "$mirror"
else
  cp "$tmp/Authoring.lean" "$mirror"
fi
[ "$mode" != runtime ] || exit 0

lake build geb-author
"$runner" prove "$example/pair.manifest" "$example/Pair.proofs.geb" "$tmp/pair.cert"
"$runner" compile "$example/pair.manifest" "$tmp/pair.img"
.lake/build/bin/geb-defs "$tmp/pair.img" "$tmp/pair.defs"
cp bootstrap/compiler.img "$tmp/compiler.img"
"$runner" convert canonical "$example/pair.manifest" "$example/Pair.geb" "$tmp/pair.source.csexp"
"$runner" convert canonical "$example/pair.manifest" "$example/Lists.geb" "$tmp/lists.source.csexp"
"$runner" convert canonical "$example/pair.manifest" \
  "$example/Pair.proofs.geb" "$tmp/pair.proofs.csexp"
# Retain the compiler image itself; the input digests also pin its emitted Lean and the
# source and proof documents, including their annotations.
{
  printf '%s\n' lean-toolchain lake-manifest.json bootstrap/compiler.img \
    bootstrap/lean/GebBoot.lean GebHost/Compiler.lean GebHost/Authoring.lean \
    GebHost/Json.lean GebHost/Navigation.lean \
    GebAuthorMain.lean scripts/authoring.sh \
    bootstrap/authoring.manifest "$mirror" "$example/pair.manifest" \
    "$example/Pair.geb" "$example/Lists.geb" "$example/Pair.proofs.geb"
  .lake/build/bin/geb-kernel layers bootstrap/authoring.manifest |
    awk '{ for (i = 2; i <= NF; i++) print $i }'
} | LC_ALL=C sort -u > "$tmp/inputs"
while IFS= read -r input; do sha256sum "$input"; done < "$tmp/inputs" > "$tmp/inputs.sha256"

artifacts=(compiler.img pair.cert pair.img pair.defs pair.source.csexp lists.source.csexp
  pair.proofs.csexp inputs.sha256)
if [ "$mode" = regen ]; then
  mkdir -p "$example/record"
  for artifact in "${artifacts[@]}"; do
    cp "$tmp/$artifact" "$example/record/$artifact"
  done
else
  for artifact in "${artifacts[@]}"; do
    cmp "$tmp/$artifact" "$example/record/$artifact"
  done
fi
"$runner" replay "$example/pair.manifest" "$example/Pair.proofs.geb" "$example/record/pair.cert"
if [ "$mode" = check ]; then
  lake build GebHost
  lake exe batteries/runLinter GebHost
fi
printf '%s\n' 'authoring: runner, proof, elaborated definitions, and pinned inputs agree'
