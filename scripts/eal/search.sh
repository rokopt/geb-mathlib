#!/usr/bin/env bash
#
# scripts/eal/search.sh DEFS|--self OUT
#
# Runs the search for elementary-affine decorations written in Geb,
# bootstrap/affine-search.geb, on a program's definitions in the form
# `lake exe geb-defs IMAGE DEFS` writes, or with --self on those of the search's own
# program. OUT receives the verdicts, in the form scripts/eal/eal.py prints them, and
# the certificate of the definitions typable per use, its last line.
#
# The search's program is that of bootstrap/affine-search.manifest, compiled by the
# committed stage-1 compiler.

set -euo pipefail
cd "$(dirname "$0")/../.."

if [ $# -ne 2 ]; then
  echo "usage: scripts/eal/search.sh DEFS|--self OUT" >&2
  exit 2
fi

b=bootstrap
kernel=.lake/build/bin/geb-kernel
lake build -q geb-kernel geb-defs

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
"$kernel" join "$b/affine-search.manifest" "$tmp/search.geb"
"$kernel" run "$b/compiler.img" main "$tmp/search.geb" "$tmp/search.img"
[ -s "$tmp/search.img" ] || { echo "search: the stage-1 compiler rejects the search" >&2; exit 1; }

defs=$1
if [ "$defs" = --self ]; then
  defs=$tmp/search.defs
  .lake/build/bin/geb-defs "$tmp/search.img" "$defs"
fi
"$kernel" run "$tmp/search.img" main "$defs" "$2"
