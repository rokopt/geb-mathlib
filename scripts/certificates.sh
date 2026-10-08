#!/usr/bin/env bash
#
# scripts/certificates.sh regen|check
#
# Regenerate or check the certificates of the internal language's
# developments, bootstrap/certificates/*.cert, which the modules of
# GebTests/Prototypes/FreeTopos/Certified/ read and check. geb-certify,
# built from GebTests/Prototypes/FreeTopos/StoredWriter.lean, runs the
# searches of GebTests/Prototypes/FreeTopos/Certificates.lean and writes
# each development's declarations, printing for each certificate its name,
# its number of declarations, the bytes of its text and the milliseconds
# of its search.
#
#   regen  Writes the certificates into bootstrap/certificates/.
#   check  Writes them into a temporary directory and compares their bytes
#          with the committed ones, and checks that every committed
#          certificate is one a search writes.
#
# The searches recurse deeper than the default stack allows, so the
# generator runs with the stack limit raised to the hard limit.
#
# Exit 0 when every comparison holds; exit 1 naming the first that does
# not.
set -euo pipefail
cd "$(dirname "$0")/.."
dir=bootstrap/certificates
fail() { echo "certificates: $1" >&2; exit 1; }
generate() { (ulimit -s "$(ulimit -Hs)"; .lake/build/bin/geb-certify "$1"); }
case "${1:-}" in
  regen)
    lake build geb-certify
    generate "$dir"
    ;;
  check)
    lake build geb-certify
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    generate "$tmp" || fail "a search fails"
    for f in "$tmp"/*.cert; do
      cmp -s "$f" "$dir/$(basename "$f")" \
        || fail "the committed $(basename "$f") is not the search's: run scripts/certificates.sh regen"
    done
    for f in "$dir"/*.cert; do
      [ -e "$tmp/$(basename "$f")" ] || fail "the committed $(basename "$f") is no search's"
    done
    echo "certificates: every certificate is its search's"
    ;;
  *)
    echo "usage: scripts/certificates.sh regen|check" >&2
    exit 2
    ;;
esac
