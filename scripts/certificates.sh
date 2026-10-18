#!/usr/bin/env bash
#
# scripts/certificates.sh regen|check [NAME...] | searches
#
# Regenerate or check the certificates of the internal language's
# developments, bootstrap/certificates/*.cert, which the modules of
# GebTests/Prototypes/FreeTopos/Certified/ read and check. geb-certify,
# built from GebTests/Prototypes/FreeTopos/StoredWriter.lean, runs the
# searches of GebTests/Prototypes/FreeTopos/Certificates.lean and writes
# each development's declarations, printing for each certificate its name,
# its number of declarations, the bytes of its text and the milliseconds
# of its search. The searches run are those named, or all of them.
#
#   regen     Writes the certificates into bootstrap/certificates/.
#   check     Writes them into a temporary directory and compares their
#             bytes with the committed ones. A named search reads the
#             committed certificates it continues from; with no search
#             named, it also checks that every committed certificate is
#             one a search writes.
#   searches  Prints the searches' names, one to a line.
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
generate() { (ulimit -s "$(ulimit -Hs)"; .lake/build/bin/geb-certify "$@"); }
mode="${1:-}"
[ $# -gt 0 ] && shift
case "$mode" in
  regen)
    lake build geb-certify
    generate "$dir" "$@"
    ;;
  check)
    lake build geb-certify
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    out="$tmp/out"
    mkdir "$out"
    [ $# -gt 0 ] && cp "$dir"/*.cert "$out"/
    generate "$out" "$@" | tee "$tmp/written" || fail "a search fails"
    [ -s "$tmp/written" ] || fail "no search writes a certificate"
    while IFS=, read -r name _; do
      cmp -s "$out/$name.cert" "$dir/$name.cert" \
        || fail "the committed $name.cert is not the search's: run scripts/certificates.sh regen"
    done < "$tmp/written"
    if [ $# -eq 0 ]; then
      for f in "$dir"/*.cert; do
        [ -e "$out/$(basename "$f")" ] || fail "the committed $(basename "$f") is no search's"
      done
    fi
    echo "certificates: every certificate checked is its search's"
    ;;
  searches)
    lake build geb-certify >&2
    generate --searches
    ;;
  *)
    echo "usage: scripts/certificates.sh regen|check [NAME...] | searches" >&2
    exit 2
    ;;
esac
