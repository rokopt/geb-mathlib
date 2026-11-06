#!/usr/bin/env bash
#
# scripts/tests/test-eal.sh
#
# Tests the searches for elementary-affine decorations on scripts/eal/examples.defs.
# The search written in Geb (scripts/eal/search.sh): the definitions the examples mark
# as not typable, alone and with a decoration per use, and no others, are reported;
# its certificate checks, and is the committed one, which
# GebTests/Prototypes/Affine/Decoration.lean also checks; and no definition of the
# search itself is rejected. scripts/eal/eal.py: the same verdicts, with the
# first-order data exemption, and those the examples mark without it, and a
# certificate is written of the definitions typable per use, which that module checks
# in its committed form. The tests of scripts/eal/eal.py are skipped when the
# z3-solver package is absent.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EAL="$here/../eal/eal.py"
SEARCH="$here/../eal/search.sh"
DEFS="$here/../eal/examples.defs"

failed=0

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# the definitions a report names on the lines beginning with a prefix, sorted
named() { # report prefix
  sed -n "s/^  $2: \([^ ]*\).*/\1/p" "$1" | sort | tr '\n' ' '
}
sorted() { printf '%s\n' "$@" | sort | tr '\n' ' '; }

if ! bash "$SEARCH" "$DEFS" "$tmp/search.out"; then
  echo "FAIL [search]: it does not run on the examples"
  failed=1
fi
if [ "$(named "$tmp/search.out" 'NOT TYPABLE')" != \
     "$(sorted foldTwice twoPasses readTwice loopInside)" ]; then
  echo "FAIL [search]: not typable: '$(named "$tmp/search.out" 'NOT TYPABLE')'"
  failed=1
fi
if [ "$(named "$tmp/search.out" 'NOT TYPABLE PER USE')" != "$(sorted foldPairUp)" ]; then
  echo "FAIL [search, per use]: not typable: '$(named "$tmp/search.out" 'NOT TYPABLE PER USE')'"
  failed=1
fi
if ! grep -q ' of 13 definitions, checked$' "$tmp/search.out"; then
  echo "FAIL [search, certificate]: not of the 13 definitions typable per use, or not checked"
  failed=1
fi
if ! tail -n 1 "$tmp/search.out" | cmp -s - "$here/../eal/examples-geb.cert"; then
  echo "FAIL [search, certificate]: not the committed scripts/eal/examples-geb.cert"
  failed=1
fi

if ! bash "$SEARCH" --self "$tmp/self.out"; then
  echo "FAIL [search, itself]: it does not run on its own program"
  failed=1
fi
if grep -q '^  NOT TYPABLE.*: AffineSearch\.' "$tmp/self.out"; then
  echo "FAIL [search, itself]: it rejects a definition of its own"
  failed=1
fi

if ! python3 -c 'import z3' 2>/dev/null; then
  if [ $failed -eq 0 ]; then
    echo "test-eal: z3-solver not installed; the search written in Geb passed, eal.py skipped"
  fi
  exit $failed
fi


untypable() { # mode expected-names...
  local mode=$1; shift
  local got
  got=$(python3 "$EAL" $mode "$DEFS" | sed -n 's/^  NOT TYPABLE: \([^ ]*\) .*/\1/p' | sort | tr '\n' ' ')
  local want
  want=$(printf '%s\n' "$@" | sort | tr '\n' ' ')
  if [ "$got" != "$want" ]; then
    echo "FAIL [${mode:-exempt}]: not typable: '$got', expected '$want'"
    failed=1
  fi
}

untypable "" foldTwice twoPasses readTwice loopInside
untypable --pure foldTwice squareByIter twoPasses readTwice loopInside composeFirst

perUse() { # mode expected-names...
  local mode=$1; shift
  local got
  got=$(python3 "$EAL" $mode "$DEFS" | sed -n 's/^  NOT TYPABLE PER USE: \([^ ]*\) .*/\1/p' | sort | tr '\n' ' ')
  local want
  want=$(printf '%s\n' "$@" | sort | tr '\n' ' ')
  if [ "$got" != "$want" ]; then
    echo "FAIL [${mode:-exempt}, per use]: not typable: '$got', expected '$want'"
    failed=1
  fi
}

perUse "" foldPairUp
perUse --pure foldPairUp onePass

python3 "$EAL" "$DEFS" > "$tmp/z3.out"
for prefix in 'NOT TYPABLE' 'NOT TYPABLE PER USE'; do
  if [ "$(named "$tmp/z3.out" "$prefix")" != "$(named "$tmp/search.out" "$prefix")" ]; then
    echo "FAIL [verdicts]: the searches disagree on '$prefix'"
    failed=1
  fi
done

cert="$tmp/z3.cert"
if ! python3 "$EAL" --certificate "$cert" "$DEFS" | grep -q ' of 13 definitions, written'; then
  echo "FAIL [certificate]: not of the 13 definitions typable per use"
  failed=1
fi

if ! python3 "$EAL" --explain twoPasses "$DEFS" | grep -q 'contraction'; then
  echo "FAIL [explain]: twoPasses's conflict names no contraction"
  failed=1
fi

if [ $failed -eq 0 ]; then
  echo "test-eal: all checks passed"
fi
exit $failed
