#!/usr/bin/env bash
#
# scripts/tests/test-eal.sh
#
# Tests scripts/eal/eal.py on scripts/eal/examples.defs: the definitions the
# examples mark as not typable, and no others, are reported, with the first-order
# data exemption and without it. Skipped when the z3-solver package is absent.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EAL="$here/../eal/eal.py"
DEFS="$here/../eal/examples.defs"

if ! python3 -c 'import z3' 2>/dev/null; then
  echo "test-eal: z3-solver not installed; skipped"
  exit 0
fi

failed=0

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

if ! python3 "$EAL" --explain twoPasses "$DEFS" | grep -q 'contraction'; then
  echo "FAIL [explain]: twoPasses's conflict names no contraction"
  failed=1
fi

if [ $failed -eq 0 ]; then
  echo "test-eal: all checks passed"
fi
exit $failed
