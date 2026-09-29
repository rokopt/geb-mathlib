#!/usr/bin/env bash
#
# scripts/bench-bootstrap.sh [RUNS]
#
# Time the bootstrap's programs on their own sources, the median of RUNS
# (default 5) wall-clock runs after one warm-up, one heavy process at a
# time:
#
#   compile/native  geb-compile, the compiler built from the emitted Lean,
#                   compiling the stage-1 source S to its image;
#   compile/seed    the seed evaluating bootstrap/compiler.img on S;
#   prove/<file>    the seed evaluating the prover of Gödel's T, built by the
#                   stage-0 compiler, on each file of theorems that
#                   GebTests/Prototypes/Proofs.lean checks, with the number
#                   of theorems the Geb checker accepts.
#
# S and the prover's program are assembled as scripts/bootstrap.sh and
# GebTests/Prototypes/Proofs.lean assemble them.

set -euo pipefail
cd "$(dirname "$0")/.."

runs=${1:-5}
b=bootstrap
kernel=.lake/build/bin/geb-kernel
native=.lake/build/bin/geb-compile

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

join() { local f; for f in "$@"; do cat "$f"; echo; done; }

# The median wall time in seconds of running the command $2.. $runs times, after a warm-up, as
# the line "$1 <seconds>".
bench() {
  local name=$1; shift
  "$@" > /dev/null
  local i s e ts=()
  for ((i = 0; i < runs; i++)); do
    s=$(date +%s.%N); "$@" > /dev/null; e=$(date +%s.%N)
    ts+=("$(echo "$e - $s" | bc)")
  done
  printf '%-22s %s\n' "$name" "$(printf '%s\n' "${ts[@]}" | sort -g | sed -n "$(((runs + 1) / 2))p")"
}

lake build geb-kernel geb-compile > /dev/null

join $b/prelude.geb $b/serialize.geb $b/reader.geb $b/check.geb $b/stage1/datatype.geb \
  $b/compile.geb $b/stage1/lean.geb > "$tmp/S.geb"
bench compile/native "$native" image "$tmp/S.geb" "$tmp/out.img"
bench compile/seed "$kernel" run $b/compiler.img main "$tmp/S.geb" "$tmp/out.img"

# The prover, its entry point giving the number of theorems the Geb checker accepts.
"$kernel" build $b/prelude.geb $b/serialize.geb $b/reader.geb $b/check.geb $b/datatype.geb \
  $b/compile.geb "$tmp/stage0.img"
{ join $b/prelude.geb $b/reader.geb $b/check.geb $b/datatype.geb $b/goedel-t/equations.geb \
    $b/goedel-t/prove.geb
  echo '(def main (lam ((file T)) (node 0 (single (foldr T T (lam ((x T) (n T))
    (if (eq (label (child x 3)) 1) (add n 1) n)) 0 (children (child (child (proveFile 256 file) 0) 1)))))))'
} > "$tmp/prover.geb"
"$kernel" run "$tmp/stage0.img" main "$tmp/prover.geb" "$tmp/prover.img"
[ -s "$tmp/prover.img" ] || { echo "bench-bootstrap: the stage-0 compiler rejects the prover" >&2; exit 1; }

p=$b/proofs
for f in prelude nat check equations datatype; do
  case $f in
    prelude|nat) join $b/prelude.geb $p/$f.geb ;;
    check|datatype) join $b/prelude.geb $b/reader.geb $b/check.geb $p/$f.geb ;;
    equations) join $b/prelude.geb $b/reader.geb $b/check.geb $b/goedel-t/equations.geb $p/$f.geb ;;
  esac > "$tmp/$f.in"
  "$kernel" run "$tmp/prover.img" main "$tmp/$f.in" "$tmp/$f.out"
  bench "prove/$f ($(od -An -tu1 "$tmp/$f.out" | tr -d ' ') ok)" \
    "$kernel" run "$tmp/prover.img" main "$tmp/$f.in" "$tmp/$f.out"
done
