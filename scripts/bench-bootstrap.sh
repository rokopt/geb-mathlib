#!/usr/bin/env bash
#
# scripts/bench-bootstrap.sh [ROUNDS]
# scripts/bench-bootstrap.sh snapshot DIR
# scripts/bench-bootstrap.sh compare DIR_A DIR_B [ROUNDS]
#
# Time the bootstrap's programs on their own sources, one heavy process at a
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
#
# A build is a directory holding bin/geb-kernel, bin/geb-compile and the
# bootstrap/ sources. `snapshot DIR` builds the working copy's binaries and
# copies them and its sources into DIR. Without a mode the working copy is
# snapshotted to a temporary directory and timed; `compare` times two
# snapshots, alternating their order from round to round, and prints the
# ratio of the second's medians to the first's with a 95% bootstrap
# interval.
#
# Byte-identical copies of a binary can differ in speed by up to a quarter,
# reproducibly per copy (measured on a WSL2 host), so one copy per build can
# show a difference between builds that is only where the copies' pages lie.
# Each build is therefore timed over COPIES (default 4) copies of its
# binaries, each written anew and used in every COPIES-th of the ROUNDS
# (default 16) rounds after a warm-up of every copy, and the medians of each
# copy are printed beside the whole ones, so that a slow copy shows.

set -euo pipefail
cd "$(dirname "$0")/.."

usage() {
  sed -n '3,5p' "$0" | sed 's/^# /usage: /' >&2
  exit 2
}

snapshot() {
  lake build geb-kernel geb-compile > /dev/null
  mkdir -p "$1/bin"
  cp .lake/build/bin/geb-kernel .lake/build/bin/geb-compile "$1/bin/"
  rm -rf "$1/bootstrap"
  cp -r bootstrap "$1/bootstrap"
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

case "${1:-}" in
  snapshot)
    [ $# -eq 2 ] || usage
    snapshot "$2"
    exit 0 ;;
  compare)
    [ $# -ge 3 ] && [ $# -le 4 ] || usage
    builds=("$(realpath "$2")" "$(realpath "$3")")
    rounds=${4:-16} ;;
  '' | [0-9]*)
    [ $# -le 1 ] || usage
    rounds=${1:-16}
    snapshot "$tmp/work"
    builds=("$tmp/work") ;;
  *) usage ;;
esac

python3 - "$rounds" "${COPIES:-4}" "$tmp" "${builds[@]}" <<'PY'
import os, random, shutil, statistics, subprocess, sys, time

rounds, copies, tmp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
builds = sys.argv[4:]

STAGE0 = ["prelude", "serialize", "reader", "check", "datatype", "compile"]
STAGE1 = ["prelude", "serialize", "reader", "check", "stage1/datatype", "compile",
          "stage1/lean"]
PROVER = ["prelude", "reader", "check", "datatype", "goedel-t/equations", "goedel-t/prove"]
# the prover's entry point, giving the number of theorems the Geb checker accepts
PROVER_MAIN = b"""(def main (lam ((file T)) (node 0 (single (foldr T T (lam ((x T) (n T))
    (if (eq (label (child x 3)) 1) (add n 1) n)) 0 (children (child (child (proveFile 256 file) 0) 1)))))))
"""
PROOFS = {
    "prelude": ["prelude", "proofs/prelude"],
    "nat": ["prelude", "proofs/nat"],
    "check": ["prelude", "reader", "check", "proofs/check"],
    "equations": ["prelude", "reader", "check", "goedel-t/equations", "proofs/equations"],
    "datatype": ["prelude", "reader", "check", "proofs/datatype"],
}


def join(paths, out):
    with open(out, "wb") as f:
        for p in paths:
            with open(p, "rb") as g:
                f.write(g.read())
            f.write(b"\n")


def prepare(i, d):
    """The build's inputs, its workloads as (binary, arguments), and its copies' directories."""
    b, t = os.path.join(d, "bootstrap"), os.path.join(tmp, str(i))
    os.makedirs(t)
    src = lambda xs: [os.path.join(b, x + ".geb") for x in xs]
    at = lambda x: os.path.join(t, x)
    kernel = os.path.join(d, "bin", "geb-kernel")
    join(src(STAGE1), at("S.geb"))
    subprocess.run([kernel, "build", *src(STAGE0), at("stage0.img")], check=True,
                   stdout=subprocess.DEVNULL)
    join(src(PROVER), at("prover.geb"))
    with open(at("prover.geb"), "ab") as f:
        f.write(PROVER_MAIN)
    subprocess.run([kernel, "run", at("stage0.img"), "main", at("prover.geb"), at("prover.img")],
                   check=True)
    if os.path.getsize(at("prover.img")) == 0:
        sys.exit(f"bench-bootstrap: the stage-0 compiler of {d} rejects the prover")
    work = {
        "compile/native": ("geb-compile", ["image", at("S.geb"), at("out.img")]),
        "compile/seed": ("geb-kernel", ["run", os.path.join(b, "compiler.img"), "main",
                                        at("S.geb"), at("out.img")]),
    }
    for f, xs in PROOFS.items():
        join(src(xs), at(f + ".in"))
        work["prove/" + f] = ("geb-kernel", ["run", at("prover.img"), "main", at(f + ".in"),
                                             at(f + ".out")])
    bins = []
    for c in range(copies):
        cb = at(f"bin{c}")
        os.makedirs(cb)
        for x in ("geb-kernel", "geb-compile"):
            shutil.copyfile(os.path.join(d, "bin", x), os.path.join(cb, x))
            os.chmod(os.path.join(cb, x), 0o755)
        bins.append(cb)
    return work, bins, t


def once(cmd):
    s = time.perf_counter()
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL)
    return time.perf_counter() - s


preps = [prepare(i, d) for i, d in enumerate(builds)]
names = list(preps[0][0])
cmd = lambda p, c, f: [os.path.join(p[1][c], p[0][f][0])] + p[0][f][1]
for p in preps:
    for c in range(copies):
        for f in names:
            once(cmd(p, c, f))
accepted = [{f: "".join(str(x) for x in open(os.path.join(p[2], f[6:] + ".out"), "rb").read())
             for f in names if f.startswith("prove/")} for p in preps]
times = [{f: [[] for _ in range(copies)] for f in names} for _ in preps]
for r in range(rounds):
    order = list(range(len(preps)))
    if r % 2:
        order.reverse()
    for f in names:
        for i in order:
            times[i][f][r % copies].append(once(cmd(preps[i], r % copies, f)))


def q(xs, p):
    xs = sorted(xs)
    k = p * (len(xs) - 1)
    lo = int(k)
    return xs[lo] + (xs[min(lo + 1, len(xs) - 1)] - xs[lo]) * (k - lo)


def summary(i, f):
    xs = [x for c in times[i][f] for x in c]
    return f"{statistics.median(xs):.3f} [{q(xs, .25):.3f},{q(xs, .75):.3f}]"


def per_copy(i, f):
    return " ".join(f"{statistics.median(c):.3f}" for c in times[i][f] if c)


def name(f):
    ok = " | ".join(a[f] for a in accepted) if f in accepted[0] else ""
    return f + (f" ({ok} ok)" if ok else "")


width = max(len(name(f)) for f in names)
if len(preps) == 1:
    print(f"{'workload':{width}}  {'median [IQR]':>21}  per copy")
    for f in names:
        print(f"{name(f):{width}}  {summary(0, f):>21}  {per_copy(0, f)}")
else:
    random.seed(0)
    print(f"{'workload':{width}}  {'A median [IQR]':>21}  {'B median [IQR]':>21}  "
          f"{'B/A':>5}  {'95% interval':>13}  per copy A | B")
    for f in names:
        a = [x for c in times[0][f] for x in c]
        b = [x for c in times[1][f] for x in c]
        boot = sorted(statistics.median(random.choices(b, k=len(b))) /
                      statistics.median(random.choices(a, k=len(a))) for _ in range(4000))
        ratio = statistics.median(b) / statistics.median(a)
        print(f"{name(f):{width}}  {summary(0, f):>21}  {summary(1, f):>21}  {ratio:5.3f}  "
              f"[{boot[100]:.3f},{boot[3899]:.3f}]  {per_copy(0, f)} | {per_copy(1, f)}")
PY
