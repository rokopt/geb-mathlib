#!/usr/bin/env python3
"""Compare the verdicts of the search written in Geb with those of the search with z3,
without z3's check per use of every definition, which need not finish on a large program.

    python3 scripts/eal/compare.py DEFS OUT

DEFS holds a program's definitions, as `lake exe geb-defs IMAGE DEFS` writes them, and OUT
is what `scripts/eal/search.sh DEFS OUT` writes for them. The comparison has three parts:

  1. z3's check of each definition alone (check_local), on every definition, against the
     search's rejections alone;
  2. z3's check per use (check_per_use), on the definitions the search's certificate does
     not cover and those they use, against the search's rejections per use. Every other
     definition is exempt, which leaves these verdicts as they are in a check of the whole
     program, a definition's constraints depending only on the definitions it uses;
  3. of the remaining definitions, the certificate alone: z3 is not run on them per use,
     and the search accepted the certificate by bootstrap/affine.geb before writing that it
     is checked. This part assumes that the constraints of eal.py admit every decoration
     the checker accepts.

Exits with 0 when no verdict differs, 1 when one does. Requires the z3-solver package.
"""

import argparse
import re
import sys

import eal


def verdicts(path):
    """The rejections alone and per use that the search wrote to path, and the positions of
    the definitions its certificate covers."""
    lines = open(path).read().splitlines()
    if not any(re.search(r"^certificate: .*, checked$", l) for l in lines):
        sys.exit(f"compare: {path} records no checked certificate")

    def named(prefix):
        return {l[len(prefix):].split()[0] for l in lines if l.startswith(prefix)}
    covered, depth = set(), 0
    for m in re.finditer(r"\((\d+)|\)", lines[-1]):
        if m.group(1) is None:
            depth -= 1
        else:
            depth += 1
            if depth == 2:
                covered.add(int(m.group(1)))
    return named("  NOT TYPABLE: "), named("  NOT TYPABLE PER USE: "), covered


def closure(roots, uses, excluded):
    """roots and the definitions they use, stopping at those in excluded."""
    out, todo = set(), list(roots)
    while todo:
        i = todo.pop()
        if i not in out and i not in excluded:
            out.add(i)
            todo.extend(uses[i])
    return out


def report(part, ours, theirs):
    print(f"{part}: z3 rejects {sorted(ours)}; the search rejects {sorted(theirs)}")
    return ours == theirs


def main():
    ap = argparse.ArgumentParser(description="Compare the searches' verdicts on a program.")
    ap.add_argument("defs")
    ap.add_argument("out")
    args = ap.parse_args()
    defs = eal.load(args.defs)
    names = [n for n, _ in defs]
    alone, per_use, covered = verdicts(args.out)
    bad = {n for n, _, r in eal.check_local(defs) if r != eal.z3.sat}
    same = report("alone", bad, alone)
    rejected = {i for i, n in enumerate(names) if n in bad | alone}
    uncovered = [i for i in range(len(defs)) if i not in covered | rejected]
    globs, uses = [], []
    for name, body in defs:
        t = eal.Template(name, body, globs)
        globs.append((name, t.ty, None))
        uses.append({j for j, _, _ in t.uses})
    near = closure(uncovered, uses, rejected)
    worse, _ = eal.check_per_use(defs, set(range(len(defs))) - near)
    same = report("per use", {n for n, _, _ in worse}, per_use) and same
    print(f"{len(covered)} definitions covered by the certificate; {len(near)} checked per use"
          f" by z3, {len(uncovered)} of them not covered")
    print("no verdict differs" if same else "verdicts differ")
    sys.exit(0 if same else 1)


if __name__ == "__main__":
    main()
