#!/usr/bin/env python3
"""Elementary-affine typability of the definitions of a Geb kernel program.

    python3 scripts/eal/eal.py [--pure] [--explain NAME] DEFS

DEFS is a program's definitions in the form `lake exe geb-defs IMAGE DEFS` writes: one per
line, the name, a tab, and the kernel term as an S-expression of labels; lines beginning
with `#` are comments. The checker decides, for each definition, whether its term admits an
elementary-affine decoration in the style of Coppola and Martini (Optimizing optimal
reduction, ACM TOCL 7(2), 2006; arXiv:cs/0305011): a number of boxes on every edge of the
term and a number of `!` on every node of its simple type, subject to linear constraints,
solved by z3. It then checks the typable definitions together, each with one decoration
shared by all its references.

The rules:
  * types without arrows are first-order data: freely contracted and promoted, no
    constraints (`--pure` removes this exemption, so that data obey the discipline);
  * a variable occurrence under p boxes from its binder sees !^(k-p) A, and needs k >= p;
  * a non-data variable, or a place reached from one by projections, used twice needs
    k >= 1 (contraction);
  * no dereliction: a function in application position, a pair under a projection and a
    list consumed by a constant all have no `!` as seen;
  * iter_A  : !(A -o A) -o !A -o T -o !A
    fold_A, para_A : !(T -o List A -o A) -o T -o !A, para's step receiving the node that
      its recursion also consumes, a copy of data that para makes as a primitive and that
      elementary affine logic proper cannot define, so that even under `--pure` para
      assumes the copying of data natively
    foldr_AB: !(A' -o B -o B) -o !B -o List A -o !B, where A = !A'
    lcase_AB: List A -o B -o (A -o List A -o B) -o B, its branches additive when saturated;
  * the branches of a conditional are additive;
  * the projections of a variable are split into places (tensor elimination);
  * references to definitions are closed: freely duplicated and boxed. Checked one at a
    time, each reference takes a decoration of its own, so that a definition typable alone
    is typable whenever each of its callees is typable at the decoration it is used at.

For a definition that is not typable the checker prints a minimal set of the constraints
that conflict; `--explain NAME` tracks every constraint of that definition, each labelled
with the rule that added it, and prints a minimal conflicting set.

Status: a measurement tool. Elementary affine logic proper (`--pure`) is what the
soundness of the oracle-free optimal-reduction algorithm is proved for (Baillot, Coppola
and Dal Lago, arXiv:0704.2448); the exemption of first-order data is not proved sound for
such a machine, and a typing of a whole program needs a decoration per use of a
definition where one per definition fails. Requires the z3-solver package
(scripts/eal/requirements.txt).
"""
import argparse
import sys
import traceback

import z3

# ---------------------------------------------------------------- parsing

def parse(s):
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def go():
        nonlocal pos
        assert toks[pos] == "("
        pos += 1
        lab = int(toks[pos]); pos += 1
        kids = []
        while toks[pos] != ")":
            kids.append(go())
        pos += 1
        return (lab, kids)
    return go()


def load(path):
    defs = []
    for line in open(path):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        name, body = line.split("\t", 1)
        defs.append((name, parse(body)))
    return defs

# ---------------------------------------------------------------- simple types

T, UNIT, PROD, ARROW, LIST = 0, 1, 2, 3, 4
tT = (T, [])
tUnit = (UNIT, [])
def tArrow(a, b): return (ARROW, [a, b])
def tProd(a, b): return (PROD, [a, b])
def tList(a): return (LIST, [a])


def is_data(ty):
    return ty[0] != ARROW and all(is_data(c) for c in ty[1])


def show_ty(ty):
    l, c = ty
    return {T: lambda: "T", UNIT: lambda: "1",
            PROD: lambda: f"({show_ty(c[0])} x {show_ty(c[1])})",
            ARROW: lambda: f"({show_ty(c[0])} -> {show_ty(c[1])})",
            LIST: lambda: f"[{show_ty(c[0])}]"}[l]()

# ---------------------------------------------------------------- decorated types
# A decorated type is (shape, bang, kids): shape the simple type, bang a z3 Int
# expression (the number of ! in front of this node), kids decorated children.


class Ctx:
    def __init__(self):
        self.solver = z3.Solver()
        self.n = 0
        self.tag = None      # current assumption literal
        self.tags = {}       # literal -> description
        self.track = False

    def var(self, base="v"):
        self.n += 1
        v = z3.Int(f"{base}{self.n}")
        self.solver.add(v >= 0)
        return v

    def add(self, c, why=None):
        if self.track == "all":
            why = why or "rule at line " + str(traceback.extract_stack()[-2].lineno)
        if why is not None and self.track:
            lit = z3.Bool(f"why{len(self.tags)}")
            self.tags[lit] = why
            self.solver.add(z3.Implies(lit, c))
        elif self.tag is None:
            self.solver.add(c)
        else:
            self.solver.add(z3.Implies(self.tag, c))

    def fresh(self, ty):
        if is_data(ty):
            return zero(ty)
        return (ty, self.var("b"), [self.fresh(c) for c in ty[1]])

    def eq(self, d1, d2):
        assert d1[0] == d2[0], (show_ty(d1[0]), show_ty(d2[0]))
        if is_data(d1[0]):
            return
        self.add(d1[1] == d2[1])
        for a, b in zip(d1[2], d2[2]):
            self.eq(a, b)

    def nonneg(self, d):
        if not is_data(d[0]):
            self.add(d[1] >= 0)


def zero(ty):
    return (ty, z3.IntVal(0), [zero(c) for c in ty[1]])


def shift(d, e):
    if is_data(d[0]):
        return d
    return (d[0], d[1] + e, d[2])


def node(ty, kids, bang=0):
    return (ty, z3.IntVal(bang), kids)

# ---------------------------------------------------------------- analysis

class Walker:
    def __init__(self, cx, globs, mode):
        self.cx = cx
        self.globs = globs      # list of (name, simple type, decorated type)
        self.mode = mode        # "local": fresh decoration per reference
        self.places = {}        # place -> (decorated type, depth of binder)
        self.nbind = 0
        self.binders = {}

    # A place is (binder id, path of projections).
    def place_type(self, pl):
        bid, path = pl
        d, _ = self.places[(bid, ())]
        for i in path:
            d = shift(d[2][i], d[1]) if not is_data(d[0]) else d[2][i]
        return d

    def occurrence(self, pl, depth):
        d = self.place_type(pl)
        if is_data(d[0]):
            return d
        _, dbind = self.places[(pl[0], ())]
        p = depth - dbind
        self.cx.add(d[1] - p >= 0, f"occurrence of {show_ty(d[0])} (binder #{pl[0]} {self.binders.get(pl[0])}, place {pl[1]}) under more boxes than its !s")
        return shift(d, -p)

    def child(self, t, ctx, depth, desc):
        # b > 0 enters boxes, b < 0 leaves them through a door (the child is the door's term)
        self.cx.n += 1
        b = z3.Int(f"box{self.cx.n}")
        dc = depth + b
        self.cx.add(dc >= 0)
        ty, d, counts = self.walk(t, ctx, dc, desc)
        for pl in counts:                              # no occurrence leaves its binder's box
            self.cx.add(dc - self.places[(pl[0], ())][1] >= 0, f"scope: binder #{pl[0]} {self.binders.get(pl[0])}")
        if not is_data(ty):
            self.cx.add(d[1] + b >= 0, f"door: {show_ty(ty)} leaves a box without a !")
        return ty, shift(d, b), counts

    def walk(self, t, ctx, depth, desc):
        cx = self.cx
        lab, ks = t
        if lab == 8:                                   # var
            n = ks[0][0]
            ty, bid = ctx[n]
            pl = (bid, ())
            return ty, self.occurrence(pl, depth), {pl: 1}
        if lab in (13, 14):                            # fst / snd
            path, inner = [], t
            while inner[0] in (13, 14):
                path.append(0 if inner[0] == 13 else 1)
                inner = inner[1][0]
            if inner[0] == 8:                          # projection of a variable: a place
                ty, bid = ctx[inner[1][0][0]]
                path = tuple(reversed(path))
                for i in path:
                    ty = ty[1][i]
                pl = (bid, path)
                return ty, self.occurrence(pl, depth), {pl: 1}
            ty, d, c = self.child(ks[0], ctx, depth, desc)
            if ty[0] != PROD:
                raise TypeError("projection of a non-pair")
            cx.add(d[1] == 0, f"no dereliction: project {show_ty(ty)}") if not is_data(ty) else None
            i = 0 if lab == 13 else 1
            return ty[1][i], d[2][i], c
        if lab == 9:                                   # lam
            A = ks[0]
            self.nbind += 1
            bid = self.nbind
            self.binders[bid] = f"lam {show_ty(A)} under {desc}"
            dA = cx.fresh(A)
            self.places[(bid, ())] = (dA, depth)
            tb, db, c = self.child(ks[1], [(A, bid)] + ctx, depth, desc)
            self.contraction(bid, c)
            c = {k: v for k, v in c.items() if k[0] != bid}
            return tArrow(A, tb), node(tArrow(A, tb), [dA, db]), c
        if lab == 10:                                  # app
            spine, head = [], t
            while head[0] == 10:
                spine.append(head[1][1])
                head = head[1][0]
            spine.reverse()
            if head[0] == 24 and len(spine) == 3:      # saturated lcase: additive branches
                return self.lcase(head, spine, ctx, depth, desc)
            tf, df, cf = self.child(ks[0], ctx, depth, desc)
            tx, dx, cxs = self.child(ks[1], ctx, depth, desc)
            if tf[0] != ARROW or tf[1][0] != tx:
                raise TypeError(f"ill-typed application {show_ty(tf)} to {show_ty(tx)}")
            cx.add(df[1] == 0, f"no dereliction: apply {show_ty(tf)}")
            cx.eq(df[2][0], dx)
            return tf[1][1], df[2][1], add(cf, cxs)
        if lab in (11, 15):                            # unit, quote
            ty = tUnit if lab == 11 else tT
            return ty, zero(ty), {}
        if lab == 12:                                  # pair
            ta, da, ca = self.child(ks[0], ctx, depth, desc)
            tb, db, cb = self.child(ks[1], ctx, depth, desc)
            ty = tProd(ta, tb)
            return ty, node(ty, [da, db]), add(ca, cb)
        if lab == 16:                                  # cond: additive branches
            _, _, cc = self.child(ks[0], ctx, depth, desc)
            ta, da, ca = self.child(ks[1], ctx, depth, desc)
            tb, db, cb = self.child(ks[2], ctx, depth, desc)
            cx.eq(da, db)
            return ta, da, add(cc, mx(ca, cb))
        if lab == 19:                                  # nil
            ty = tList(ks[0])
            return ty, node(ty, [cx.fresh(ks[0])]), {}
        if lab == 20:                                  # cons
            tx, dx, c1 = self.child(ks[0], ctx, depth, desc)
            tl, dl, c2 = self.child(ks[1], ctx, depth, desc)
            if not is_data(tl):
                cx.add(dl[1] == 0, f"no dereliction: cons onto {show_ty(tl)}")
                cx.eq(dl[2][0], dx)
            return tl, node(tl, [dx]), add(c1, c2)
        if lab in (17, 18, 21, 24, 25):
            return self.constant(t)
        if lab == 22:                                  # primitive: data
            ty = PRIMS[ks[0][0]]
            return ty, zero(ty), {}
        if lab == 23:                                  # ref: closed
            name, ty, d = self.globs[ks[0][0]]
            if self.mode == "local":
                d = cx.fresh(ty)
            return ty, d, {}
        raise ValueError(f"label {lab}")

    def constant(self, t):
        cx = self.cx
        lab, ks = t
        if lab == 18:                                  # iter
            A = ks[0]; dA = cx.fresh(A)
            step = node(tArrow(A, A), [dA, dA], 1)
            res = shift(dA, 1)
            ty = tArrow(tArrow(A, A), tArrow(A, tArrow(tT, A)))
            return ty, node(ty, [step, node(ty[1][1], [res, node(ty[1][1][1][1], [zero(tT), res])])]), {}
        if lab in (17, 25):                            # fold, and para (the step sees the node)
            A = ks[0]; dA = cx.fresh(A)
            sty = tArrow(tT, tArrow(tList(A), A))
            step = node(sty, [zero(tT), node(sty[1][1], [node(tList(A), [dA]), dA])], 1)
            ty = tArrow(sty, tArrow(tT, A))
            return ty, node(ty, [step, node(ty[1][1], [zero(tT), shift(dA, 1)])]), {}
        if lab == 21:                                  # foldr
            A, B = ks[0], ks[1]
            dA, dB = cx.fresh(A), cx.fresh(B)
            if not is_data(A):
                cx.add(dA[1] >= 1, f"foldr over a list of {show_ty(A)} needs boxed elements")
            dA1 = shift(dA, -1)
            sty = tArrow(A, tArrow(B, B))
            step = node(sty, [dA1, node(sty[1][1], [dB, dB])], 1)
            rest = tArrow(B, tArrow(tList(A), B))
            ty = tArrow(sty, rest)
            dB1 = shift(dB, 1)
            return ty, node(ty, [step, node(rest, [dB1, node(rest[1][1], [node(tList(A), [dA]), dB1])])]), {}
        if lab == 24:                                  # lcase, unsaturated
            A, B = ks[0], ks[1]
            dA, dB = cx.fresh(A), cx.fresh(B)
            cty = tArrow(A, tArrow(tList(A), B))
            dc = node(cty, [dA, node(cty[1][1], [node(tList(A), [dA]), dB])])
            ty = tArrow(tList(A), tArrow(B, tArrow(cty, B)))
            return ty, node(ty, [node(tList(A), [dA]), node(ty[1][1], [dB, node(ty[1][1][1][1], [dc, dB])])]), {}
        raise ValueError(lab)

    def lcase(self, head, spine, ctx, depth, desc):
        cx = self.cx
        tl_, dl, c1 = self.child(spine[0], ctx, depth, desc)
        tn, dn, c2 = self.child(spine[1], ctx, depth, desc)
        tc, dc, c3 = self.child(spine[2], ctx, depth, desc)
        A, B = head[1][0], head[1][1]
        if tl_ != tList(A) or tn != B or tc != tArrow(A, tArrow(tList(A), B)):
            raise TypeError("ill-typed lcase")
        if not is_data(tl_):
            cx.add(dl[1] == 0, f"no dereliction: lcase on {show_ty(tl_)}")
        if not is_data(tc):
            cx.add(dc[1] == 0, 'no dereliction: lcase branch')
            cx.add(dc[2][1][1] == 0, 'no dereliction: lcase branch')
            cx.eq(dc[2][0], dl[2][0])
            cx.eq(dc[2][1][2][0], dl)
            cx.eq(dc[2][1][2][1], dn)
        return B, dn, add(c1, mx(c2, c3))

    def contraction(self, bid, counts):
        """A place used more than once, or used beside a sub-place, needs a !."""
        mine = {k[1]: v for k, v in counts.items() if k[0] == bid}

        def go(path):
            d = self.place_type((bid, path))
            if is_data(d[0]):
                return
            direct = mine.get(path, 0)
            subs = [p for p in mine if len(p) > len(path) and p[:len(path)] == path]
            if direct >= 2 or (direct >= 1 and subs):
                self.cx.add(d[1] >= 1, f"contraction of {show_ty(d[0])} at place {path} of binder #{bid} ({self.binders[bid]}), uses={direct}, subplaces={len(subs)}")
            elif not direct:
                for i in (0, 1):
                    if any(p[:len(path) + 1] == path + (i,) for p in subs):
                        go(path + (i,))
        go(())


def add(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + v
    return r


def mx(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = max(r.get(k, 0), v)
    return r


_b = tArrow(tT, tArrow(tT, tT))
PRIMS = [tArrow(tT, tT), tArrow(tT, tT), _b, tArrow(tT, tArrow(tList(tT), tT)),
         tArrow(tT, tList(tT)), _b, _b, _b, _b, _b, _b, _b, _b, tArrow(tT, tT)]

# ---------------------------------------------------------------- driver


def check_local(defs):
    """Each definition alone, references fresh (optimistic about callees)."""
    globs, results = [], []
    for name, body in defs:
        cx = Ctx()
        w = Walker(cx, globs, "local")
        ty, d, _ = w.walk(body, [], z3.IntVal(0), name)
        globs.append((name, ty, zero(ty)))
        r = cx.solver.check()
        if r != z3.sat:
            cx2 = Ctx(); cx2.track = True
            w2 = Walker(cx2, globs[:-1], "local")
            w2.walk(body, [], z3.IntVal(0), name)
            lits = list(cx2.tags)
            assert cx2.solver.check(*lits) == z3.unsat
            core = cx2.solver.unsat_core()
            # shrink to a minimal core
            core = list(core)
            i = 0
            while i < len(core):
                trial = core[:i] + core[i+1:]
                if cx2.solver.check(*trial) == z3.unsat:
                    core = trial
                else:
                    i += 1
            r = (r, [cx2.tags[l] for l in core])
        results.append((name, ty, r))
    return results


def check_global(defs, skip=()):
    """All definitions together, each with one decoration shared by its references;
    definitions in skip contribute a free decoration and no constraints."""
    cx = Ctx()
    globs = []
    lits = []
    for name, body in defs:
        lit = z3.Bool(f"def_{len(globs)}")
        cx.tag = lit
        w = Walker(cx, globs, "global")
        if name in skip:
            cx.tag = None
            ty, _, _ = Walker(Ctx(), globs, "local").walk(body, [], z3.IntVal(0), name)
            d = cx.fresh(ty)
            cx.tag = lit
        else:
            ty, d, _ = w.walk(body, [], z3.IntVal(0), name)
        globs.append((name, ty, d))
        lits.append(lit)
    r = cx.solver.check(*lits)
    core = [] if r == z3.sat else [globs[int(str(l)[4:])][0] for l in cx.solver.unsat_core()]
    return r, core



def minimal(solver, lits):
    """A minimal subset of the tracked constraints that is unsatisfiable."""
    assert solver.check(*lits) == z3.unsat
    core = list(solver.unsat_core())
    i = 0
    while i < len(core):
        trial = core[:i] + core[i + 1:]
        if solver.check(*trial) == z3.unsat:
            core = trial
        else:
            i += 1
    return core


def explain(defs, target):
    globs = []
    for name, body in defs:
        cx = Ctx()
        if name == target:
            cx.track = "all"
            Walker(cx, globs, "local").walk(body, [], z3.IntVal(0), name)
            lits = list(cx.tags)
            if cx.solver.check(*lits) == z3.sat:
                print(f"{name} is typable")
                return
            for lit in minimal(cx.solver, lits):
                print("  " + cx.tags[lit])
            return
        ty, _, _ = Walker(cx, globs, "local").walk(body, [], z3.IntVal(0), name)
        globs.append((name, ty, zero(ty)))
    sys.exit(f"eal: no definition named {target}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Elementary-affine typability of kernel definitions.")
    ap.add_argument("--pure", action="store_true", help="first-order data obey the discipline")
    ap.add_argument("--explain", metavar="NAME", help="every constraint of NAME, minimal conflict")
    ap.add_argument("defs")
    args = ap.parse_args()
    if args.pure:
        is_data = lambda ty: False
    defs = load(args.defs)
    if args.explain:
        explain(defs, args.explain)
        sys.exit(0)
    res = check_local(defs)
    bad = [(n, ty, r) for n, ty, r in res if r != z3.sat]
    print(f"{len(defs)} definitions; {len(defs) - len(bad)} typable alone; {len(bad)} not")
    for n, ty, r in bad:
        print(f"  NOT TYPABLE: {n} : {show_ty(ty)}")
        for why in r[1]:
            print(f"      {why}")
    r, core = check_global(defs, {n for n, _, _ in bad})
    print(f"the typable definitions together, one decoration per definition: {r}")
    if core:
        print("  conflicting:", ", ".join(core))
