# Tree-recognizer workstream — session handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [Which document owns what](#which-document-owns-what)
- [Where the line stands](#where-the-line-stands)
- [What this session delivered](#what-this-session-delivered)
- [What remains](#what-remains)
- [What to pick up next](#what-to-pick-up-next)
- [Context the next session will want](#context-the-next-session-will-want)
- [Loose ends](#loose-ends)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Read these first

- [CONTRIBUTING.md](../../../CONTRIBUTING.md),
  [AGENTS.md](../../../AGENTS.md), [CLAUDE.md](../../../CLAUDE.md).
- [docs/rules/lean-coding.md](../../rules/lean-coding.md),
  [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md),
  [docs/rules/markdown-writing.md](../../rules/markdown-writing.md),
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md).
- [The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) —
  the branch-by-branch record for B3 to B6, and the Lean facts each cost
  a failed build to learn. Read it before writing any Lean here.
- [TODO.md](../../../TODO.md) § Extensions of the tree recognizers, and
  [docs/index.md](../../index.md) for what is implemented.

## Which document owns what

Two handoffs sit in this directory, and they are not interchangeable.
Keep an edit in the one that owns the subject, so they do not drift.

- [The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) owns
  the description of each remaining branch, the constraints each carries,
  the deferrals, and the accumulated Lean facts. It outlives this
  session.
- This document owns the state of the line, what the last session
  delivered, and what to pick up next. Replace it when that state
  changes; it is transient in the sense
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape gives.

## Where the line stands

One line off `main`, with a bookmark at each segment boundary. `jj`
pushes each segment as its own pull request, so the segments remain
separately submittable while the commits stay in one chain; stacking is
deliberate and avoids the conflicts parallel branches over the same
files produce.

```text
main                          f8e824b2   PR #134, merged
  └─ feat/ranked-tree-recognizers  c9adda16   B1, unpushed
       └─ feat/cobham-scanner      23e94d52   B2, unpushed
```

Nothing in either segment has been pushed.
[AGENTS.md](../../../AGENTS.md) § No `jj git push` without user
line-by-line review binds: the user reviews a segment's diff before it
goes anywhere, first creation included.

At `23e94d52` the tree is clean and every gate passes: `lake build`
(1260 jobs), `lake test`, `lake lint`, and `scripts/pre-push.sh` in full,
which adds the import linter, `lake shake`, and the Markdown, table-of-
contents and link checks.

## What this session delivered

B2, the scan combinator, in eleven commits `b1a5af61..23e94d52`.

- `Geb/Mathlib/Computability/Cobham/Scan.lean` — a right-to-left fold
  over a bitstring whose state is a bitstring, as a `boundedRec` node of
  the class. `scanRaw` assembles the node from a base, two steps of
  arity one lifted by `liftRaw`, and the bound child `boundRaw`;
  `wValid_scanRaw` gives admissibility from the components' own together
  with their index equations; `scanSem` is the meaning read at the raw
  tree; `scanSem_eq` identifies it with `List.foldr`; `scan` takes a
  length bound on that meaning and yields a member of the class.
- `Geb/Mathlib/Computability/Cobham/Basic.lean` gained
  `transport_transport`.
- `Geb/Mathlib/Computability/Cobham/Tree.lean` — the recognizer's scan
  rebuilt on the combinator, its two steps dropped to arity one, and
  `combOf`/`combSem_eq_eval` now the combinator's own `scanOf` and
  `scanSem_eq_eval` rather than independent re-derivations. Everything
  from `combSem_eq` downward keeps its form, and
  `GebTests/Mathlib/Computability/Cobham/Tree.lean` passes unedited,
  which is the evidence the recognizer is unchanged.
- `GebTests/Mathlib/Computability/Cobham/Scan.lean` mirrors the module.
- `docs/index.md`, `TODO.md` and the workstream handoff record it; B2's
  own spec and plan were removed in the branch's final commits.

The generic ranked recognizer was moved out of B2 into its own entry,
B6, since nothing depended on it and its state layout is undecided.

## What remains

The workstream handoff carries each of these in full; this is the index.

- **B3**, depending on B2 — `Cobham/Fold.lean`, the catamorphism at a
  finite carrier.
- **B4**, depending on B1 and B2 — `BinTree` absorbed into
  `RankedAlphabet.Term`, and the duplication in
  `Geb/Mathlib/Data/Tree/Preorder.lean` removed.
- **B5**, depending on B2 — linear time and space against Cslib's
  `MultiTapeTM`, confined to `Geb/Internal/`. Differs in kind from the
  others; B1 to B4 and B6 stand without it.
- **B6**, depending on B2 and B1 — the generic ranked recognizer as a
  scanner instance. Its state layout is the open design question: the
  step must dispatch on `2 ^ width` block values against
  `RankedAlphabet.arOf`, so the dispatch is built by recursion on
  `width` rather than written out.

## What to pick up next

B3 is the recommendation, for a reason particular to how B2 finished.
The whole-branch review judged the combinator earned at its core and not
at its periphery: `scanSem_eq` is new mathematical content, but the
module has one instantiation, and an interface with one implementation
is what [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost warns
against. B3 is the second instantiation, and it consumes `scanSem_eq`
directly. Building it settles the question the review left open, and it
will show quickly whether the interface is the right one — while it is
still cheap to change, since B2 is unpushed.

B4 is the cheaper branch and the one that completes the workstream's
stated goal, no tree encoding defined twice. Take it first if a short
branch is wanted; it needs the bridge B1 already delivers,
`RankedAlphabet.Binary.valid_iff`, and little else.

Either way the phase is brainstorming: neither has a spec.

## Context the next session will want

**The transport constraint is the one design fact that is not read off
the signatures.** `Cobham.transport` along an equation whose two sides
reduce to the same literal disappears by proof irrelevance; along an
opaque equation it does not, and a transport along a composite equality
is then not definitionally the composition of two transports. A scan
node's own arity reduces to one whatever its children are, so its
transport disappears; a component's arity equation is `base.2` or
`step.2` at a variable, which reduces to nothing. That is why the
component meanings are stated in composed-transport form, and it is
recorded in `Scan.lean`'s implementation notes. Expect the same shape of
problem in any further construction over expressions of the class.

**`decide` discharges admissibility only at a named constant.** Instance
search finds `Decidable (sig.WValid w)` when `w` is a constant but not
when it is a literal `WType.mk` application. This is why every
construction is split into a `…Raw` constant and the expression built on
it, and it is stated in `Basic.lean` and `Tree.lean`. A draft that
inlines a tree will not compile.

**Prototype while reviewing, not after.** B2's spec went through four
adversarial rounds. Rounds one and two found real defects, several of
which only a compiler would have caught, because a throwaway module
under `Geb/Internal/` compiled every Lean claim the spec made as the
review ran. Rounds three and four found only bookkeeping in the spec's
prose, and round four reported that three of its five serious findings
were introduced by round three's own fixes. When revisions start
generating defects at the rate they remove them, the artifact has
stopped converging; surface the trend rather than looping further. The
prototype is deleted before the module it prototypes lands — it carries
`open Cobham` and its own names, which collide once the real module
exists.

**Subagent-driven execution worked without a fix loop here**, over nine
tasks, because the plan carried compiled code rather than descriptions
of code. Where it carried a draft instead — the test mirror — the
implementer had to depart from it three times. A plan step is worth
writing out in full only to the extent it has been built.

## Loose ends

- The bookmark `doc/todo-cobham-deferrals` at `0d14ecfd` is an ancestor
  of neither `main` nor the stack. Decide whether its content is wanted
  and either fold it into the line or drop the bookmark.
- `docs/references.bib` still has no key for `BarringtonCorbett1989`,
  nor for the three succinct-tree references the design cites for
  context. They are verified but uncited, and belong to the branch that
  first cites one, which is expected to be B5.
