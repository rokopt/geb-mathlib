# Tree-recognizer workstream — session handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [Which document owns what](#which-document-owns-what)
- [Status of every roadmap item](#status-of-every-roadmap-item)
- [Where the line stands](#where-the-line-stands)
- [What this session delivered](#what-this-session-delivered)
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
- [The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) — the
  branch-by-branch record and the Lean facts each cost a failed build to
  learn. Read it before writing any Lean here.
- [The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md) —
  its § Segment 2 and § Segment 3 are the specification for the next two
  pieces of work. Its § Segment 1 is built and is history.
- [TODO.md](../../../TODO.md) § Extensions of the tree recognizers, and
  [docs/index.md](../../index.md) for what is implemented.

## Which document owns what

Two handoffs and one design sit in this tree, and they are not
interchangeable. Keep an edit in the one that owns the subject.

- [The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) owns
  the description of each remaining branch, the constraints each carries,
  the deferrals, and the accumulated Lean facts. It outlives this session.
- [The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md) owns
  the specification of segments 2 and 3. It is transient in the sense
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape gives, and is
  removed in the final commits of segment 3.
- This document owns the state of the line, what the last session
  delivered, and what to pick up next. Replace it when that state changes.

## Status of every roadmap item

The roadmap letters and the design's segment numbers are different
schemes, and conflating them has already caused one misreading. The case
combinator carries no letter: it is shared machinery both B6 and B3 need,
introduced because a dispatch over `2 ^ width` block values cannot be
written out at a symbolic width.

| Item | What it is | Status |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — ranked alphabets, the preorder encoding, the validity scan, `BinTree` as the two-symbol instance | Done, unpushed |
| B2 | `Cobham/Scan.lean` — the scan combinator, and `Cobham/Tree.lean` rebuilt on it | Done, unpushed |
| — | `Cobham/Cases.lean` — definition by cases, with the constant-word, iterated-predecessor and diagonal combinators in `Cobham/Basic.lean` | Done, unpushed |
| B6 | `Cobham/RankedTree.lean` — the generic ranked recognizer. Design § Segment 2 | **Not started** |
| B3 | `Cobham/Fold.lean` — the catamorphism at a carrier with a bit encoding. Design § Segment 3 | **Not started** |
| B4 | `BinTree` absorbed into `RankedAlphabet.Term`, the duplication in `Data/Tree/Preorder.lean` removed | Not started |
| B5 | `Geb/Internal/` — linear time and space against Cslib's `MultiTapeTM` | Not started |

Nothing has been pushed. [AGENTS.md](../../../AGENTS.md) § No `jj git push`
without user line-by-line review binds every segment, first creation
included.

## Where the line stands

One line off `main`, with a bookmark at each segment boundary. `jj` pushes
each segment as its own pull request, so the segments stay separately
submittable while the commits stay in one chain.

```text
main                              cfb6e2c7
  └─ feat/ranked-tree-recognizers  B1
       └─ feat/cobham-scanner      B2   0aef6df3
            └─ feat/cobham-cases   e560f184
```

`main` moved to `cfb6e2c7` (a Lean toolchain auto-update) after the line
was cut. Nothing on the line depends on it; rebase before pushing.

At `e560f184` the tree is clean and every gate passes: `lake build`
(1261 jobs), `lake test`, `lake lint`, `lake lint -- GebTests`, and
`scripts/pre-push.sh` in full, which adds the import linter, `lake shake`,
and the Markdown, table-of-contents and link checks.

## What this session delivered

The case combinator, in the commits from `150a4387` to `e560f184`.

- `Cobham/Cases.lean` — `bits` and its round trip against `List.ofFn`; the
  scrutinee shift; the case tree `casesRaw` with its admissibility and
  recursion bound; `casesSem_eq` identifying the meaning with the branch
  the scrutinee selects; and the words the `Cobham/Basic.lean` combinators
  contribute.
- `Cobham/Basic.lean` gained `semAt`, the `zeroAt` family moved in from
  `Cobham/Tree.lean`, and the `predIter`, `prepend`/`constAt` and `diag`
  families.
- `Cobham/Scan.lean` and `Cobham/Tree.lean` had six definitions restated
  through `semAt`, which names once what they each spelled out.
- `GebTests/Mathlib/Computability/Cobham/Cases.lean` mirrors the module.
- `docs/index.md` and `TODO.md` record it; the segment's own plan was
  removed in its final commits.

A `chore(vale)` commit at the base of the segment wires up the project's
Vale vocabulary, which `.vale.ini` had never selected. It is a separate
concern carried here by decision.

## What to pick up next

**Segment 2: the generic ranked recognizer, closing B6.** The design's
§ Segment 2 is its specification and is written to implementation detail.
It depends on the case combinator, which is now in place, and on B1's
`RankedAlphabet.Preorder`.

Its largest unbuilt piece is `decodeState`: the inverse of the state
layout, as a function of a bit family at a symbolic `dispatchWidth`. The
design routes it through `List.ofFn` and the `List` API rather than
indexing a `Fin` family, which removes the bound-threading that made it
hard, but none of it is compiled. Four statements it consumes are also
unbuilt and are specified in § Additions to the ranked-encoding modules.

Prototype `decodeState`, `nextPrefix` and `dropCount` at a symbolic `R`
before writing that segment's plan. The step arithmetic was verified by
hand at `narrowAlphabet` over every reachable state, and the step lemma
`stateWord_scanStep_of_lt` was proved in Lean for arbitrary `R` during
review, but both were built against throwaway modules since deleted.

## Context the next session will want

**Compile before planning; do not review prose describing Lean.** Four
adversarial rounds against a document describing Lean plateaued at about
one blocker a round, each introduced by the previous round's fix, and
every one of them was a signature that would not typecheck or a name never
declared. Building a prototype first, then reviewing the plan against it,
converged in three rounds, and the execution that followed ran twelve
tasks with no fix round at all. The plan carried transcribed compiled
code, so implementers transcribed rather than composed.

**A task-scoped review cannot see a module-scoped defect.** Every per-task
review of the last segment came back clean; the whole-segment review then
found two docstrings asserting the opposite of what their proofs did, and
a pair of tests that opened with a rewrite which replaced the construction
under test before anything computed. Budget for a final review that reads
the segment as one body of work.

**Two routes into `Classical.choice` are live in this material.** `omega`
discharging an `Iff` goal pulls it in, so an equivalence is proved from
its two implications; and `DecidableEq (Fin n → Bool)` resolves through
`Fintype.decidablePiFintype`, so a decision over a bit family is taken on
`List Bool` after `List.ofFn`. `ofFn_bits` proved through
`List.ext_getElem` and `omega` measured `Classical.choice`; the structural
induction that replaced it is clean.

**`lake lint` lints the `Geb` umbrella's import closure.** A module under
`Geb/Internal/` that no index imports is built by `lakefile.toml`'s glob
but never linted, and `scripts/tests/test-lint-driver.sh` fails on it. A
prototype left in the tree therefore fails `scripts/pre-push.sh`; measure
its axioms per declaration rather than trusting the linter.

**Every semantic lemma over the class meets the same obstacle.** A `comp`
node applies its head at `fun i : Fin m ↦ …` while the lemma reads
`![…]`; the two agree only by `funext`, and `congrArg f h` fails unless
`h`'s two sides are written out explicitly first.

## Loose ends

- `docs/references.bib` still has no key for `BarringtonCorbett1989`, nor
  for the three succinct-tree references. They are verified but uncited,
  and belong to the branch that first cites one, expected to be B5.
- The design document is carried to segment 3 and removed there. Until
  then a merged segment leaves it in `main`'s working tree, which
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape otherwise
  forbids; this is a recorded decision, not an oversight.
- `Cobham/Tree.lean`'s `oneAtOf`, `falseAtOf` and `predPred` duplicate
  `constAtOf` and `predIter 2`. The substitution is definitionally
  transparent — measured, not argued — so removing the duplication is a
  short branch whenever someone wants it.
