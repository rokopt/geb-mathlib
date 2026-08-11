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
- [TODO.md](../../../TODO.md) § Extensions of the tree recognizers, and
  [docs/index.md](../../index.md) for what is implemented.

B4 has no specification. Its first phase is
`superpowers:brainstorming`, not planning: a spec, then a plan, each
carried to adversarial review convergence, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review of specs and plans.

## Which document owns what

Two handoffs sit in this tree, and they are not interchangeable. Keep an
edit in the one that owns the subject.

- [The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) owns
  the description of each remaining branch, the constraints each carries,
  the deferrals, and the accumulated Lean facts. It outlives this session.
- This document owns the state of the line, what the last session
  delivered, and what to pick up next. Replace it when that state changes.

## Status of every roadmap item

The case combinator carries no letter: it is shared machinery both B6 and
B3 needed, introduced because a dispatch over `2 ^ width` block values
cannot be written out at a symbolic width.

| Item | What it is | Status |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — ranked alphabets, the preorder encoding, the validity scan, `BinTree` as the two-symbol instance | Done, unpushed |
| B2 | `Cobham/Scan.lean` — the scan combinator, and `Cobham/Tree.lean` rebuilt on it | Done, unpushed |
| — | `Cobham/Cases.lean` — definition by cases, with the constant-word, iterated-predecessor and diagonal combinators in `Cobham/Basic.lean` | Done, unpushed |
| B6 | `Cobham/RankedTree.lean` — the generic ranked recognizer | Done, unpushed |
| B3 | `Cobham/Fold.lean` — the catamorphism at a carrier with a bit encoding | Done, unpushed |
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
main                                   312c5adf
  └─ feat/ranked-tree-recognizers      2f50f879
       └─ feat/cobham-scanner          8cbff06f
            └─ feat/cobham-cases       5ea87784
                 └─ feat/cobham-ranked-tree  79aaea40
                      └─ feat/cobham-fold
```

`main` is the line's base and has not moved since the line was cut: it is
`312c5adf`, and `main..@` contains only this line's own commits. No rebase
is needed before pushing.

`feat/cobham-fold` is this segment's bookmark; it is set after this
session's final commit, not before, so that it does not omit the commit
removing this segment's own transient documents.

## What this session delivered

The catamorphism at a carrier with a bit encoding, closing B3, in the
commits from `822a80e3` to `d2a618e1`.

- `Cobham/Fold.lean` — the step as a dispatch on the encoded state
  (`foldStep`, `stepWord_foldStep`); the fold's meaning as the scan at the
  encoded base and the two steps (`foldSem`, `foldSem_nil`, `foldSem_cons`);
  the length invariant and the expression (`length_foldSem`,
  `length_foldSem_le`, `fold`, `foldOf`, `foldSem_eq_eval`); and the
  carrier-level fold (`foldSem_eq`), which identifies the value with
  `List.ofFn` of the encoding of `w.foldr step init` under the retraction
  hypothesis `∀ a, dec (enc a) = a`. The carrier is arbitrary; neither
  `Fintype` nor `FinEnum` appears.
- `GebTests/Mathlib/Computability/Cobham/Fold.lean` mirrors the module, at
  a three-element carrier whose decoding is not injective off the image of
  its encoding, so the retraction hypothesis is exercised rather than
  trivially satisfied; `counterShift` and `counterShift_values` add a
  second step whose branches do not commute, exhibiting the fold's
  consumption order by giving a word and its reverse different values.
- `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` gained
  `length_wordsUpTo_seven`, the length the mirror's sweep uses.
- `docs/index.md` and `TODO.md` record it.

A prototype at `Geb/Internal/FoldSpike.lean` and
`Geb/Internal/FoldSpikeMirror.lean`, compiled at a symbolic carrier and
encoding width during planning, was transcribed into the modules above and
then deleted; its declarations' axioms were measured there and fell within
`{propext, Quot.sound}`.

## What to pick up next

**B4: absorbing `BinTree` into `RankedAlphabet.Term`.** B4 has no
specification, unlike B3 and B6 before it: the next session's first phase
is `superpowers:brainstorming`, followed by its own spec, plan and
adversarial review to convergence, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review of specs and plans.
It depends on B1 and B2, both in place.

[The workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md) § B4
records what is absorbed — `termEquiv`, `spell_termEquiv` and `valid_iff`
are the bridge B1 delivers, and `binRanked.parse w = (BinTree.parse
w).map termEquiv` is the shape every further bridge takes — which modules
name `BinTree`, and the staging decision that leaves the duplication in
`Geb/Mathlib/Data/Tree/Preorder.lean` on `main` until B4 lands.

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
review of the case-combinator segment came back clean; the whole-segment
review then found two docstrings asserting the opposite of what their
proofs did, and a pair of tests that opened with a rewrite which replaced
the construction under test before anything computed. Budget for a final
review that reads the segment as one body of work.

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

**`rw` does not unfold a `def`.** `stepWord_foldStep` needed a `change` to
the unfolded form before `stepWord_diagOf` applied, and a second `change`
to present the goal as `casesSem` before `casesSem_eq` applied; `rw` is
syntactic and does not search up to delta-reduction.

## Loose ends

- `docs/references.bib` still has no key for `BarringtonCorbett1989`, nor
  for the three succinct-tree references. They are verified but uncited,
  and belong to the branch that first cites one, expected to be B5.
- `Cobham/Tree.lean`'s `oneAtOf`, `falseAtOf` and `predPred` duplicate
  `constAtOf` and `predIter 2`. The substitution is definitionally
  transparent — measured, not argued — so removing the duplication is a
  short branch whenever someone wants it.
