# B5 execution — session handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [What this session does](#what-this-session-does)
- [Where the workstream stands](#where-the-workstream-stands)
- [The state of the working tree](#the-state-of-the-working-tree)
- [What is verified and what is not](#what-is-verified-and-what-is-not)
- [Decisions already taken](#decisions-already-taken)
- [Task 2 governs the rest](#task-2-governs-the-rest)
- [Process this session must follow](#process-this-session-must-follow)
- [Loose ends](#loose-ends)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document orients a fresh session executing B5. It does not restate
the plan; it records what a reader of the plan alone would not know. It is
transient and is removed with the spec and the plan in the branch's final
commit, per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Read these first

- [CONTRIBUTING.md](../../../CONTRIBUTING.md),
  [AGENTS.md](../../../AGENTS.md), [CLAUDE.md](../../../CLAUDE.md).
- [docs/rules/lean-coding.md](../../rules/lean-coding.md),
  [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md),
  [docs/rules/markdown-writing.md](../../rules/markdown-writing.md),
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md).
- The spec,
  [docs/superpowers/specs/2026-08-12-b5-time-space-bound-
  design.md](../specs/2026-08-12-b5-time-space-bound-design.md),
  and the plan,
  [docs/superpowers/plans/2026-08-13-b5-time-space-bound-
  plan.md](2026-08-13-b5-time-space-bound-plan.md).
  Both are needed: the plan argues from the spec throughout.

## What this session does

Execute the plan with `superpowers:subagent-driven-development`: a fresh
subagent per task, review between tasks. The plan's sixteen tasks are
sized for that.

The plan's own header names the skill. Nothing about the plan requires
inline execution, and the tasks are independent enough that a fresh
context per task is the cheaper mode.

## Where the workstream stands

| Item | What it is | Status |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — ranked alphabets, the preorder encoding, the validity scan | Merged, PR #144 |
| B2 | `Cobham/Scan.lean` and `Cobham/Tree.lean` rebuilt on it | Merged, PR #145 |
| — | `Cobham/Cases.lean`, with the combinators in `Cobham/Basic.lean` | Merged, PR #146 |
| B6 | `Cobham/RankedTree.lean` — the generic ranked recognizer | Merged, PR #148 |
| B3 | `Cobham/Fold.lean` — the catamorphism at a carrier with a bit encoding | Merged, PR #149 |
| B4 | `BinTree` absorbed into `RankedAlphabet.Term` | Merged, PR #150 |
| B5 | The machine and its bound | Specified and planned; not started |

B5 is the last segment, and it is the only one not yet merged. Everything
it depends on is already in `main`: `RankedAlphabet.Binary`, the scan and
its lemmas, and the recognizers. So B5 branches from `main` directly —
there is no stack of open segment branches to rebase onto or to keep in
order, which earlier handoffs in this workstream had to manage.

`main` also carries the toolchain bump to `v4.34.0-rc1` (PR #152), which
is the pin every measurement in the spec was taken at.

## The state of the working tree

Five paths are uncommitted and B5 has no topic branch yet; the working
copy sits directly on `main`. Task 0 of the plan creates the branch and
commits all five, the spec, the plan and this handoff first.

`jj bookmark list` showing only `main` is not evidence that no branch has
existed — the six merged segments' bookmarks were consumed when their
pull requests landed. It means B5's branch has not been created.

Two facts about the tooling that the plan depends on and that invite a
wrong assumption:

- **`jj commit` takes path arguments.** `jj commit [FILESETS]... -m …`
  keeps the selected changes in the current commit and moves the rest to
  a new working-copy commit on top. Without a path argument it commits
  the whole working copy. Task 0 Step 3 relies on this.
- **`scripts/check-commit-msg.sh` reads subjects from stdin.** Run bare
  it reads EOF, checks nothing, and reports success. Invoke it as
  `scripts/pre-push.sh` does, piping `jj log` output into it; Task 0 Step
  5 gives the invocation.

## What is verified and what is not

The plan's Lean was checked by independent reviewers who elaborated it at
the pinned toolchain, not by reading. Treat that division as the map of
where to expect trouble.

**Elaborated and confirmed to close.** Every definition the plan gives in
full; every theorem statement in Tasks 4 to 13; all ten
transition-resolution lemmas of Task 6, each with a minimal and
sufficient hypothesis set; the four input-symbol projections;
`step_of_state` and both step lemmas built on it;
`sweepCfg_workTapeSymbols_eq`; `validBool_eq_ok_and_depth`;
`sweepCfg_workTapeSymbols`; `seekCfg_zero`; Task 12's whole route; and
Task 13's `decide`, which closes in-module with the six sample values and
no `maxRecDepth` bump. `Machine.lean`'s content measures choice-free
throughout, so Task 3 Step 8's contingency is not expected to fire.

**Task 2's spike is also elaborated.** Its definitions, `spikeCfg_step`
and `spikeCfg_workSymbol` were proved as written, and `spikeCfg_configs`
was proved after its bound was corrected from `j ≤ n` to `j < n` — the
spike's own boundary, where the work head sits on the second marker and
the arm that moves it is not selected. The real `sweepCfg` has no marker
at the count's own cell and does not share it. `#lint only
unusedArguments` reports no flags across the module.

Three earlier versions of this spike were refuted by elaboration, each
for a different reason, so treat its statements as the part of the plan
most likely to still need adjustment while running — but they are no
longer unmeasured.

**Already measured, so Task 2 confirms rather than discovers.** A
leftward work-head move at a cast position does close, and
`Int.natCast_sub` is not needed — `omega` handles `↑(d - 1)` at `ℕ → ℤ`
natively. What blocks is the `SignType`-to-`ℤ` coercion on the
transition's `-1`, which `omega` treats as an atom; the plan states
`signNegOne` for it, and having that lemma in context is enough, since
`omega` consumes it as a linear hypothesis. The `ite` chain on state
equality closes by `rfl`
and by nothing else — never by `simp only` or `dsimp only` — so the
plan's alternative encodings are a contingency that is not expected to be
needed.

## Decisions already taken

Do not reopen these without cause; each was argued in the spec and
several were argued across more than one review round.

- **The criterion correction rides in this branch.** Task 14 Step 3 gives
  the three replacement sentences verbatim. The criterion is what an
  allowlisted module is *for*: its subject is the correspondence between
  a concept developed here and a concept of an external Lean library —
  Batteries, mathlib, Cslib — that itself uses `Classical.choice`.
- **Two work-tape markers, not one.** This is what makes the sweep one
  step per symbol, removes the restore mechanism, and folds the emitting
  step into the live and dead states. The spec's § Why the work tape
  carries two markers records why.
- **Three named configurations, not two.** The plant step's configuration
  must be named, because `configs_add`'s inner term is exactly it.
- **Stage 3 is the minimum merge point**, which is the plan's Task 11.
  Work stopping earlier is committed locally but not merged.
- **The upstream Cslib patch is not part of this branch.** It is recorded
  in `TODO.md` as its own item.

## Task 2 governs the rest

Task 2 is a measurement spike whose outcome the rest of the plan is
conditioned on. If a measurement falsifies a spec assumption, record the
measurement, correct
[the spec](../specs/2026-08-12-b5-time-space-bound-design.md) in the same
commit, and only then continue. The spec's § Staged reduction of scope
requires this so that the reviewed artifact and the executed one do not
diverge.

A spec correction made this way does not re-enter the adversarial-review
loop of [AGENTS.md](../../../AGENTS.md) § Adversarial review: that loop
governs the artifact before execution begins. Record the correction and
the measurement that forced it, and let the user see both.

## Process this session must follow

- Invoke the phase skill before acting.
  `superpowers:subagent-driven-development` to execute;
  `superpowers:verification-before-completion` before claiming anything
  passes; `superpowers:systematic-debugging` before proposing a fix for
  an unexpected failure.
- **Build alone.** Two concurrent `lake build` invocations corrupt
  package `.trace` files and fail unrelated mathlib targets. The
  `lean-lsp` tools that run Lean count as a second process.
- **`jj` for every state-mutating VCS operation**, never a mutating `git`
  subcommand. Local commits are fine; no push without the user's
  line-by-line review, per [AGENTS.md](../../../AGENTS.md) § No
  `jj git push` without user line-by-line review — first creation
  included.
- **Verify agent claims** against the source before acting on them,
  including claims made by this document. Several statements in this
  branch's own spec were confidently wrong and were caught only by
  elaboration or by opening the cited file.
- **Quote a rule in full** when a decision rests on what it permits. Four
  separate truncations of one rule during this branch's review each
  changed the conclusion.
- Do not draft PR descriptions, Zulip messages or GitHub comments.
- This document is transient. The plan's Task 15 removes it with the spec
  and the plan.

## Loose ends

- `docs/references.bib` gains no key from this branch. The unverified
  references `BarringtonCorbett1989`,
  `BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980` and
  `BraunmuhlVerbeek1983` stay unverified and unrecorded; Task 14 Step 2
  preserves the record that they are.
- `Geb/Internal/TMSpike.lean` is committed for the record by Task 0 and
  removed by Task 15. It needs five corrections first, which Task 0 Step
  2 lists.
- Earlier handoffs in this workstream carried a `scripts/pre-push.sh` WARN
  about commit `5cfd5ef1`'s 73-character subject. It does not apply here:
  that commit is not an ancestor of `main`, having been rewritten when
  the case-combinator segment merged, so it cannot appear in the
  `fork_point(main | @)..@` range pre-push checks for a branch cut from
  `main`.
