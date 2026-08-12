# B5, the time and space bound — workstream handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [Where the workstream stands](#where-the-workstream-stands)
- [Where the line stands](#where-the-line-stands)
- [B5: the time and space bound](#b5-the-time-and-space-bound)
- [What Cslib provides](#what-cslib-provides)
- [What Cslib does not provide](#what-cslib-does-not-provide)
- [A staged route](#a-staged-route)
- [Why this segment differs in kind](#why-this-segment-differs-in-kind)
- [The references B5 is expected to cite](#the-references-b5-is-expected-to-cite)
- [Facts established by building](#facts-established-by-building)
- [Process this session must follow](#process-this-session-must-follow)
- [Loose ends](#loose-ends)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document replaces the two handoffs dated 2026-08-10. It is the only
handoff the workstream now needs: B5 is the last segment, so when B5 lands
this document is removed with it, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Read these first

- [CONTRIBUTING.md](../../../CONTRIBUTING.md),
  [AGENTS.md](../../../AGENTS.md), [CLAUDE.md](../../../CLAUDE.md).
- [docs/rules/lean-coding.md](../../rules/lean-coding.md),
  [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md),
  [docs/rules/markdown-writing.md](../../rules/markdown-writing.md),
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md).
- [TODO.md](../../../TODO.md) § Extensions of the tree recognizers, which
  records B5 and every deferral the workstream has accumulated, and
  [docs/index.md](../../index.md) for what is implemented.

B5 has no specification. Its first phase is
`superpowers:brainstorming`, then a spec and a plan, each carried to
adversarial-review convergence, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review of specs and plans.
§ A staged route below is a sketch to brainstorm against, not a plan.

## Where the workstream stands

| Item | What it is | Status |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — ranked alphabets, the preorder encoding, the validity scan | Done, unpushed |
| B2 | `Cobham/Scan.lean` — the scan combinator, and `Cobham/Tree.lean` rebuilt on it | Done, unpushed |
| — | `Cobham/Cases.lean` — definition by cases, with the constant-word, iterated-predecessor and diagonal combinators in `Cobham/Basic.lean` | Done, unpushed |
| B6 | `Cobham/RankedTree.lean` — the generic ranked recognizer | Done, unpushed |
| B3 | `Cobham/Fold.lean` — the catamorphism at a carrier with a bit encoding | Done, unpushed |
| B4 | `BinTree` absorbed into `RankedAlphabet.Term`, the duplication removed | Done, unpushed |
| B5 | `Geb/Internal/` — linear time and space against Cslib's `MultiTapeTM` | Not started |

The workstream's own completion condition is already met: no tree encoding
is defined twice, and the recognizer is stated at an arbitrary ranked
alphabet. B5 is a separate undertaking whose failure costs nothing already
built.

Nothing in this workstream has been pushed.
[AGENTS.md](../../../AGENTS.md) § No `jj git push` without user
line-by-line review binds every segment, first creation included.

## Where the line stands

Six segments off `main` (`312c5adf`), each with a bookmark, so `jj` pushes
each as its own pull request while the commits stay in one chain.

```text
main                                    312c5adf
  └─ feat/ranked-tree-recognizers       2f50f879
       └─ feat/cobham-scanner           8cbff06f
            └─ feat/cobham-cases        5ea87784
                 └─ feat/cobham-ranked-tree  79aaea40
                      └─ feat/cobham-fold    c368339d
                           └─ refactor/tree-absorb-bintree  9b9c0cea
```

`main` has not moved since the line was cut, so no rebase is needed before
pushing. B5's segment sits on `refactor/tree-absorb-bintree`; its bookmark
is set after its own final commit, so that it does not omit the commit
removing this document.

## B5: the time and space bound

`Geb/Internal/`. Depends on B2, and on B4 only for the names it states the
language over.

The target is linear time and space for the tree recognizer against
Cslib's `MultiTapeTM`, sharper than the polynomial-time, linear-space
membership that `Cobham.isTree_smashFree` gives through [Strahm2003]
Theorem 1(2).

The language is fixed and already characterised three ways, which is what
makes the statement expressible at all:

- `RankedAlphabet.Binary.binRanked.validBool : List Bool → Bool` — the
  computable decision function, a projection-free `Bool`, which is the form
  the bound is stated over.
- `Cobham.isTreeSem_eq_singleton_iff_valid` — the expression of `C` accepts
  exactly the words `binRanked.Valid` accepts.
- `RankedAlphabet.Binary.valid_iff_ok_and_depth_eq_one` — validity is the
  counter form's two conditions, liveness and a pending count of one, at
  width one. This is the shape a machine mirrors: a right-to-left pass
  carrying one counter.

`Geb/Mathlib/` may not import `Cslib.*` and `Geb/Cslib/` may not import
`Geb.Mathlib.*`, so the statement is confined to `Geb/Internal/`, which may
import from both.

Record what measuring the algebra term itself gives, as the contrast:
`pred` and `cond` are `boundedRec` nodes rather than generators, so under a
strict reading each costs one unit per bit of its scrutinee, and the scan's
total is the sum of the stack depths — quadratic in the word length on a
left comb, linear on a right comb. The machine bound is the sharper claim
and does not follow from the algebra's cost.

## What Cslib provides

Re-verified 2026-08-12 against
`.lake/packages/cslib/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`
(531 lines) and its sibling `TapeLemmas.lean`. Every claim the superseded
handoff made about this API still holds; the additions below were not
previously recorded.

- `ComputableInTimeAndSpace {IOSymbol} (f : List IOSymbol → List IOSymbol)
  (t s : ℕ → ℕ) : Prop` — three explicit arguments, existentially
  quantifying `k`, the machine alphabet `Fin sym`, the state set
  `Fin state`, the embedding and the machine. It is the existential
  alphabet, not the embedding, that admits a work-tape symbol wide enough
  to hold a stack frame; the embedding is `IOSymbol ↪ Symbol`, of input and
  output only.
- `f` returns a `List IOSymbol`, not a `Bool`. A `Bool`-valued decision
  becomes a one-symbol output list.
- **`DecidableInTimeAndSpace` is not the route.** It is
  `ComputableInTimeAndSpace (indicator L)`, and `indicator` is declared
  `open Classical in noncomputable def`. State the bound over
  `binRanked.validBool` composed into list form instead.
- `ComputesFunInTimeAndSpace` is the intermediate the existential unfolds
  to: `∀ input, ∃ t' ≤ t input.length, ∃ s' ≤ s input.length,
  ComputesInTimeAndSpace tm (input.map toMachineSymbol)
  ((f input).map toMachineSymbol) t' s'`. The bounds are per input length,
  and the `≤` lives here.
- `ComputesInTimeAndSpace tm input output t s` is three conjuncts: the
  configuration at step `t` has `state = none` (halted), `outputString` at
  `t` is `output`, and `spaceUsed` at `t` **equals** `s`. The exactness of
  the space conjunct is why the `≤` has to come from the layer above.
- `Cfg k Symbol State input` is indexed by the input, so the configuration
  type depends on the input term. Statements quantify over `input` first.
- `initCfg` is `⟨some tm.q₀, 1, fun _ _ => none, fun _ => 0⟩`: the input
  head starts at position `1` of `Fin (n + 2)`, at the **left** end, with
  work tapes blank and their heads at `0`. The validity scan consumes a
  word **right to left**, so a machine mirroring it must first walk to the
  right end. That costs one extra pass and leaves a linear bound linear —
  worth stating in the spec rather than discovering in a proof.
- `spaceUsed cfg t = ∑ i, spaceUsedByTape cfg t i`, and
  `spaceUsedByTape cfg t i = (visitedByTapeHead cfg t i).card` where
  `visitedByTapeHead` is the image of `Finset.range (t+1)` under
  `workTapePos i`. Space is cells *visited*, not cells written.
- `TapeLemmas.lean` is the space-accounting toolkit, and nothing recorded
  it before: `spaceUsedByTape_le`, `spaceUsed_linear`, `spaceUsed_mono`,
  `spaceUsedByTape_mono`, `visitedByTapeHead_mono`,
  `mem_visitedByTapeHead`, `uIcc_workTapePos_subset_visitedByTapeHead`,
  `natAbs_le_spaceUsedByTape_of_mem_visited`,
  `content_natAbs_le_spaceUsedByTape`, `step_workTapes_eq_of_ne`. A space
  bound is expected to go through these rather than through
  `visitedByTapeHead`'s definition.
- `configs cfg t = tm.step^[t] cfg`, with `configs_zero` and
  `step_of_halt` (a halted configuration is a fixed point) as the base
  facts; `relatesInSteps_iff_configs_eq` bridges the relational and
  iterated-step views and the file recommends the latter for deterministic
  machines. `haltsAtStep` is `Bool`-valued.
- `spaceUsed_zero_tapes_eq_zero`: a zero-tape machine uses zero space —
  the smallest available foothold for a first construction.

## What Cslib does not provide

A grep for a concrete machine across the whole of `.lake/packages/cslib/`
returns only the `MultiTapeTM` structure declaration itself. **Cslib
contains no worked
example, no machine construction and no composition combinator.** B5 would
build the first concrete `MultiTapeTM` in
that ecosystem.

That is the single largest fact about this segment's difficulty, and it
cuts both ways. No idiom exists to follow, so the first construction
sets one and will be slow. Equally, nothing exists to conflict with, and a
first worked machine is plausibly of interest to Cslib upstream in its own
right — which is worth weighing during brainstorming, since it would
change the segment's destination from `Geb/Internal/` to a Cslib-targeted
subtree for that part.

`Cslib/Computability/Machines/Turing/SingleTape/` also exists
(`Defs.lean`, `Deterministic.lean`, `NonDeterministic.lean`) and is worth
reading for patterns even though the target is the multi-tape predicate.

## A staged route

A sketch to brainstorm against. Each stage is independently valuable, so a
session that runs out of room banks something rather than nothing. Nothing
here is verified beyond the API facts above; the arithmetic in stage C is
a claim to check, not a result.

- **A. The first machine.** Construct any concrete `MultiTapeTM` and prove
  `ComputesInTimeAndSpace` of it — a machine that halts at once, or copies
  its input. No algorithmic content; the point is to establish the idioms
  (`Cfg` indexed by input, `initCfg`, `configs`, `outputString`,
  `spaceUsed`) and to find out what proving anything about this API costs.
  `configs_zero`, `step_of_halt` and `spaceUsed_zero_tapes_eq_zero` are
  the footholds.
- **B. The scanning machine.** One work tape holding the pending count in
  unary; the input head walks to the right end, then right to left once,
  incrementing on a leaf bit and decrementing twice-then-incrementing on a
  node bit, failing on underflow. This mirrors
  `RankedAlphabet.scanStep` at `binRanked` exactly, which is why the
  counter form of B4 is the thing to state it against.
- **C. The bounds.** Time: two passes plus O(1) counter work per symbol.
  Space: the pending count never exceeds the word length
  (`RankedAlphabet.Binary.depth_le_length`), so the unary counter occupies
  at most `n` cells and `spaceUsed ≤ n`. Both are claims to verify — in
  particular whether the counter's head movement keeps the per-symbol work
  constant, since `spaceUsed` counts cells visited and a head that walks
  the counter each step would cost quadratic time.
- **D. Correctness.** Relate the machine's output to `binRanked.validBool`,
  which is where `valid_iff_ok_and_depth_eq_one` and the four
  `cons`-lemmas earn their keep: the machine's step and `scanStep` agree
  one bit at a time.

Stages A and B are the ones with unbounded difficulty. If A alone lands
with a spec, a plan and its reviews, that is a segment.

## Why this segment differs in kind

Every other segment in this workstream transcribed or restated
mathematics that was already settled, in an area the repository had
already built. B5 is exploratory: it proves a cost bound, in an ecosystem
with no precedent, against an API nobody here has used. Three
consequences for how to run it.

- **The prototype-first discipline matters more here, not less.** The
  workstream's own record (§ Facts established by building) is a list of
  facts that each cost a failed build, and the fold segment converged in
  three review rounds only because a prototype was compiled before the
  plan was written. With an unfamiliar API the ratio of unknown to known
  is higher, so compile a spike before specifying anything.
- **Scope down rather than out.** The bound is the goal, but a first
  machine with a proof of anything is progress and a spec that promises
  the whole bound and delivers nothing is not. Prefer a segment that
  lands stage A over one that stalls in stage C.
- **Failure is affordable and should be declared.** B1 to B4 and B6 stand
  without B5. If the API turns out to make the bound impractical, the
  honest outcome is a `Geb/Internal/` note recording what was tried and
  why it does not go through, plus a `TODO.md` entry — not an
  indefinitely open segment.

## The references B5 is expected to cite

`docs/references.bib` has no key for `BarringtonCorbett1989`, nor for the
three succinct-tree references `BenoitDemaineMunroRamanRamanRao2005`,
`Mehlhorn1980` and `BraunmuhlVerbeek1983`. They are verified as existing
but their attributed claims are not verified against the primary sources,
and they are uncited. B5 is the branch expected to cite the first of them.

Before recording any key, verify the attribution against the primary
source with `theoremsearch` (`theorem_search`) or `arxiv-mcp-server`
(`search_papers`, `read_paper`), per
[AGENTS.md](../../../AGENTS.md) § Verify agent claims and
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing. In particular the DLOGTIME-uniform TC⁰ claim attributed to
`BarringtonCorbett1989` has never been checked against the article.

## Facts established by building

Twenty-six facts, each of which cost a failed build or a measurement.
Items 1 to 11 date from B1, 12 to 16 from the ranked-recognizer segment,
17 to 23 from the fold, and 24 to 26 from the absorption. Three are marked
corrected: they were stated wrongly in an earlier handoff and cost a
second failed build. Do not reinstate a corrected claim from any older
document.

Several are specific to the Cobham material and will not bear on a Turing
machine. Items 5, 8, 9, 11, 13, 16 and 26 are the general ones — the
`Classical.choice` traps, the linters this repository makes errors, the
transparency at which `rw` closes a goal, the module-system rules for test
fixtures, the build-alone rule, and `omega`'s treatment of an unreduced
`Nat.zero`.

1. **`Term.mk R i ch`, never `R.Term.mk i ch`.** Generalized field notation
   resolves `R.Term` first, and a `Type` carries no `mk`.
2. **A symbol index must carry an assigned bound proof (corrected).**
   `R.arity i` reduces for a literal index, so `Fin (arity ⟨0, h⟩)` is `Fin 0`
   and `Fin (arity ⟨1, h⟩)` is `Fin 2` — but only once `h` is assigned. Written
   inline, `⟨0, by decide⟩` leaves `h` an unassigned metavariable while the
   child family elaborates, and the family's domain is then neither. Name the
   index, as `leafSym` and `nodeSym` do. Against an index that is itself a
   pattern variable the goal carries a free variable, which `decide` refuses,
   and presents the arity as an atom, which `omega` cannot unfold; ascribe the
   bound with `show (0 : ℕ) < 2`. The previous handoff's
   `by decide +revert` is not the working form in either situation.
3. **`Nat.land` is not exposed, so a block does not reduce during
   elaboration.** Prove a `code` equality by `decide`, which the kernel
   evaluates, not by `rfl`, and rewrite through the result downstream.
4. **`Nat.mod_mul` depends on `Classical.choice`**, and `omega` cannot
   discharge a residue identity whose modulus is a variable.
   `RankedAlphabet.mod_two_mul` and `RankedAlphabet.add_one_mod` replace the
   two that were needed. Expect the same trap in any further `Nat` division
   reasoning, and re-measure after each.
5. **`omega` proving a non-`False` goal can pull in `Classical.choice`.** It
   did not in B1, but `lake lint` is what settles it, not inspection.
6. **`decide` on a `Term` equality is available (corrected).** mathlib has no
   `DecidableEq (WType …)`; `Geb/Mathlib/Data/W/Basic.lean` supplies one for
   `[DecidableEq α] [∀ a, FinEnum (β a)]`. B1's mirrors state the descent's
   value through `Option.map` of the spelling anyway, which costs neither that
   import nor the `FinEnum` instances its `decide` would reduce through. The
   previous handoff's claim that no instance exists is wrong.
7. **Sweep budgets are per-computation, not per-word-count (corrected).**
   `set_option maxRecDepth 100000 in decide` is valid in tactic position. The
   word count is not what decides whether it is needed: at 127 words the
   `validBool`-against-`parse` sweep closes at the default depth while
   `length_wordsUpTo_six`, which builds the same enumeration, does not. Measure
   rather than predict. `native_decide` is banned (compiler-trust axiom).
8. **`linter.flexible`, `linter.unnecessarySeqFocus` and `linter.style.show`
   are errors here.** A bare `simp` that modifies the goal must be terminal;
   `tac1 <;> tac2` where `tac1` leaves one goal fails; and a `show` that
   changes the goal must be `change`.
9. **`simp only [] at h` after a `split` is an error** (`simp made no
   progress`) — the `split` already iota-reduces the hypothesis. `simp only []`
   on the goal is sometimes required, to reduce a `match some …`.
10. **Import placement.** `List.sum_map_mul_left` is in
    `Mathlib.Algebra.BigOperators.Ring.List`. `List.le_sum_of_mem` needs
    `Mathlib.Algebra.Order.BigOperators.Group.List` and routes through
    ordered-algebra instances the axiom rules warn about; `size_le_sum_ofFn`
    proves the bound directly instead.
11. **Test modules** need `set_option linter.privateModule false` or
    `@[expose] public section`. Fixtures shared across test modules need a
    `public import` of the declaring module and `@[expose]`. Group
    `public import`s before plain `import`s, separated by a blank line.
12. **A projection of a `Scan` constructor does not reduce syntactically.**
    After `obtain ⟨buf, depth, live⟩ := s`, or under `{ s with depth := … }`,
    the goal carries `{ buf := buf, … }.live` rather than `live`. A `cases`
    on a scrutinee written in the fields then matches nothing and silently
    splits nothing, and the following `rw` fails with a pattern that is
    visibly present in the printed goal. `dsimp only` reduces them, and is
    needed once after the definitions are unfolded and again after each
    `cases`.
13. **`rw` closes a goal by `rfl` at reducible transparency only.** A branch
    ending in an equation true by unfolding an `@[expose] def` needs an
    explicit `rfl` after the rewrite.
14. **`rw [List.length_cons]` inside a chain rewrites the first matching
    instantiation**, which under `scanStep`'s unfolding is the block's
    length rather than the word's. Supply the word's length as a `have` for
    `omega`.
15. **`List.takeWhile_replicate` depends on `Classical.choice`**, through
    `List.filter_replicate`, whose proof is a `simp_all` and so does not
    show it in the source. This is a fourth route beyond `omega`
    discharging an `Iff` goal, `DecidableEq (Fin n → Bool)` resolving
    through `Fintype.decidablePiFintype`, and `RankedAlphabet.Scan`
    deriving no `DecidableEq`; the two-case reduction that replaces it
    measures clean. `DecidableEq (Fin n → Bool)` was measured the same way
    and does depend on `Classical.choice`, while `DecidableEq (List Bool)`
    depends on nothing.
16. **Two concurrent `lake build` invocations corrupt package `.trace`
    files** and fail unrelated mathlib targets. The `lean-lsp` tools that
    run Lean count as a second process. Build alone.
17. **`constAtOf` takes the arity explicitly**, `constAtOf (n : ℕ)
    (u : List Bool) : COf n`; the calls are `constAtOf 0 …` for the base
    and `constAtOf 1 …` for a branch.
18. **`rw` does not unfold `foldStep`.** `stepWord_foldStep` opens with a
    `change` to the `diagOf (casesOf …)` form before `stepWord_diagOf`
    applies, and needs a second `change` to present the goal as `casesSem`
    before `casesSem_eq` applies.
19. **`scanSem_cons` is not a `rfl`**, so `foldSem ![b :: w]` is not
    definitionally the step applied to `foldSem ![w]` and a `change` does
    not reach it. `foldSem_cons` is stated and proved from `scanSem_cons`,
    its last step `cases b <;> rfl` discharging `scanStepWord`'s `if`.
20. **`Cobham.scanSem_eq_eval` instantiates directly at this base and
    step**, and `Cobham.scanOf` likewise, so `foldSem_eq_eval` and `foldOf`
    reuse them rather than restating them as `rfl` and `⟨fold …, rfl⟩`.
    Both forms compile and both measure `[propext, Quot.sound]`; the
    instantiating form is the one `Cobham/RankedTree.lean` uses.
    `scanSem_eq_eval` is itself a `rfl`, unlike `casesSem_eq_eval`, whose
    transport is opaque.
21. **`#eval` of a fold value fails** with "Could not find native
    implementation of external declaration `Cobham.constAt`" — the
    cross-module IR gap
    [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Lean 4
    module system records. The mirror asserts by `decide`, which the
    kernel evaluates and which needs no `public meta import`.
22. **The sweep budget is seven.** At 255 words the sweep closes in about
    twelve seconds under `set_option maxRecDepth 100000 in decide`; at 511
    words it reaches the 200000-heartbeat `isDefEq` limit and fails. At
    127 words it closes in about six seconds.
23. **`linter.hashCommand` logs at info, not error**, so `#print axioms`
    is available inside a `Geb/` module for measuring a prototype. It
    remains barred from committed library code by review, not by the
    linter.
24. **`decide (([b] : List Bool).length = binRanked.width)` does not
    iota-reduce inside `scanStep`'s `match`**, though `binRanked.width`
    itself reduces to `1`. The equality is proved separately, by cases on
    `b`, and rewritten in.
25. **`depth` unfolds under `simp only [depth]` at a hypothesis and the
    goal together**, rather than needing a separate `simp only [depth] at
    h` and `simp only [depth]` on the goal.
26. **`omega` treats an unreduced `Nat.zero` as an atom.** A `Nat.rec`
    base case's bound is named at a literal first, before `omega` is
    called on it.

## Process this session must follow

- Invoke the phase skill before acting: `superpowers:brainstorming` before any
  spec, `superpowers:writing-plans` for a plan,
  `superpowers:executing-plans` or `superpowers:subagent-driven-development` to
  execute one, `superpowers:verification-before-completion` before claiming
  anything passes.
- Adversarial review of every spec and plan to convergence — no blocker and no
  serious finding — each round a fresh general-purpose `Agent`, never a
  continued one, re-fetching the mathlib guides each round. Respond in writing
  to every finding: fix, defer with rationale, or reject as cosmetic-taste.
- Verify agent claims, and claims inherited from a handoff, against the source
  before acting on them. Three of this document's own facts are corrections of
  a previous handoff that were confidently stated and wrong.
- Prefer building over arguing. In B1 the two rounds spent reviewing a document
  that described Lean did not converge; the round run against compiled code
  converged with no blocker.
- `jj` for every state-mutating VCS operation; never a mutating `git`
  subcommand. Local commits are fine; no push without the user's line-by-line
  review.
- Do not draft PR descriptions, Zulip messages or GitHub comments.
- This document is transient. Remove it in the final commits of whichever
  branch last needs it, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Loose ends

- `docs/references.bib` still has no key for `BarringtonCorbett1989` or
  the three succinct-tree references; see § The references B5 is expected
  to cite.
- `Cobham/Tree.lean`'s `oneAtOf`, `falseAtOf` and `predPred` duplicate
  `constAtOf` and `predIter 2`. The substitution is definitionally
  transparent — measured, not argued — so removing the duplication is a
  short branch whenever someone wants it. `TODO.md` carries it.
- Whether `Cobham/Tree.lean`'s recognizer is redundant beside
  `Cobham/RankedTree.lean`'s, now that both decide `binRanked.Valid`.
  `isTree_smashFree` and its [Strahm2003] corollary are the residue that
  is not. `TODO.md` carries it, and B5 has a stake in the answer: the
  smash-free membership is the weaker bound B5 aims to sharpen.
- `scripts/pre-push.sh` emits a non-blocking WARN that commit `5cfd5ef1`,
  of the case-combinator segment, carries a 73-character subject, one over
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Commit-message convention's "under 72 when possible." That commit is
  not part of any remaining branch, so it is left alone; the WARN is open
  and non-blocking.
