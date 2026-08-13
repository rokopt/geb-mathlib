# B5, the time and space bound — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [What this plan can and cannot state](#what-this-plan-can-and-cannot-state)
- [Where the branch may be merged](#where-the-branch-may-be-merged)
- [File structure](#file-structure)
- [What is already in the working tree](#what-is-already-in-the-working-tree)
  - [Task 0: Committing what is already there](#task-0-committing-what-is-already-there)
  - [Task 1: Reading the precedent](#task-1-reading-the-precedent)
  - [Task 2: The measurement spike](#task-2-the-measurement-spike)
  - [Task 3: The machine](#task-3-the-machine)
  - [Task 4: The configurations](#task-4-the-configurations)
  - [Task 5: The decision-function bridge](#task-5-the-decision-function-bridge)
  - [Task 6: The transition-resolution lemmas](#task-6-the-transition-resolution-lemmas)
  - [Task 7: The seek phase](#task-7-the-seek-phase)
  - [Task 8: The plant boundary](#task-8-the-plant-boundary)
  - [Task 9: The sweep step lemma](#task-9-the-sweep-step-lemma)
  - [Task 10: The sweep configuration theorem](#task-10-the-sweep-configuration-theorem)
  - [Task 11: The emitting step](#task-11-the-emitting-step)
  - [Task 12: The bound](#task-12-the-bound)
  - [Task 13: The test mirror](#task-13-the-test-mirror)
  - [Task 14: Documentation and TODO](#task-14-documentation-and-todo)
  - [Task 15: Removing the transient artifacts](#task-15-removing-the-transient-artifacts)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** A concrete deterministic multi-tape Turing machine deciding
`RankedAlphabet.Binary.binRanked.validBool`, with proofs that it runs in
`2 * n + 3` steps and `2 * n + 4` space.

**Architecture:** The pending count is the work head's position, with two
distinct markers at cells `0` and `1` so that one read separates count
`0`, `1` and `≥ 2`. Four states — seek, plant, live, dead — and three
named configurations, joined by boundary step lemmas and composed with
`configs_add`. Every proof runs by an explicit `Nat.rec` on a step or
drop index against a closed-form configuration, never by induction on the
input, since `Cfg` is indexed by it.

**Tech Stack:** Lean 4 at the pin in `lean-toolchain`; Cslib's
`Turing.MultiTapeTM`; `Geb/Mathlib/Data/Tree/Ranked/`.

**Spec:**
[docs/superpowers/specs/2026-08-12-b5-time-space-bound-
design.md](../specs/2026-08-12-b5-time-space-bound-design.md).
Read it alongside this plan; every task argues from it.

## Global constraints

Copied from the spec and from the binding rule files. Every task's
requirements implicitly include this section.

- **Destination is `Geb/Internal/`.** `Geb/Mathlib/` may not import
  `Cslib.*` and `Geb/Cslib/` may not import `Geb.Mathlib.*`; this content
  needs both.
- **No `noncomputable`, minimise `Classical`.** `Machine.lean` must
  measure within `{propext, Quot.sound}`; `Steps.lean` and `Bound.lean`
  are admitted to `GebMeta.classicalAllowedModules` and the mirror with
  them.
- **No `induction` tactic.** Every recursion is an explicit `Nat.rec` or
  `List.rec` application, per `docs/rules/lean-coding.md` § Recursion and
  induction through recursors.
- **No `sorry` and no `_` in any commit.** `_` in proof position is an
  elaboration error and so fails `lake build`; it is the placeholder this
  plan writes for a proof whose route is given but whose script Task 2
  has not yet measured, and every task's build step is what removes it.
- **Module docstring mandatory**, with `# Title`, a summary,
  `## Main definitions`, `## Main statements`, `## Implementation notes`
  where non-vacuous, and `## Tags`. Declaration docstrings mandatory for
  every `def`, `structure`, `instance`, every structure field, and every
  theorem of public interest.
- **No `#print axioms`, `#eval`, `#check` or `#guard` in library code.**
  `lake lint` is what enforces the axiom measurements. The spikes are
  exempt; they are prototypes committed for the record.
- **Line length: 100 characters in `.lean`, 80 in `.md`.** 2-space
  indent; Unicode notation.
- **`weak.warningAsError = true`.** An imprecise `simp` set is an error:
  `linter.unusedSimpArgs` and `linter.unnecessarySimpa` both fail the
  build. `if_pos`, `if_neg`, `dif_pos`, `dif_neg` and `List.take_succ`
  are deprecated at this pin and are therefore errors; `split_ifs` names
  no lemma and is unaffected.
- **Build alone.** Two concurrent `lake build` invocations corrupt
  package `.trace` files; the `lean-lsp` tools that run Lean count as a
  second process.
- **Commit messages** follow `docs/rules/ci-and-workflow.md`
  § Commit-message convention: `type(scope): imperative subject`, no
  capital, no trailing period, under 72 characters.
- **`jj` for every state-mutating VCS operation.** Never a mutating `git`
  subcommand. No push without the user's line-by-line review.

## What this plan can and cannot state

The spec fixes the machine, the configurations and every statement. It
deliberately does **not** fix the tactic scripts, because Task 2 exists
to measure ten assumptions the proofs depend on — whether a `Fin`-literal
match reduces under `simp only`, whether a step lemma resolves
`Cfg.workTapeSymbols` at an opaque head position, whether a leftward move
at a cast position closes, and so on.

This plan therefore gives, literally:

- every definition, in full;
- every theorem statement, in full, with binders and hypotheses;
- for each proof, the route: which lemmas discharge which goal, in what
  order, and what the known hazards are.

It does not give tactic scripts for proofs whose tactics Task 2 has not
yet measured. Writing them would be invention, not planning. Where a
proof is expected to close by a specific short script, the script is
given and marked as expected rather than verified.

The boundary is proofs. Theorem *statements*, definitions and
documentation text do not depend on an unmeasured tactic, so this plan
gives every one of them in full rather than by reference to a pattern.

## Where the branch may be merged

The spec's § Staged reduction of scope makes its stage 3 the minimum
merge point, which is **Task 11** here: at that point the machine exists
and is proved to decide `binRanked.validBool`, which is a theorem worth a
`docs/index.md` entry. Tasks 12 to 15 complete the segment and are short
given Task 11, so the expected outcome is that all of them complete
together; the merge point exists for the case where they do not. Work
stopping at Task 10 or earlier describes a machine without relating it to
`validBool` and is committed locally but not merged, since
`CONTRIBUTING.md` § Code is cost does not admit a machine that decides
nothing. If Task 11 is not reached, the artifact is a record under
`docs/` of what was built and what did not succeed, with a `TODO.md`
entry.

**If Task 2 falsifies a spec assumption, stop.** Record the measurement,
correct the spec, and only then continue. The spec's § Staged reduction
of scope requires this so that the reviewed artifact and the executed one
do not diverge.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Internal/TreeScannerSpike.lean` | Task 2's measurements. A prototype; removed in Task 15. |
| `Geb/Internal/TreeScannerSpikeMirror.lean` | Task 2's cross-module `decide` measurement. A prototype. |
| `Geb/Internal/Computability/TreeScanner/Machine.lean` | The machine, `boolEmb`, the four states, the three configurations, their field projections, the decision-function bridge. Choice-free; not allowlisted. |
| `Geb/Internal/Computability/TreeScanner/Steps.lean` | `Cfg.inputSymbol` projections, transition-resolution lemmas, step lemmas, phase configuration theorems, halting and output conjuncts. Allowlisted. |
| `Geb/Internal/Computability/TreeScanner/Bound.lean` | Time and space bounds; `computableInTimeAndSpace_validBool`. Allowlisted. |
| `Geb/Internal/Computability/TreeScanner.lean` | Directory index. |
| `Geb/Internal/Computability.lean` | Directory index. |
| `Geb/Internal.lean` | Gains `public import Geb.Internal.Computability`. |
| `GebTests/Internal/Computability/TreeScanner/Machine.lean` | Mirror; asserts machine output against `validBool` by `decide` through a named `def`. Allowlisted. |
| `GebTests/Internal/Computability/TreeScanner.lean`, `GebTests/Internal/Computability.lean`, `GebTests/Internal.lean` | Mirror indexes and import. |
| `GebMeta.lean` | Three allowlist entries; declaration docstring corrected. |
| `docs/rules/lean-coding.md`, `docs/process.md` | The criterion correction. |
| `docs/index.md`, `TODO.md` | Documentation and workstream bookkeeping. |

## What is already in the working tree

Five paths are uncommitted when this plan begins:
`Geb/Internal/TMSpike.lean`, this plan, the spec, the execution handoff
`docs/superpowers/plans/2026-08-13-b5-execution-handoff.md`, and appended
terms in `styles/config/vocabularies/GebMathlib/accept.txt`. The B5
workstream handoff is not among them; it is already in `main`. Task 0
commits these four in the
order [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape fixes,
spec and plan first.

`jj commit` takes path arguments: `jj commit [FILESETS]... -m …` keeps
the selected changes in the current commit and moves the rest to a new
working-copy commit on top. No `jj split` is needed.

B5 has no topic branch yet, and the working copy sits directly on `main`.
Task 0 creates it, since
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Working develops on a topic
branch and § Project status makes `main` append-only. That
`jj bookmark list` shows only `main` reflects the workstream's six
earlier segments having been merged and their bookmarks consumed, not an
absence of branching; `main` already contains everything B5 depends on,
so no rebase is needed before Task 0.

---

### Task 0: Committing what is already there

**Files:**

- Modify: `Geb/Internal/TMSpike.lean`
- Commit: this plan, the spec, the execution handoff, `TMSpike.lean`,
  `styles/config/vocabularies/GebMathlib/accept.txt`

**Interfaces:**

- Consumes: nothing.
- Produces: a named topic branch, a committed spec and plan, and a
  committed prototype. No declaration.

- [ ] **Step 1: Create the topic branch**

```bash
jj bookmark create feat/tree-scanner-bound
```

Every later commit advances it. `AGENTS.md` § No `jj git push` without
user line-by-line review needs this name; without it there is nothing to
push and nothing to review.

- [ ] **Step 2: Bring `TMSpike.lean` to the standard the spec requires**

The spec's § Artifacts states what a prototype committed for the record
must satisfy. As the file stands, five things are outstanding:

1. its module docstring is four lines, with no `## Main definitions`,
   `## Main statements` or `## Tags`;
2. it opens `namespace TMSpike`, a bare root namespace; B6's spike used
   `namespace RankedAlphabet` and B3's `namespace Cobham`, the namespace
   of the mathematical subject, so use `namespace Turing`;
3. its five projection lemmas — `copyCfg_state`, `copyCfg_inputPos_val`,
   `copyCfg_workTapePos`, `copyCfg_workTapes`, `copyCfg_inputSymbol` —
   carry no docstrings;
4. it has one anonymous `example`, at the `decide` measurement;
5. its docstring, its `## Spike 2` section heading and two comments carry
   process narration and the barred words "throwaway" and "gap".

Its `set_option linter.unusedSimpArgs false` and its `#print axioms`
commands stay: the spec states that they are what make it a prototype,
and the `#`-commands have precedent in B3's spike.

Note for every later task that cites this file: after this step its
declarations are `Turing.copyIn_step`, `Turing.id_computable` and so on,
not `TMSpike.*`.

- [ ] **Step 3: Commit the spec, the plan and the execution handoff**

```bash
jj commit docs/superpowers -m "doc(scanner): specify and plan the tree scanner's bound"
```

The path argument is what keeps this to § Concern shape's phase-1
content; without it `jj commit` takes the whole working copy.

- [ ] **Step 4: Commit the prototype and the vocabulary**

```bash
jj commit -m "chore(scanner): record the multi-tape machine prototype"
```

No path argument is needed: the working copy now holds only these two.

- [ ] **Step 5: Verify**

Run: `lake build`; `markdownlint-cli2 'docs/superpowers/**/*.md'`;
`doctoc --dryrun --update-only docs/superpowers`;
`scripts/check-md-links.sh`; and the commit-message check as pre-push
invokes it, since the script reads subjects from stdin and run bare it
checks nothing and reports success:

```bash
jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
  -T 'description.first_line() ++ "\n"' | scripts/check-commit-msg.sh
```

Expected: all PASS. `lake lint` is not expected to see `TMSpike.lean`,
which is not imported from `Geb/Internal.lean` and must not be — it is
not allowlisted and its theorems mention `spaceUsed`.

---

### Task 1: Reading the precedent

**Files:** none modified.

**Interfaces:**

- Consumes: nothing.
- Produces: notes carried into Tasks 6 to 10; no declaration.

The spec's § Size names this as a task of the plan, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost's instruction
to reuse existing abstractions.

- [ ] **Step 1: Read mathlib's two concrete machine constructions**

`Mathlib/Computability/TuringMachine/ToPartrec.lean` and
`Mathlib/Computability/TuringMachine/StackTuringMachine.lean` are the
only concrete-machine-with-step-lemma precedent available, at a different
API but for the same proof shape. Read them for idiom: how a step lemma
is stated against a machine, how a configuration invariant is carried,
and how a simulation is composed.

- [ ] **Step 2: Record what transfers**

Write the findings into `docs/superpowers/plans/` as a short note
alongside this plan, committed with Task 2's spike so that Tasks 7 to 11
can read them: each task runs in a fresh context, so notes held only in
this task's context are gone by the time they are wanted.

---

### Task 2: The measurement spike

**Files:**

- Create: `Geb/Internal/TreeScannerSpike.lean`
- Create: `Geb/Internal/TreeScannerSpikeMirror.lean`

**Interfaces:**

- Consumes: nothing.
- Produces: ten measurements, recorded in the task's commit message and
  in the spec if any falsifies it. No declaration any later task uses.

This task's outcome governs the rest. Its purpose is to find out what the
proofs cost
before any of them is written, per the handoff's instruction to compile a
spike before specifying anything, and the spec's § Risks.

- [ ] **Step 1: Create the spike module with a two-state machine**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A two-state scanner spike

A two-state machine over one work tape carrying two markers, with a head
position that is an opaque function of the step. It measures what the
tree scanner's proofs will cost before they are written.

## Main definitions

- `spikeTM` — the two-state machine.
- `spikeCfg` — the closed-form configuration at an opaque count.

## Main statements

- `spikeCfg_workSymbol` — the work symbol at an opaque count.
- `spikeCfg_step` — one step against the closed form.
- `spikeCfg_configs` — a two-index recursion with a bundled motive.

## Tags

Turing machine, spike
-/

@[expose] public section

namespace Geb

open Turing MultiTapeTM

/-- The first of two states. -/
def spikeA : Fin 2 := ⟨0, by omega⟩

/-- The second of two states. -/
def spikeB : Fin 2 := ⟨1, by omega⟩

/-- A two-state machine written in the shape `treeScanner` will use: an
`ite` chain on state equality against named definitions, wrapping a
`match` on `Option (Fin 2)` with one numeral pattern and one wildcard,
with one branch binding neither argument. -/
def spikeTM : MultiTapeTM 1 (Fin 2) (Fin 2) where
  q₀ := spikeA
  tr q inSym work :=
    if q = spikeA then
      { inputMove := 1, workActions := fun _ ↦ (some (some 0), 1),
        outS := none, q' := some spikeB }
    else
      match inSym with
      | some 0 => { inputMove := -1, workActions := fun _ ↦ (none, 1),
                    outS := none, q' := some spikeB }
      | some _ =>
        match work 0 with
        | none => { inputMove := -1, workActions := fun _ ↦ (none, -1),
                    outS := none, q' := some spikeB }
        | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                      outS := none, q' := some spikeB }
      | none => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                  outS := some 1, q' := none }

end Geb
```

- [ ] **Step 2: Build and record which transition encoding reduces**

Run: `lake build Geb.Internal.TreeScannerSpike`

**Measurement 1.** How the `ite` chain on state equality reduces. The
rule to confirm is narrow: close it with `rfl`, never with `simp only` or
`dsimp only`. Unfolded, the chain presents as
`if ⟨3, stDead._proof_2⟩ = ⟨0, stSeek._proof_2⟩ then …`, which no simp
set resolves — but `rfl` closes it directly, and a resolution lemma that
never unfolds the chain never produces that goal. Confirm that a
resolution lemma of the form `rw [inputSymbol projection]; rfl` closes,
in both the true and the false direction of the chain.

**Measurement 2.** Whether the `match inSym with | some 0 => … | some _
=> …` numeral patterns on `Option (Fin 2)` reduce, given an input symbol
of the form `some (boolEmb b)` under a hypothesis on `b`.

**Measurement 3.** Whether the `q = spikeA` branch, which binds neither
`inSym` nor `work`, reduces with both left opaque. The spec's § The
machine states as design constraints that `tr` is constant in the work
symbol except at two `(state, input symbol)` pairs and constant in the
input symbol at the plant state; this is what tests both.

If any of the three fails, the alternatives are a match on `Fin.mk`
patterns (`| ⟨0, _⟩ => …`) or a vector-valued `tr` through
`Matrix.vecCons`, reduced by `Matrix.cons_val_zero` and
`Matrix.cons_val_succ`. Measure whichever is needed, restructure `tr`,
and correct the spec.

- [ ] **Step 3: Add the closed-form configuration at an opaque count**

```lean
/-- The spike's configuration at an opaque count `d`, with the input head
indexed by the same variable. -/
def spikeCfg (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length) :
    Cfg 1 (Fin 2) (Fin 2) input where
  state := some spikeB
  inputPos := ⟨d, by omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := (d : ℤ)
```

The input position is `d`, not a constant. Every non-halting arm of
`spikeTM` moves the input head left, so a family holding `inputPos` fixed
cannot be a step invariant of it — the machine's own movement refutes the
statement before any measurement is taken. The real `sweepCfg` couples
the two for the same reason, and a spike that does not is measuring a
different machine.

Two consequences the statements below carry. The step lemma needs a
hypothesis on the input symbol, since an opaque `input[d - 1]` does not
select an arm — this is what `tr_live_node_deep` will take as `hbit`. And
`1 ≤ d` is needed wherever the position is decremented.

- [ ] **Step 4: Measure the work-symbol read at an opaque position**

State and prove:

```lean
theorem spikeCfg_workSymbol (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length) :
    (spikeCfg input d h).workTapeSymbols 0 =
      if d = 0 then some 0 else if d = 1 then some 1 else none := by
  _
```

Expected route: `unfold Cfg.workTapeSymbols spikeCfg`, then `dsimp only`
— without it `split_ifs` leaves goals with no usable constraints and
`omega` fails — then `split_ifs <;> first | rfl | omega`. Record whether
`Int.decEq` at `↑d` blocks reduction, which is
what the spec's § The proof architecture assumes, and what the working
order of `cases` and `unfold step` is.

- [ ] **Step 5: Measure a leftward work-head move at a cast position**

State and prove:

```lean
theorem spikeCfg_step (input : List (Fin 2)) (d : ℕ) (hi : d ≤ input.length)
    (h : 2 ≤ d) (hs : input[d - 1]'(by omega) = 1) :
    spikeTM.step (spikeCfg input d hi) = spikeCfg input (d - 1) (by omega) := by
  _
```

The `hs` hypothesis selects the arm; without it the machine's behaviour
at an opaque `input[d - 1]` is undetermined and the statement is false.

This is the measurement most likely to fail. The copying prototype's
rightward move closed by bare `rfl` because `Int.ofNat t + Int.ofNat 1`
reduces, and the tree scanner's node case is entirely decrements.
Expected route: `rw [step_of_state _ _ spikeB …, tr-resolution lemma]`,
`Cfg.ext`, `dsimp only`, then the `workTapePos` field.

Two fields are nontrivial, not one. `workTapePos` is the cast question
below. `inputPos` is a second and independent obligation —
`moveInputPos ⟨d, _⟩ (-1) = ⟨d - 1, _⟩` — which needs `moveInputPos`'s
`dite` split, or Cslib's `moveInputPos_neg_of_ne_left`, together with the
same cast normalisation. This is the input-position coupling Step 3
introduced, so it is the field the spike exists to exercise.

Two things to record separately about the cast, because they are
different questions. `omega` is expected to handle `↑(d - 1)` at
`ℕ → ℤ` natively, so no `Int.natCast_sub` should be needed — confirm
that. But `omega` is expected to fail on the transition's `-1` until the
`SignType`-to-`ℤ` coercion is normalised, since it treats that cast as an
atom and reports `↑(-1)`; confirm that `signNegOne` closes it, and note
that having `signNegOne` in context is enough — `omega` consumes it as a
linear hypothesis, so an explicit `rw` is optional. `dsimp only` alone
does not normalise the cast.

- [ ] **Step 6: Measure a conditional state field**

Add a second configuration whose `state` field is
`if P then some 0 else some 1` for an opaque `P : Prop` with a
`Decidable` instance, and prove a step lemma against it. Record whether
`step` unfolds and `Cfg.ext` closes with an `ite` in the state field, and
whether `cases h : P` before or after `unfold step` is the working order.

- [ ] **Step 7: Measure `Cfg.inputSymbol` at both guards**

Prove two lemmas about the spike's configuration: one reading at a
position of the form `⟨k, _⟩` with `1 ≤ k` through `inputSymbolInner`,
with `List.length_map` and `List.getElem_map` in the same step; and one
reading at position `0`, which takes `Cfg.inputSymbol`'s **first** guard,
an equality at `Fin (n + 2)`. The prototype exercised only the second
guard. Record what closes each.

- [ ] **Step 8: Measure the composition and the bundled motive**

Prove that two toy phases compose by `configs_add` and
`outputString_add_eq_append`, neither having been used by either
prototype. Then prove a two-index recursion with the bundled motive:

```lean
theorem spikeCfg_configs (input : List (Fin 2)) (n : ℕ) (hi : n ≤ input.length)
    (hs : ∀ i, ∀ _ : i < n, input[i] = 1) :
    ∀ j, ∀ _ : j < n,
      spikeTM.configs (spikeCfg input n hi) j = spikeCfg input (n - j) (by omega) ∧
      spikeTM.outputString (spikeCfg input n hi) j = [] := by
  _
```

The bound is `j < n`, not `j ≤ n`. At `j = n` the machine steps from
`d = 1`, where the work head reads the second marker rather than blank
and so takes the arm that does not move it; the closed form would put it
at `0`. This is the spike's own boundary and does not indicate anything
about the real sweep, whose `sweepCfg` has no marker at the count's own
cell. `spikeCfg_step`'s `2 ≤ d` hypothesis is the same fact stated one
step earlier.

Record whether `Nat.rec` with a motive carrying `∀ h : k + j = n` and a
`by omega` inside a family application elaborates, and whether proof
irrelevance reconciles the differing bound proofs. Drive the recursion
with an explicit `Nat.rec`, not the `induction` tactic, which
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
induction through recursors bars. Handoff item 26
records that `omega` treats an unreduced `Nat.zero` as an atom, so name
each base case's index at a literal first.

- [ ] **Step 9: Measure that one transition-resolution lemma serves both
consumers**

`step` and `outputSymbol` both call
`tm.tr q cfg.inputSymbol cfg.workTapeSymbols` on identical arguments. Task
6's ten lemmas rest on one resolution serving both, which is the largest
economy in the design. State a resolution lemma for the spike's second
state and use it to close both a step lemma and an
`outputSymbol … = none` lemma. Record whether both consumers accept it.

- [ ] **Step 10: Measure cross-module reduction and the mirror's `decide`**

Create `Geb/Internal/TreeScannerSpikeMirror.lean` importing the spike,
and there — not in the spike module — assert by `decide` a machine
output over the **whole six-word list** the real mirror will use, since
`decide` evaluates the list equality in one kernel call and a single-word
measurement does not predict the total. Route the assertion through a
named `def`, not an anonymous `example`: `lake shake` runs over this
module too, and an anonymous `example` leaves no olean constant
reference, so shake would report the spike's own import as removable. This
is B3's
`FoldSpikeMirror.lean` pattern, and it exists because an in-module
`example` does not reproduce the condition a `GebTests/` mirror faces.

Record: whether `decide` closes; at what `set_option maxRecDepth`;
whether a configuration defined in one module reduces against `initCfg`
from a consuming module, which is what `seekCfg w 0 = initCfg` will
assert across the `Machine.lean`/`Steps.lean` boundary; and whether
`@[expose]` is required for it.

- [ ] **Step 11: Record the measurements and commit**

Write the ten outcomes into the commit message, numbered to match the
spec's stage-0 bullets. If any falsifies a spec
assumption, correct
`docs/superpowers/specs/2026-08-12-b5-time-space-bound-design.md` in the
same commit and note the correction.

```bash
jj commit -m "chore(scanner): prototype the tree scanner's proof mechanics"
```

---

### Task 3: The machine

**Files:**

- Create: `Geb/Internal/Computability/TreeScanner/Machine.lean`
- Create: `Geb/Internal/Computability/TreeScanner.lean`
- Create: `Geb/Internal/Computability.lean`
- Modify: `Geb/Internal.lean`

**Interfaces:**

- Consumes: Task 2's chosen transition encoding.
- Produces: `Geb.TreeScanner.boolEmb : Bool ↪ Fin 2`;
  `stSeek stPlant stLive stDead : Fin 4`;
  `treeScanner : MultiTapeTM 1 (Fin 2) (Fin 4)`.

- [ ] **Step 1: Create the module with its header and the embedding**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Mathlib.Data.Tree.Ranked.Binary

/-!
# A linear-time tree scanner

A deterministic multi-tape Turing machine deciding
`RankedAlphabet.Binary.binRanked.validBool`. The pending count is the
work head's position, with distinct markers at cells `0` and `1` so that
one read separates a count of `0`, of `1`, and of `2` or more — the
three-way distinction a node bit's guard and the final test between them
require. The machine is the one-counter recognizer for a prefix-code term
language.

## Main definitions

- `boolEmb` — the input alphabet's embedding into the machine alphabet.
- `stSeek`, `stPlant`, `stLive`, `stDead` — the four states.
- `treeScanner` — the machine.
- `seekCfg`, `plantCfg`, `sweepCfg` — the closed-form configurations.

## Main statements

- `validBool_eq_ok_and_depth` — the decision function as the pair of
  conditions the machine computes.

## Implementation notes

`Cfg` is indexed by the input, so no proof here inducts on the input;
each configuration is a closed form in a step or drop index.

## Tags

Turing machine, tree, preorder encoding, linear time
-/

@[expose] public section

namespace Geb.TreeScanner

open Turing MultiTapeTM RankedAlphabet.Binary

/-- The input alphabet's embedding into the machine alphabet: `false` to
`0` and `true` to `1`. -/
def boolEmb : Bool ↪ Fin 2 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- `false` embeds as the machine alphabet's first symbol. -/
@[simp] theorem boolEmb_false : boolEmb false = 0 := rfl

/-- `true` embeds as the machine alphabet's second symbol. -/
@[simp] theorem boolEmb_true : boolEmb true = 1 := rfl
```

These are `@[simp]` conveniences, not necessities: `boolEmb false` is
defeq to `0`, so a resolution lemma closes by `rw [projection, hbit]` and
`rfl` without them. They are stated because the emitting step and the
`docs/index.md` entry both read better against a literal, and because a
`simp` set that has them need not fall back on `rfl`.

- [ ] **Step 2: Build**

Run: `lake build Geb.Internal.Computability.TreeScanner.Machine`
Expected: PASS.

- [ ] **Step 3: Name the four states**

Each carries an assigned bound proof, following `leafSym` and `nodeSym`
in `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`; handoff item 2 records
that an inline `⟨0, by decide⟩` leaves the bound an unassigned
metavariable.

```lean
/-- The state that walks the input head to the right end. -/
def stSeek : Fin 4 := ⟨0, by omega⟩

/-- The state that writes the second marker. -/
def stPlant : Fin 4 := ⟨1, by omega⟩

/-- The state that sweeps a live scan right to left. -/
def stLive : Fin 4 := ⟨2, by omega⟩

/-- The state that sweeps a failed scan right to left. -/
def stDead : Fin 4 := ⟨3, by omega⟩
```

- [ ] **Step 4: Define the transition function**

Written so that `tr` is constant in its work-symbol argument except at
`stLive` with input `some 1` and `stLive` with input `none`, and constant
in its input-symbol argument at `stPlant`. Both are design constraints of
the spec's § The machine; Task 2 Step 2 measured that they reduce.

```lean
/-- The machine. One work tape; the count is the work head's position,
with a marker at cell `0` and a different marker at cell `1`. -/
def treeScanner : MultiTapeTM 1 (Fin 2) (Fin 4) where
  q₀ := stSeek
  tr q inSym work :=
    if q = stSeek then
      match inSym with
      | none => { inputMove := -1, workActions := fun _ ↦ (some (some 0), 1),
                  outS := none, q' := some stPlant }
      | some _ => { inputMove := 1, workActions := fun _ ↦ (none, 0),
                    outS := none, q' := some stSeek }
    else if q = stPlant then
      { inputMove := 0, workActions := fun _ ↦ (some (some 1), -1),
        outS := none, q' := some stLive }
    else if q = stLive then
      match inSym with
      | some 0 => { inputMove := -1, workActions := fun _ ↦ (none, 1),
                    outS := none, q' := some stLive }
      | some _ =>
        match work 0 with
        | none => { inputMove := -1, workActions := fun _ ↦ (none, -1),
                    outS := none, q' := some stLive }
        | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                      outS := none, q' := some stDead }
      | none =>
        match work 0 with
        | some 1 => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                      outS := some 1, q' := none }
        | _ => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                 outS := some 0, q' := none }
    else
      match inSym with
      | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                    outS := none, q' := some stDead }
      | none => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                  outS := some 0, q' := none }
```

If Task 2 Step 2 selected a different encoding, use it here and keep the
same behaviour; the case table above is normative, the syntax is not.

- [ ] **Step 5: Build**

Run: `lake build Geb.Internal.Computability.TreeScanner.Machine`
Expected: PASS.

- [ ] **Step 6: Create the two index files**

`Geb/Internal/Computability/TreeScanner.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.TreeScanner.Machine

/-!
# The tree scanner

Index for the tree scanner's modules.
-/
```

`Geb/Internal/Computability.lean` follows the same shape, importing
`Geb.Internal.Computability.TreeScanner`.

- [ ] **Step 7: Add the import to `Geb/Internal.lean`**

Insert `public import Geb.Internal.Computability` in alphabetical order
among the existing imports. Without it the new modules stay outside
`lake lint`'s environment, which is what makes the later allowlist
entries meaningful.

- [ ] **Step 8: Build and lint**

Run: `lake build` then `lake lint`
Expected: both PASS. `lake lint` runs the whole Batteries env-linter set
— `docBlame`, `simpNF`, `unusedArguments` and the rest — as well as
`GebMeta.detectNonstandardAxiom`, so read which linter failed before
diagnosing.

If the axiom linter is the one that fails, `Machine.lean` has reached
`Classical.choice`. Two exposures: an `omega` in a `Fin` bound proof,
which handoff item 5 records as possible; and `boolEmb.inj'`'s `simp`,
which runs in a closure reaching mathlib's `Fin` order API, where this
repository's own rule records that instance search selects a
choice-dependent `LawfulBEq (Fin n)`. Task 2 measures both. The remedy is
to discharge the bound over individually named hypotheses and to replace
the `simp` with an explicit case analysis, per
`docs/rules/lean-coding.md` § Constructive-only Lean code. If neither
cleans it, the contingency is to move the affected declaration to
`Steps.lean` and record in the spec that `Machine.lean`'s choice-free
content is smaller than the spec's § Constructive posture states — which
bears on the criterion Task 14 Step 3 corrects. Do not allowlist
`Machine.lean` without that spec correction.

- [ ] **Step 9: Commit**

```bash
jj commit -m "feat(scanner): add the tree scanner machine and its states"
```

---

### Task 4: The configurations

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Machine.lean`

**Interfaces:**

- Consumes: `treeScanner`, `boolEmb`, the four states.
- Produces: `seekCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length)`,
  `plantCfg (w : List Bool)`,
  `sweepCfg (w : List Bool) (k : ℕ) (h : k ≤ w.length)`, all at
  `Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb)`; and their field projection
  lemmas.

- [ ] **Step 1: Define the three configurations**

```lean
/-- The configuration after `t` seek steps: the input head at `t + 1`,
the work tape blank and its head at cell `0`. At `t = 0` this is
`initCfg`. -/
def seekCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := some stSeek
  inputPos := ⟨t + 1, by simp only [List.length_map]; omega⟩
  workTapes _ _ := none
  workTapePos _ := 0

/-- The configuration after the seek's exit step: the first marker
written, the work head at cell `1`, the input head at position
`w.length`. -/
def plantCfg (w : List Bool) : Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := some stPlant
  inputPos := ⟨w.length, by simp only [List.length_map]; omega⟩
  workTapes _ z := if z = 0 then some 0 else none
  workTapePos _ := 1

/-- The configuration at the sweep boundary where `w.drop k` has been
consumed: the count is that suffix's pending depth and the state is live
exactly when the suffix's scan has not failed. -/
def sweepCfg (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := if ok (w.drop k) then some stLive else some stDead
  inputPos := ⟨k, by simp only [List.length_map]; omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := (depth (w.drop k) : ℤ)
```

- [ ] **Step 2: Build**

Run: `lake build Geb.Internal.Computability.TreeScanner.Machine`
Expected: PASS.

- [ ] **Step 3: State the field projections**

One lemma per field per configuration, each `rfl` where the field is
unconditional. Handoff item 12 and the spec's fact 3 both record why
these exist: a step lemma must cite them rather than unfold the
configuration, since unfolding replaces it with a structure literal and
invalidates any hypothesis about its projections.

```lean
@[simp] theorem seekCfg_state (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    (seekCfg w t h).state = some stSeek := rfl

@[simp] theorem seekCfg_inputPos_val (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    (seekCfg w t h).inputPos.val = t + 1 := rfl

@[simp] theorem seekCfg_workTapePos (w : List Bool) (t : ℕ) (h : t ≤ w.length)
    (i : Fin 1) : (seekCfg w t h).workTapePos i = 0 := rfl

theorem seekCfg_workTapes (w : List Bool) (t : ℕ) (h : t ≤ w.length)
    (i : Fin 1) (z : ℤ) : (seekCfg w t h).workTapes i z = none := rfl
```

Give the matching four for `plantCfg` and `sweepCfg`. `sweepCfg_state`
is not `rfl`-shaped in the same way, so state it as the conditional:

```lean
theorem sweepCfg_state (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    (sweepCfg w k h).state = if ok (w.drop k) then some stLive else some stDead :=
  rfl
```

Follow the prototype in not marking the work-tape projections `@[simp]`;
the spec's fact 3 records that not every projection wants it.

- [ ] **Step 4: State the work-symbol resolution**

`Cfg.workTapeSymbols` measures no axioms, so this belongs here rather
than in `Steps.lean`.

```lean
theorem sweepCfg_workTapeSymbols (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    (sweepCfg w k h).workTapeSymbols 0 =
      if depth (w.drop k) = 0 then some 0
      else if depth (w.drop k) = 1 then some 1 else none := by
  _
```

State also the companion at the unapplied function, which is the form
the transition-resolution lemmas need — `tr` takes the work-symbol
*function*, not its value at `0`, so a lemma stated at
`… .workTapeSymbols 0` never matches inside a `tr` application:

```lean
theorem sweepCfg_workTapeSymbols_eq (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    (sweepCfg w k h).workTapeSymbols =
      fun _ ↦ if depth (w.drop k) = 0 then some 0
        else if depth (w.drop k) = 1 then some 1 else none := by
  funext i
  _
```

Route for both: `unfold Cfg.workTapeSymbols`, cite `sweepCfg_workTapes`
and `sweepCfg_workTapePos`, then `split_ifs <;> first | rfl | omega`. The
surviving goals after `split_ifs` are `Option (Fin 2)` equalities, not
arithmetic, so `omega` alone does not close them; `omega` does relate
`(↑d : ℤ) = 0` to `d = 0`, which is the half of the split it is for. Task
2 Step 4 measured this exact shape.

- [ ] **Step 5: Prove `seekCfg w 0 = initCfg`**

```lean
theorem seekCfg_zero (w : List Bool) :
    seekCfg w 0 (Nat.zero_le _) = treeScanner.initCfg (w.map boolEmb) := by
  _
```

`rfl` closes this: `initCfg` is
`⟨some tm.q₀, 1, fun _ _ ↦ none, fun _ ↦ 0⟩` and `treeScanner.q₀` is
`stSeek`. Both this lemma and `seekCfg` live in `Machine.lean`, so no
module boundary is crossed and Task 2 Step 10's cross-module measurement
does not bear on it. If `rfl` fails, close it by `Cfg.ext` and the field
projections, the prototype's route, which costs two lines.

- [ ] **Step 6: Build and lint**

Run: `lake build` then `lake lint`
Expected: both PASS, with `Machine.lean` still unallowlisted.

- [ ] **Step 7: Commit**

```bash
jj commit -m "feat(scanner): add the scanner's closed-form configurations"
```

---

### Task 5: The decision-function bridge

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Machine.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.Binary.ok`, `depth`, `buf_scanFinal_eq_nil`.
- Produces: `validBool_eq_ok_and_depth`.

This lemma is choice-free — it mentions only `RankedAlphabet`
declarations — so it lives here rather than in an allowlisted module.

- [ ] **Step 1: State and prove the bridge**

```lean
/-- At width one no incomplete block survives, so the decision function
is the pair of conditions the machine computes. -/
theorem validBool_eq_ok_and_depth (w : List Bool) :
    binRanked.validBool w = (ok w && depth w == 1) := by
  _
```

Route: `unfold RankedAlphabet.validBool ok depth`, rewrite by
`buf_scanFinal_eq_nil`, then `List.isEmpty_nil` and `Bool.and_true`. `&&`
is left-associative, so `validBool` parses as
`(live && buf.isEmpty) && (depth == 1)` and the rewrites apply in that
order. `RankedAlphabet.Binary.valid_iff_ok_and_depth_eq_one` is
deliberately not used: `Valid` is defined as `validBool w = true`, so
routing through a `Prop` and back is a detour.

- [ ] **Step 2: Build, lint, commit**

Run: `lake build` then `lake lint`

```bash
jj commit -m "feat(scanner): state the decision function as ok and depth"
```

---

### Task 6: The transition-resolution lemmas

**Files:**

- Create: `Geb/Internal/Computability/TreeScanner/Steps.lean`
- Modify: `Geb/Internal/Computability/TreeScanner.lean`
- Modify: `GebMeta.lean`

**Interfaces:**

- Consumes: the three configurations and their projections.
- Produces: `seekCfg_inputSymbol`, `seekCfg_inputSymbol_end`,
  `sweepCfg_inputSymbol_succ`, `sweepCfg_inputSymbol_zero`; the ten
  transition-resolution lemmas `tr_seek_mid`, `tr_seek_exit`, `tr_plant`,
  `tr_live_leaf`, `tr_live_node_deep`, `tr_live_node_shallow`,
  `tr_live_end_accept`, `tr_live_end_reject`, `tr_dead_mid`,
  `tr_dead_end`; and `outputSymbol_seekCfg`, `outputSymbol_plantCfg`,
  `outputSymbol_sweepCfg_succ`.

`step` and `outputSymbol` both call
`treeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols` on identical
arguments, so one lemma per case discharges the step lemma and the
no-emission lemma together, and the input-symbol resolution is performed
once rather than twice. Task 2 Step 9 measured that both consumers use
the same lemma.

- [ ] **Step 1: Create the module and add its allowlist entry**

Header, `module`, `@[expose] public section` and
`namespace Geb.TreeScanner` as in `Machine.lean`. Its imports are
`Geb.Internal.Computability.TreeScanner.Machine` and
`Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, which is
where `configs_add`, `configs_zero`, `configs_succ_eq_step'`,
`outputString_succ`, `outputString_add_eq_append`, `inputSymbolInner` and
the `moveInputPos` lemmas live. It does **not** need `TapeLemmas`; that
is `Bound.lean`'s import, for `spaceUsed_linear`.

The module's docstring states why it is admitted: its statements mention
`step`, `configs`, `outputString` and `Cfg.inputSymbol`, each of which
depends on `Classical.choice` through Cslib's `Cfg.inputSymbol` and
`inputSymbolInner`, so nothing here can be stated choice-free.

Add `` `Geb.Internal.Computability.TreeScanner.Steps `` to
`GebMeta.classicalAllowedModules`, and correct that declaration's
docstring, which currently describes the allowlist as covering "the
categorical wrappers over mathlib's `Classical`-dependent category
theory" and says feature branches append "their own wrapper module
names"; both are falsified by this entry.

- [ ] **Step 2: State the input-symbol projections**

```lean
theorem sweepCfg_inputSymbol_succ (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    (sweepCfg w (k + 1) h).inputSymbol = some (boolEmb w[k]) := by
  _

theorem sweepCfg_inputSymbol_zero (w : List Bool) :
    (sweepCfg w 0 (Nat.zero_le _)).inputSymbol = none := by
  _
```

and the two the seek phase needs:

```lean
theorem seekCfg_inputSymbol (w : List Bool) (t : ℕ) (h : t < w.length) :
    (seekCfg w t (Nat.le_of_lt h)).inputSymbol = some (boolEmb w[t]) := by
  _

theorem seekCfg_inputSymbol_end (w : List Bool) :
    (seekCfg w w.length (Nat.le_refl _)).inputSymbol = none := by
  _
```

`sweepCfg_inputSymbol_succ` and `seekCfg_inputSymbol` route through
`inputSymbolInner`, which needs `inputPos.val = 1 + k` — note the
argument order, `1 + k` and not `k + 1` — and `k < (w.map boolEmb).length`,
so `List.length_map` and `List.getElem_map` are both needed in the same
step. `sweepCfg_inputSymbol_zero` takes `Cfg.inputSymbol`'s **first**
guard, an equality at `Fin (n + 2)`; `seekCfg_inputSymbol_end` takes the
**second**, at `ℕ` with the coercion on the left. The spec's fact 8
records the difference and Task 2 Step 7 measured both.

- [ ] **Step 3: State one transition-resolution lemma per case**

Each has the shape

```lean
theorem tr_live_leaf (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = false) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 1),
        outS := none, q' := some stLive } := by
  rw [sweepCfg_inputSymbol_succ, hbit]
  rfl
```

Note what it does **not** take: a liveness hypothesis. `tr` receives the
state as an explicit argument, so no resolution lemma can consult
liveness, and an unused binder is reported by Batteries'
`unusedArguments` env-linter, which `lake lint` runs — not `lake build`.
Each lemma below takes only the hypotheses its own reduction
consumes.

The other nine, in full:

```lean
theorem tr_seek_mid (w : List Bool) (t : ℕ) (h : t < w.length) :
    treeScanner.tr stSeek (seekCfg w t (Nat.le_of_lt h)).inputSymbol
        (seekCfg w t (Nat.le_of_lt h)).workTapeSymbols =
      { inputMove := 1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stSeek }

theorem tr_seek_exit (w : List Bool) :
    treeScanner.tr stSeek (seekCfg w w.length (Nat.le_refl _)).inputSymbol
        (seekCfg w w.length (Nat.le_refl _)).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (some (some 0), 1),
        outS := none, q' := some stPlant }

theorem tr_plant (w : List Bool) :
    treeScanner.tr stPlant (plantCfg w).inputSymbol (plantCfg w).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (some (some 1), -1),
        outS := none, q' := some stLive }

theorem tr_live_node_deep (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = true) (hd : 2 ≤ depth (w.drop (k + 1))) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, -1),
        outS := none, q' := some stLive }

theorem tr_live_node_shallow (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = true) (hd : depth (w.drop (k + 1)) < 2) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stDead }

theorem tr_live_end_accept (w : List Bool) (hd : depth w = 1) :
    treeScanner.tr stLive (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 1, q' := none }

theorem tr_live_end_reject (w : List Bool) (hd : depth w ≠ 1) :
    treeScanner.tr stLive (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 0, q' := none }

theorem tr_dead_mid (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.tr stDead (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stDead }

theorem tr_dead_end (w : List Bool) :
    treeScanner.tr stDead (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 0, q' := none }
```

`tr_live_end_*`'s hypotheses are on `depth w`, so their proofs rewrite
`w.drop 0` to `w` by `List.drop_zero` before citing
`sweepCfg_workTapeSymbols`. Route for all ten: rewrite by the
input-symbol projection and by the bit hypothesis, as the worked proof
above does; where the case reads the work symbol, first
by an intermediate `have` collapsing the tape to a constant, since
rewriting by `sweepCfg_workTapeSymbols_eq` alone leaves an `ite` on an
opaque `depth` inside the `tr` argument and the transition does not
reduce:

```lean
  have hw : (sweepCfg w (k + 1) h).workTapeSymbols = fun _ ↦ (none : Option (Fin 2)) := by
    rw [sweepCfg_workTapeSymbols_eq]
    funext i
    split_ifs <;> first | rfl | omega
```

with `fun _ ↦ some 0` or `fun _ ↦ some 1` in the shallow and end cases.
`rw [if_neg …]` is not the repair: `if_neg` is deprecated at this pin and
so is an error. All four of `tr_live_node_deep`,
`tr_live_node_shallow`, `tr_live_end_accept` and `tr_live_end_reject`
need this `have`; then reduce the transition by the
encoding
Task 2 selected. `boolEmb_false` and `boolEmb_true` are the `@[simp]`
lemmas that let the bit hypothesis reach the numeral pattern, and are
cited only where the rewrite does not close without them —
`tr_seek_mid` and `tr_dead_mid` take the catch-all arm and need
neither. Their case coverage:

| Lemma | State | Input | Work-symbol hypothesis |
| --- | --- | --- | --- |
| `tr_seek_mid` | `stSeek` | `some _` | none |
| `tr_seek_exit` | `stSeek` | `none` | none |
| `tr_plant` | `stPlant` | any | none |
| `tr_live_leaf` | `stLive` | `some (boolEmb false)` | none |
| `tr_live_node_deep` | `stLive` | `some (boolEmb true)` | `2 ≤ depth (w.drop (k+1))` |
| `tr_live_node_shallow` | `stLive` | `some (boolEmb true)` | `depth (w.drop (k+1)) < 2` |
| `tr_live_end_accept` | `stLive` | `none` | `depth w = 1` |
| `tr_live_end_reject` | `stLive` | `none` | `depth w ≠ 1` |
| `tr_dead_mid` | `stDead` | `some _` | none |
| `tr_dead_end` | `stDead` | `none` | none |

`tr_plant` takes no input hypothesis: the plant row is a catch-all in the
input column precisely so that the plant step is uniform in `n`, the
input head there reading `some (w.map boolEmb)[n-1]` when `1 ≤ n` and
`none` when `n = 0`.

- [ ] **Step 4: Derive the no-emission facts**

```lean
theorem outputSymbol_seekCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    treeScanner.outputSymbol (seekCfg w t h) = none := by
  _

theorem outputSymbol_plantCfg (w : List Bool) :
    treeScanner.outputSymbol (plantCfg w) = none := by
  _

theorem outputSymbol_sweepCfg_succ (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.outputSymbol (sweepCfg w (k + 1) h) = none := by
  _
```

Each is `unfold outputSymbol`, the configuration's state projection, and
the matching transition-resolution lemma, whose `outS` field is `none`.

Two of them need a case split the third does not.
`outputSymbol_seekCfg` is stated for all `t ≤ w.length`, and the seek
transition differs at `t = w.length` — `tr_seek_exit` rather than
`tr_seek_mid` — so it splits on `t = w.length`.
`outputSymbol_sweepCfg_succ` splits on liveness and on the bit, and in
the live node branch must still resolve the work symbol (hence the depth)
far enough to select the transition's arm, even though `outS` is `none`
in every branch.

- [ ] **Step 5: Build, lint, commit**

Run: `lake build` then `lake lint` and `lake lint -- GebTests`

```bash
jj commit -m "feat(scanner): resolve the transition at each configuration"
```

---

**The step-lemma route.** Every step lemma in Tasks 7 to 11, and the
three `outputSymbol` lemmas of Task 6 Step 4, need one shared lemma
first, because two natural routes both fail:

- `rw` on the state projection alone leaves the outer
  `match cfg.state with` unreduced, so the transition-resolution lemma
  finds no `tr` application to rewrite;
- `simp only` citing the state projection and the transition-resolution
  lemma **together** fails too: the state projection fires first and
  iota-reduces, producing the raw structure projection `treeScanner.2`,
  against which the resolution lemma's pattern no longer matches. It then
  contributes nothing, and `linter.unusedSimpArgs` makes that an error.

State this in `Steps.lean` before anything else:

```lean
/-- A machine's step from a known state, in the form that names `tr`. -/
theorem step_of_state {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    tm.step cfg =
      { state := (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).q'
        inputPos := moveInputPos cfg.inputPos
          (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove
        workTapes := fun i ↦
          match ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).1 with
          | none => cfg.workTapes i
          | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
        workTapePos := fun i ↦ cfg.workTapePos i +
          ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).2 } := by
  unfold step
  rw [hq]
  rfl
```

The trailing `rfl` is required: `rw`'s own closing `rfl` runs at reducible
transparency, and Cslib's `step` destructures the transition through a
`let`-shaped `match` that needs iota.

Every step lemma then opens `rw [step_of_state _ _ q hq, tr_…]`, which
puts the transition in the named form the resolution lemmas are stated
against, so they fire. After that: `refine Cfg.ext ?_ ?_ ?_ ?_ <;>
dsimp only`, then the four fields.

State one more lemma beside it, which every leftward work-head move
needs:

```lean
/-- The transition's leftward movement, as an integer. -/
theorem signNegOne : ((-1 : SignType) : ℤ) = -1 := rfl
```

Without it the `workTapePos` field of any decrementing step lemma fails:
`omega` treats the `SignType`-to-`ℤ` coercion as an atom and reports
`f := ↑(-1)`. The `+1` direction needs nothing, closing by `rfl`.

For the `inputPos` field, Cslib states `moveInputPos_pos_of_ne_right` and
`moveInputPos_neg_of_ne_left` at `SignType.pos` and `SignType.neg`, while
the machine's transitions write `inputMove := 1` and `-1`.
`(1 : SignType)` is defeq to `.pos` but not syntactically equal, so `rw`
fails where `exact` succeeds: state the movement as a `have` at
`SignType.pos` or `.neg` and close by `exact`, as `copyIn_step` does in
the prototype.

`split_ifs <;> first | rfl | omega` is safe where no hypothesis in
context already decides one of the conditions — it is, at Task 4 Step 4.
Inside the Task 9 case branches a hypothesis often does, `split_ifs`
consumes it, and `omega` becomes unreachable, which
`linter.unusedTactic` reports as an error. Use `split_ifs` and discharge
the branches individually there.

### Task 7: The seek phase

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Steps.lean`

**Interfaces:**

- Consumes: `tr_seek_mid`, `outputSymbol_seekCfg`, `seekCfg_zero`.
- Produces: `seekCfg_step`, `configs_seek`.

- [ ] **Step 1: State and prove the seek step lemma**

```lean
theorem seekCfg_step (w : List Bool) (t : ℕ) (h : t + 1 ≤ w.length) :
    treeScanner.step (seekCfg w t (by omega)) = seekCfg w (t + 1) h := by
  _
```

Route: the shared step-lemma shape above, citing `seekCfg_state` and
`tr_seek_mid` in one `simp only`. The `inputPos` field goes through
`moveInputPos_pos_of_ne_right`, whose hypothesis is `p.val ≠ n + 1`,
available from `h`, and which must be applied by `exact` against a `have`
at `SignType.pos`. The work tape is blank on both sides, so
`Function.update` does not appear.

- [ ] **Step 2: State and prove the seek phase theorem**

```lean
theorem configs_seek (w : List Bool) :
    ∀ t, ∀ h : t ≤ w.length,
      treeScanner.configs (treeScanner.initCfg (w.map boolEmb)) t = seekCfg w t h ∧
      treeScanner.outputString (treeScanner.initCfg (w.map boolEmb)) t = [] := by
  refine Nat.rec ?_ ?_
  · _
  · _
```

Base case: `configs_zero` and `seekCfg_zero` for the first conjunct,
`outputString` at zero for the second. Step case: `configs_succ_eq_step'`
and `seekCfg_step` for the first, `outputString_succ` and
`outputSymbol_seekCfg` for the second. Both conjuncts are carried
together so that the output obligation is discharged in the same
recursion rather than in a second one.

- [ ] **Step 3: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: both PASS.

```bash
jj commit -m "feat(scanner): prove the seek phase's configuration"
```

---

### Task 8: The plant boundary

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Steps.lean`

**Interfaces:**

- Consumes: `tr_seek_exit`, `tr_plant`, `seekCfg_inputSymbol_end`.
- Produces: `seekCfg_exit`, `plantCfg_step`.

- [ ] **Step 1: The exit step**

```lean
theorem seekCfg_exit (w : List Bool) :
    treeScanner.step (seekCfg w w.length (Nat.le_refl _)) = plantCfg w := by
  _
```

At `t = w.length` the input head is at `w.length + 1`, which
`Cfg.inputSymbol` reads as `none` by its second guard — an equality at
`ℕ`, per the spec's fact 8. The step writes the first marker at cell `0`
while the head is there, moves the work head right to `1`, and moves the
input head left. This covers `n = 0` with no separate case, `seekCfg w 0`
being `initCfg`. `Function.update` appears here for the first time; the
work-tape field goes from the blank function to `if z = 0 then some 0
else none` by `funext` and `split_ifs`.

- [ ] **Step 2: The plant step**

```lean
theorem plantCfg_step (w : List Bool) :
    treeScanner.step (plantCfg w) = sweepCfg w w.length (Nat.le_refl _) := by
  _
```

The right-hand side's conditional state field resolves to the live branch
because `w.drop w.length = []` by `List.drop_length` and `ok [] = true`
by `rfl` through `RankedAlphabet.scanFinal_nil`; its `workTapePos`
resolves to `0` because `depth [] = 0` the same way. The step writes the
second marker at cell `1` and moves the work head back to `0`; the input
head does not move. `Function.update` appears here as it does in the exit
step: the work-tape field goes from `if z = 0 then some 0 else none` to
the two-marker function by `funext` and `split_ifs`, this being the
second and last such obligation in the branch. `tr_plant` is a catch-all
in the input column, so no case analysis on `n` or on the bit is needed.

- [ ] **Step 3: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: both PASS.

```bash
jj commit -m "feat(scanner): prove the seek exit and the plant step"
```

---

### Task 9: The sweep step lemma

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Steps.lean`

**Interfaces:**

- Consumes: `tr_live_leaf`, `tr_live_node_deep`, `tr_live_node_shallow`,
  `tr_dead_mid`, `sweepCfg_inputSymbol_succ`, `sweepCfg_workTapeSymbols`,
  `boolEmb_false`, `boolEmb_true`, and the scan lemmas below.
- Produces: `sweepCfg_step`.

This lemma carries the design's content. Everything it scrutinises
belongs to the **source** configuration, at index `k + 1`.

- [ ] **Step 1: State it**

```lean
theorem sweepCfg_step (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.step (sweepCfg w (k + 1) h) = sweepCfg w k (by omega) := by
  _
```

- [ ] **Step 2: Set up the advance and the case analysis**

Opening moves, in order. Note that `w.drop k` does **not** occur in the
goal at the outset — it occurs only inside `sweepCfg`'s body, which the
discipline of Task 4 Step 3 forbids unfolding — so the advance rewrite —
`List.drop_eq_getElem_cons`, whose hypothesis is `k < w.length` — comes
after `Cfg.ext` and the projections have exposed it, not before.

1. case on `w[k]`, which is a term rather than a variable, so the case
   hypothesis is rewritten in rather than substituted;
2. case on `ok (w.drop (k + 1))`, the **source's** liveness;
3. in the live node branch, case three ways on `depth (w.drop (k + 1))`
   against `0`, `1` and `2 ≤`, which is what resolves
   `sweepCfg_workTapeSymbols`'s nested `ite` to a literal so that the
   transition's arm can be selected;
4. within each case, the shared step-lemma route above. First build the
   state hypothesis at a definite state, since `sweepCfg`'s state field
   is an `ite`: `have hst : (sweepCfg w (k + 1) h).state = some stLive :=
   by rw [sweepCfg_state, hok]; rfl`, the trailing `rfl` reducing
   `if true then some stLive else some stDead`. Then
   `rw [step_of_state _ _ stLive hst, tr_…]` — not a `simp only` citing
   the state projection, which the route block explains fails. Then
   `refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only`;
   `refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only`;
5. now the fields. The `state` field rewrites by `ok_cons_false` or
   `ok_cons_true` and then reduces by `split_ifs` — `if_pos` and `if_neg`
   are deprecated at this pin and so are errors. The `inputPos` field
   goes through `moveInputPos_neg_of_ne_left`, whose hypothesis `p ≠ 0`
   is an equality at `Fin (input.length + 2)`, applied by `exact` against
   a `have` at `SignType.neg`. The `workTapes` field is `funext` and
   `sweepCfg_workTapes` on both sides, the tape being identical. The
   `workTapePos` field is the table below.

- [ ] **Step 3: Discharge the four live and two dead cases**

| Case | Target's state, from | Target's count, from |
| --- | --- | --- |
| dead | `scanStep_of_not_live` | unchanged; work head does not move |
| live, leaf | `ok_cons_false` | `depth_cons_false_of_ok`, head `+1` |
| live, node, `2 ≤ d` | `ok_cons_true` | `depth_cons_true_of_ok_of_two_le_depth`, head `-1` |
| live, node, `d < 2` | `ok_cons_true` gives `false` | `scanStep_true_of_live_of_buf_nil_of_depth_lt_two` preserves `depth`; head does not move |

`scanStep_true_of_live_of_buf_nil_of_depth_lt_two` takes `s.buf = []`,
discharged by `buf_scanFinal_eq_nil`. It and `scanStep_of_not_live`
return a `Scan` constructor application, whose projections need
`dsimp only` — handoff item 12. Both route through `scanFinal_cons`
first.

The `workTapePos` field crosses `ℕ` and `ℤ`: the deep node case relates a
head displacement of `-1` to `depth (true :: v) = depth v - 1` at `ℕ`.
`omega` handles `↑(a - b)` at `ℕ → ℤ` natively under `2 ≤ depth v`; Task
2 Step 5 measured whether an explicit cast lemma is needed instead.

The work tape is identical on both sides — nothing is written after the
plant step — so `Function.update` does not appear anywhere in this proof.

- [ ] **Step 4: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: both PASS.

```bash
jj commit -m "feat(scanner): prove one sweep step against the scan"
```

---

### Task 10: The sweep configuration theorem

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Steps.lean`

**Interfaces:**

- Consumes: `sweepCfg_step`, `outputSymbol_sweepCfg_succ`.
- Produces: `configs_sweep`.

- [ ] **Step 1: State it with the linking equation in the motive**

```lean
theorem configs_sweep (w : List Bool) :
    ∀ j, ∀ k, ∀ h : k + j = w.length,
      treeScanner.configs (sweepCfg w w.length (Nat.le_refl _)) j =
          sweepCfg w k (by omega) ∧
        treeScanner.outputString (sweepCfg w w.length (Nat.le_refl _)) j = [] := by
  refine Nat.rec ?_ ?_
  · _
  · _
```

The family descends in `k` while the step count ascends in `j`, so the
motive carries `k + j = w.length` to link them; indexing this way means
nothing subtracts. Base case: `j = 0` forces `k = w.length`, and
`configs_zero` closes the first conjunct. Step case: from
`k + (j + 1) = w.length` obtain `(k + 1) + j = w.length` by `omega`,
apply the induction hypothesis at `k + 1`, then `configs_succ_eq_step'`
and `sweepCfg_step`. `configs_add` is not the lemma for a single step;
`configs_succ_eq_step'` is, and Task 7 Step 2 already uses it.

Handoff item 26 records that `omega` treats an unreduced `Nat.zero` as an
atom, so name the base case's index at a literal before calling it. Task
2 Step 8 measured whether `by omega` inside a family application in the
motive elaborates, and whether proof irrelevance reconciles the differing
bound proofs.

- [ ] **Step 2: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: both PASS.

```bash
jj commit -m "feat(scanner): prove the sweep's configuration theorem"
```

---

### Task 11: The emitting step

**Files:**

- Modify: `Geb/Internal/Computability/TreeScanner/Steps.lean`

**Interfaces:**

- Consumes: `tr_live_end_accept`, `tr_live_end_reject`, `tr_dead_end`,
  `sweepCfg_inputSymbol_zero`, `validBool_eq_ok_and_depth`, `configs_seek`,
  `seekCfg_exit`, `plantCfg_step`, `configs_sweep`, `outputSymbol_seekCfg`,
  `outputSymbol_plantCfg`, `outputSymbol_sweepCfg_succ`.
- Produces: `sweepCfg_zero_halts`, `outputSymbol_sweepCfg_zero`,
  `halts_at`, `outputString_eq`.

- [ ] **Step 1: The halting and output projections**

The emitting step needs no configuration equality. Nothing downstream
uses the halted configuration.

```lean
theorem sweepCfg_zero_halts (w : List Bool) :
    (treeScanner.step (sweepCfg w 0 (Nat.zero_le _))).state = none := by
  _

theorem outputSymbol_sweepCfg_zero (w : List Bool) :
    treeScanner.outputSymbol (sweepCfg w 0 (Nat.zero_le _)) =
      some (boolEmb (binRanked.validBool w)) := by
  _
```

The second is where the machine's answer meets the specification. Three
cases: dead, by `tr_dead_end`, emitting `false`; live with the work head
reading the second marker, by `tr_live_end_accept`, emitting `true`; live
otherwise, by `tr_live_end_reject`, emitting `false`. Each is matched to
`validBool_eq_ok_and_depth`'s `ok w && depth w == 1` after rewriting
`w.drop 0` to `w` by `List.drop_zero`.

- [ ] **Step 2: Compose the three phases**

```lean
theorem halts_at (w : List Bool) :
    (treeScanner.configs (treeScanner.initCfg (w.map boolEmb))
      (2 * w.length + 3)).state = none := by
  _

theorem outputString_eq (w : List Bool) :
    treeScanner.outputString (treeScanner.initCfg (w.map boolEmb))
        (2 * w.length + 3) =
      [boolEmb (binRanked.validBool w)] := by
  _
```

Route for both: first re-associate `2 * w.length + 3` to
`(w.length + 1) + 1 + w.length + 1` by `show … by omega`, since the two
are not syntactically equal and `configs_add` matches on the sum's shape;
then `configs_add` at that decomposition,
rewriting by `configs_seek`, then `configs_succ_eq_step'` and
`seekCfg_exit` to peel the exit step, then `configs_succ_eq_step'` and
`plantCfg_step` for the plant step, then `configs_sweep` — `configs_add`'s
inner term is not a named
configuration, so each composition step rewrites by the preceding phase's
theorem before the next applies. For the output, `outputString_add_eq_append`
splits the same way, the first three summands being `[]` by the phase
theorems and the no-emission facts, and the last being the single
emission of Step 1.

- [ ] **Step 3: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: both PASS.

```bash
jj commit -m "feat(scanner): compose the phases and emit the answer"
```

---

### Task 12: The bound

**Files:**

- Create: `Geb/Internal/Computability/TreeScanner/Bound.lean`
- Modify: `Geb/Internal/Computability/TreeScanner.lean`
- Modify: `GebMeta.lean`

**Interfaces:**

- Consumes: `halts_at`, `outputString_eq`.
- Produces: `computableInTimeAndSpace_validBool`.

- [ ] **Step 1: Create the module and add its allowlist entry**

Header, `module`, `@[expose] public section` and
`namespace Geb.TreeScanner` as in `Machine.lean`. Its imports are
`Geb.Internal.Computability.TreeScanner.Steps` and
`Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`, the latter
being where `spaceUsed_linear` lives and which no earlier module imports.

Its docstring states that it is admitted because `spaceUsed` is a
`Finset.image` through `visitedByTapeHead`, and mathlib's `Finset.image`
depends on `Classical.choice` — a root neither this repository nor Cslib
can remove without redefining the space measure.

- [ ] **Step 2: State and prove the headline theorem**

```lean
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace
      (fun w : List Bool ↦ [binRanked.validBool w])
      (fun n ↦ 2 * n + 3) (fun n ↦ 2 * n + 4) := by
  refine ⟨1, 2, 4, boolEmb, treeScanner, fun w ↦ ?_⟩
  _
```

Supply `2 * w.length + 3` as the step witness, with
`t' ≤ (fun n ↦ 2 * n + 3) w.length` by `le_refl`. `List.length_map` is
not wanted here: `ComputesFunInTimeAndSpace` bounds against
`t input.length` for the unmapped `input : List Bool`, and `halts_at` and
`outputString_eq` are already stated at `2 * w.length + 3`. What is
needed instead is the rewrite
`((fun w ↦ [binRanked.validBool w]) w).map boolEmb =
[boolEmb (binRanked.validBool w)]`. Supply the machine's **actual**
`treeScanner.spaceUsed (treeScanner.initCfg (w.map boolEmb))
(2 * w.length + 3)` as the space witness, so that
`ComputesInTimeAndSpace`'s space conjunct — an equality, not an
inequality — is discharged by `rfl`. Bound it by
`le_trans (spaceUsed_linear _ _) (by simp)`: at one work tape
`spaceUsed_linear` gives `1 * t + 1`, and
`1 * (2 * n + 3) + 1 = 2 * n + 4`. Use `simp`, not `omega`: the residual
goal is `1 * (2 * w.length + 3) + 1 ≤ (fun n ↦ 2 * n + 4) w.length`, and
`omega` does not beta-reduce, treating the redex as an atom. This is the
form `TMSpike.id_computable` uses.

The three conjuncts of `ComputesInTimeAndSpace` are then `halts_at`,
`outputString_eq` and `rfl`.

- [ ] **Step 3: Build, lint, commit**

Run: `lake build` then `lake lint`
Expected: PASS, with `Machine.lean` unallowlisted and `Steps.lean` and
`Bound.lean` allowlisted.

```bash
jj commit -m "feat(scanner): bound the scanner's time and space"
```

---

### Task 13: The test mirror

**Files:**

- Create: `GebTests/Internal/Computability/TreeScanner/Machine.lean`
- Create: `GebTests/Internal/Computability/TreeScanner.lean`
- Create: `GebTests/Internal/Computability.lean`
- Modify: `GebTests/Internal.lean`
- Modify: `GebMeta.lean`

**Interfaces:**

- Consumes: `treeScanner`, `boolEmb`.
- Produces: nothing later tasks use.

- [ ] **Step 1: Write the mirror through a named `def`**

`scripts/pre-push.sh` runs `lake shake`, which infers required imports
from the constants an olean references. An anonymous
`example … := by decide` leaves no such reference, so shake would report
the import of the module under test as removable and pre-push would fail.
Build the assertion from a named `def`, as the repository's other test
files do.

```lean
/-- The words the mirror checks. -/
def sampleWords : List (List Bool) :=
  [[], [false], [true], [true, false], [false, true, false],
   [true, true, false, false, false]]

/-- The scanner's output on each sample word. -/
def sampleOutputs : List (List (Fin 2)) :=
  sampleWords.map fun w ↦
    treeScanner.outputString (treeScanner.initCfg (w.map boolEmb))
      (2 * w.length + 3)

/-- The scanner emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (binRanked.validBool w)] := by
  decide
```

The right-hand side names `binRanked.validBool` rather than
hand-computed literals, which is what the spec's § Artifacts asks for: a
check written against literals verifies the machine against the plan
author's arithmetic, and the values here are `false, true, false, false,
false, true`. If the kernel cannot close the six-word form at Task 2 Step
10's measured budget, the fallback is to shorten `sampleWords`, not to
substitute literals.

Add `set_option maxRecDepth` only if Task 2 Step 10's measurement showed
it is needed, at the value that measurement recorded.

- [ ] **Step 2: Create the mirror's index files and import**

`GebTests/Internal/Computability/TreeScanner.lean` and
`GebTests/Internal/Computability.lean`, and add
`import GebTests.Internal.Computability` to `GebTests/Internal.lean`.
That file uses plain `import` under a `-- shake: keep-all` marker, so a
`public import` there would break the grouping handoff item 11 records.

- [ ] **Step 3: Add the mirror's allowlist entry**

It asserts `outputString` values, so its statements name the taint
frontier and it is admitted, even though `Machine.lean`, whose machine it
exercises, is not.

- [ ] **Step 4: Build, test, lint, shake, commit**

Run: `lake build`, `lake test`, `lake lint`, `lake lint -- GebTests`,
`lake build GebTests` then
`lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: all PASS. A shake report naming the module under test means the
assertion is not routed through a named `def`.

```bash
jj commit -m "test(scanner): check the scanner's output against validBool"
```

---

### Task 14: Documentation and TODO

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`
- Modify: `docs/rules/lean-coding.md`, `docs/process.md` (subject to the
  user's decision on where the correction is made)
- Modify: `styles/config/vocabularies/GebMathlib/accept.txt`

- [ ] **Step 1: Add the `docs/index.md` entries**

In topological order beside the existing `Geb/Internal/` entries:
the machine, the three configurations, the phase theorems, and the
bound.

- [ ] **Step 2: Retire the workstream in `TODO.md`**

§ Extensions of the tree recognizers is removed, since `TODO.md` records
active workstreams and says complete ones are removed with their content
merged into the persistent documentation. Three things it carries must
survive, each treated individually:

- **The subsumption record.** § Binary trees item 1 is delivered by B1
  and closes; item 2 names item 1 by number, so its reference is
  rewritten to name the construction rather than a position, and items
  2–4 renumber. Items 2, 3 and 4 stay active on their own terms. § The
  Bellantoni-Cook tree recognizer item 6 is B5 and closes; item 1, the
  tree recursor, stays active — its own text says "Its soundness is a new
  theorem, not a corollary" — and item 3's cross-reference into § Binary
  trees item 1 is redirected to `docs/index.md`.
- **Its deferrals**, moved to sections of their own.
- **The record that `BarringtonCorbett1989`,
  `BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980` and
  `BraunmuhlVerbeek1983` are unverified**, which the spec's § References
  cites.

Add new entries for the spec's § Deferred items, the allowlist withdrawal
condition, and the upstream Cslib patch.

- [ ] **Step 3: Correct the rules file and its rationale**

Three sentences change, and each states what the allowlist is for rather
than testing what a module happens to mention. In
`docs/rules/lean-coding.md` § Constructive-only Lean code, the purpose
sentence becomes:

> The allowlist exists so that a module relating our concepts to a
> `Classical.choice`-dependent concept of an external Lean library —
> mathlib's category theory (e.g. `Over`), CSLib's Turing machines — can
> do so while the constructive core stays strict.

and the admission clause of the "Split modules by what can be stated
choice-free" bullet becomes:

> Admit to `GebMeta.classicalAllowedModules` only such a wrapper, a
> module whose subject is the correspondence between a concept developed
> here and a concept of an external Lean library — Batteries, mathlib,
> CSLib — that itself uses `Classical.choice`, their `GebTests`
> parallels, and the linter's own test fixture.

In `docs/process.md` § Constructive-only discipline, the criterion
sentence keeps its main clause and generalises its second `because`:

> a module reaches `GebMeta.classicalAllowedModules` when it has no
> choice-free content of its own left to state, either because its
> content is packaging or because its subject is the correspondence
> between a concept developed here and a concept of an external Lean
> library — Batteries, mathlib, CSLib — that is itself
> `Classical`-dependent.

The class is named rather than the members enumerated, so that Batteries
or core content needs no further correction. The criterion is what the
module is *for*, not what it cannot avoid mentioning: mention is always
avoidable at a price, by reimplementing an external concept choice-free
here, and a criterion that rewards that rewards duplicating an external
library instead of corresponding to it.

`GebMeta.lean`'s declaration docstring for `classicalAllowedModules`
takes the same generalisation: it currently describes the entries as "the
categorical wrappers over mathlib's `Classical`-dependent category
theory, and the parallel test modules that exercise those wrappers", and
says feature branches append "their own wrapper module names together
with their test parallels".

- [ ] **Step 4: Append any new vocabulary terms**

The prose this task writes into `docs/index.md` and `TODO.md` may
introduce terms the Vale vocabulary does not carry. Append them to
`styles/config/vocabularies/GebMathlib/accept.txt` without reordering the
file, as preceding segments have.

- [ ] **Step 5: Lint the Markdown and commit**

Run: `npx markdownlint-cli2 '**/*.md'`, `doctoc --update-only .`,
`scripts/check-md-links.sh`

```bash
jj commit -m "doc(scanner): document the scanner and retire the workstream"
```

---

### Task 15: Removing the transient artifacts

**Files:**

- Delete: `Geb/Internal/TMSpike.lean`
- Delete: `Geb/Internal/TreeScannerSpike.lean`
- Delete: `Geb/Internal/TreeScannerSpikeMirror.lean`
- Delete: `docs/superpowers/specs/2026-08-12-b5-time-space-bound-design.md`
- Delete: `docs/superpowers/plans/2026-08-13-b5-time-space-bound-plan.md`
- Delete: `docs/superpowers/plans/2026-08-13-b5-execution-handoff.md`
- Delete: `docs/superpowers/plans/2026-08-12-b5-time-space-bound-handoff.md`

Specs and plans are transient: they record how the current state was
reached, not what it is, so they belong in history rather than on an
active branch. `CONTRIBUTING.md` § Concern shape fixes this as the
branch's final commits.

- [ ] **Step 1: Delete the three prototypes**

None was ever imported from `Geb/Internal.lean`, so no index changes.

- [ ] **Step 2: Delete the spec, the plan and the two handoffs**

- [ ] **Step 3: Run the full pre-push checklist**

Run: `scripts/pre-push.sh`
Expected: PASS. It runs `lake exe cache get`, `lake build`,
`lake build GebTests`, `lake test`, `lake lint`, `lake lint -- GebTests`
— the invocation that exercises the mirror's allowlist entry —
`lake shake`, `scripts/lint-imports.sh`, `scripts/check-commit-msg.sh`,
`scripts/lake-update-warning.sh`, `markdownlint-cli2`, `doctoc`,
`scripts/check-md-links.sh` and its own script self-tests. The
link check matters here: deleting four Markdown files breaks any link
into them.

- [ ] **Step 4: Commit**

```bash
jj commit -m "chore(scanner): remove the scanner's prototypes and specs"
```

- [ ] **Step 5: Stop**

Do not push. `AGENTS.md` § No `jj git push` without user line-by-line
review binds every segment, first creation included. Report that the
branch is ready for review.
