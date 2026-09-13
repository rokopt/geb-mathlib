# Machine bound, plan 1: programs, sequencing, primitives, loop

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Executor context](#executor-context)
- [File structure](#file-structure)
- [Commit ordering](#commit-ordering)
  - [Task 1: the register layout (`Register.lean`)](#task-1-the-register-layout-registerlean)
  - [Task 2: runs and the program contract (`Program.lean`)](#task-2-runs-and-the-program-contract-programlean)
  - [Task 3a: sequencing, definitions and lifting lemmas (`Seq.lean`)](#task-3a-sequencing-definitions-and-lifting-lemmas-seqlean)
  - [Task 3b: sequencing, the run and contract lemmas (`Seq.lean`)](#task-3b-sequencing-the-run-and-contract-lemmas-seqlean)
  - [Task 3c: sequencing a family (`SeqFin.lean`)](#task-3c-sequencing-a-family-seqfinlean)
  - [Task 4: the return phases (`Phase/Return.lean`)](#task-4-the-return-phases-phasereturnlean)
  - [Task 5: the clearing phases (`Phase/Clear.lean`)](#task-5-the-clearing-phases-phaseclearlean)
  - [Task 6a: the copying phases (`Phase/Walk.lean`)](#task-6a-the-copying-phases-phasewalklean)
  - [Task 6b: the successor phase (`Phase/Sbs.lean`)](#task-6b-the-successor-phase-phasesbslean)
  - [Task 7: the writing phases (`Phase/Write.lean`)](#task-7-the-writing-phases-phasewritelean)
  - [Task 8a: `copy` and `appendBit` (`Primitives/Copy.lean`)](#task-8a-copy-and-appendbit-primitivescopylean)
  - [Task 8b: `const` (`Primitives/Const.lean`)](#task-8b-const-primitivesconstlean)
  - [Task 8c: `sbs` (`Primitives/Sbs.lean`)](#task-8c-sbs-primitivessbslean)
  - [Task 8d: `copyRev` (`Primitives/CopyRev.lean`)](#task-8d-copyrev-primitivescopyrevlean)
  - [Task 9a: the loop machine and its body lifts (`Loop/Basic.lean`)](#task-9a-the-loop-machine-and-its-body-lifts-loopbasiclean)
  - [Task 9a': the loop's control phases (`Loop/Phases.lean`)](#task-9a-the-loops-control-phases-loopphaseslean)
  - [Task 9b: one iteration (`Loop/Iter.lean`)](#task-9b-one-iteration-loopiterlean)
  - [Task 9c: the loop's contract (`Loop/Transforms.lean`)](#task-9c-the-loops-contract-looptransformslean)
  - [Task 10: plan exit check](#task-10-plan-exit-check)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** the machine calculus of the spec's first plan: the register
layout, the program contract, sequencing, the phase machines every
primitive is built from, the primitives `const`, `copy`, `sbs`,
`copyRev` and `appendBit`, and the recursion loop, each proved against
the contract.

**Architecture:** every program is a Cslib `Turing.MultiTapeTM k Bool S`
whose arguments live on work tapes in a reversed layout. A
configuration-level predicate `Reaches` states that a machine runs from
one configuration to another in a given number of steps without halting
earlier, emitting nothing, every head within `[-1, B]`; `RunsTo` adds
that the target is halted. The contract `Transforms tm F T B` states
that from any parked configuration holding a register valuation `σ`
the machine runs, within `T` steps, to the parked halted configuration
holding `F σ`. Since `F` describes every register, sequencing is
function composition and the loop's transformer is a `List.rec`. `seq`
composes machines with `Sum` states and is proved by lifting lemmas on
configurations, so that each primitive is a `seq` of one-state or
one-transition phase machines, each with a closed-form proof of a
single phase.

**Tech Stack:** Lean 4 (toolchain in `lean-toolchain`), mathlib, Cslib's
multi-tape Turing machines, Lake, `jj`.

**Spec:** `docs/superpowers/specs/2026-09-13-size-bounded-machine-design.md`

This is the first of the three plans the spec's § Plan decomposition
mandates. It refines the spec in two respects the spec leaves to
implementation. Each primitive is a `seq` of phase machines, each of
one state or one transition, rather than one machine with a
multi-phase configuration family. The contract is stated as an exact
transformer of the whole register valuation rather than as an output
register plus a frame clause, which is the spec's contract with the
scratch registers' contents made definite; the spec's environment,
output register and frame are then properties of the transformer that
plan 2 states for the compiled expression. The loop's control reads the
recursion word from a register holding its reverse, so that the bit to
process is the register's last cell and no shift is needed; Task 9a
states the phases.

## Global constraints

Copied from the spec and the repository rules; every task's requirements
implicitly include this section.

- Every new module is literate: `set_option doc.verso true` after the
  imports, docstrings in Verso markup with a role on every code span
  (`{name}` for an imported or earlier constant, `{lit}` for anything
  else), and the module docstring's sections written as
  `Geb/Prototypes/Computability/SizeBounded/Combinators.lean` writes
  them. Copy that file's header form exactly. `meta import GebMeta` is
  needed only where `{cite}` is used; no module of this plan uses it.
- Every `def` that another module unfolds, applies `intro` to, or
  rewrites with is `@[expose] def`: a non-exposed definition cannot be
  unfolded across a module boundary. In this plan every `def` is
  `@[expose]`.
- No `induction` tactic; recursion through `Nat.rec`, `List.rec`,
  `Fin.cases` and explicit recursors only. No `noncomputable`. No
  `sorry` in a commit; `_` marks a hole while working.
- `omega` on a conjunction: `constructor <;> omega`, never one `omega`
  on `A ∧ B`. `fin_cases` is not used; a `Fin n` is eliminated by
  `match`. Deprecated names are errors under `warningAsError`: use
  `ite_eq_left` / `ite_eq_right` for `if_pos` / `if_neg` and
  `dite_eq_left` / `dite_eq_right` for `dif_pos` / `dif_neg`.
- A theorem's hypothesis that its proof does not use fails
  `unusedArguments` in `lake lint`. Hypotheses listed below that turn
  out unused are removed, not kept.
- Every module whose statements mention `Turing.MultiTapeTM.step`,
  `configs`, `outputString`, `outputSymbol`, `Cfg.inputSymbol`,
  `spaceUsedByTape` or `spaceUsed` is added to
  `GebMeta.classicalAllowedModules` in `GebMeta.lean` in the task that
  creates it. `Register.lean` is not.
- Build a module with `lake build <Module.Name>`; never `lake env lean`,
  never `lake clean`. Run `lake lint` in every task's build step.
- Line length 100; two-space indentation; copyright header as in the
  existing modules of `Geb/Prototypes/Computability/SizeBounded/`.
- One indexing module per directory (`Machine.lean`, `Machine/Phase.lean`,
  `Machine/Primitives.lean`, `Machine/Loop.lean`), each importing the
  directory's modules with `public import`, with a module docstring of
  the form `Geb/Prototypes/Computability/SizeBounded.lean` has.
- Version control is `jj`. Commit with `jj commit -m "<message>"`, then
  `jj bookmark set feat/size-bounded-machine -r @-`. Commit messages
  follow `docs/rules/ci-and-workflow.md` § Commit-message convention:
  `feat(computability): <imperative subject>`, and end with the two
  trailer lines

  ```text
  Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
  ```

  Never push.
- Names: `UpperCamelCase` for `Prop`- and `Type`-valued declarations,
  `lowerCamelCase` for other definitions, `snake_case` for theorems.
- `{name}` cannot reference a constant declared later in the same
  module; use `{lit}` for those.

## Executor context

Read before starting any task:

- `docs/rules/lean-coding.md`, in full.
- `Geb/Prototypes/Computability/TreeScanner/Machine.lean` and
  `TreeScanner/Steps.lean`: the idiom for a machine, its configuration
  families, `step_of_state`, `Cfg.ext` after `dsimp only`, and
  `configs_succ_eq_step'` with `Nat.rec`.
- `.lake/packages/cslib/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`
  lines 121 to 260 (`MultiTapeTM`, `TransitionOut`, `Cfg`, `step`,
  `configs`) and 355 to 400 (`outputString` and its lemmas).
- `Geb/Prototypes/Computability/SizeBounded/Basic.lean` lines 175 to
  200 (`sbsSem`, `evalSRN`).

Facts of the model used throughout:

- `TransitionOut.workActions i : Option (Option Bool) × SignType`. The
  first component `none` writes nothing, `some s` writes the symbol `s`
  (so `some none` writes a blank). The second component is the move:
  `1`, `0`, `-1` as `SignType` literals.
- `step` writes at each head's current cell, then moves. A transition
  with `q' := none` still applies its writes and moves; the machine
  then stays in that configuration forever (`step_of_halt`,
  `configs_of_halts`).
- The input head is never moved by any machine of this plan
  (`inputMove := 0`), and no machine emits (`outS := none`).
- `Cfg.workTapeSymbols cfg i` unfolds to
  `cfg.workTapes i (cfg.workTapePos i)`.

Lemma names verified to exist in the pinned libraries:
`Function.update_self`, `Function.update_of_ne`, `Function.update_apply`,
`Function.update_idem`, `Function.update_eq_iff`, `Int.card_Icc` (giving
`(b + 1 - a).toNat`), `List.getElem_reverse`,
`List.drop_eq_getElem_cons`, `List.take_succ_eq_append_getElem`,
`List.reverse_append`, `List.reverse_drop`, `List.getElem?_eq_none`,
`List.getElem?_eq_getElem`, `List.ext_getElem?`, `List.reverse_injective`,
`List.take_length`, `Option.ne_none_iff_exists'`, `Matrix.cons_val_zero`,
`Matrix.cons_val_one`, `Option.elim : Option α → β → (α → β) → β`.

## File structure

All under `Geb/Prototypes/Computability/SizeBounded/Machine/` unless
stated:

- `Register.lean`: `tapeOf` and its lemmas; the list lemmas the phases
  need; `Parked`, `Holds`, `Bounded`. Strict (not allowlisted).
- `Program.lean`: `step_of_state`, `Reaches`, `RunsTo`, `after`,
  `Transforms`, and their lemmas.
- `Seq.lean`: `seq`, `liftL`, `liftR`, the lifting lemmas, `Reaches.liftL`,
  `Reaches.liftR`, `RunsTo.seq`, `Transforms.seq`.
- `SeqFin.lean`: `idle`, `seqFin`, `composeFin`, `Transforms.seqFin`.
- `Phase.lean` (index), `Phase/Return.lean`, `Phase/Clear.lean`,
  `Phase/Walk.lean`, `Phase/Sbs.lean`, `Phase/Write.lean`.
- `Primitives.lean` (index), `Primitives/Copy.lean`,
  `Primitives/Const.lean`, `Primitives/Sbs.lean`,
  `Primitives/CopyRev.lean`.
- `Loop.lean` (index), `Loop/Basic.lean`, `Loop/Phases.lean`,
  `Loop/Iter.lean`, `Loop/Transforms.lean`.
- `../Machine.lean`: the index.

A duplicate to report, not to fix: `step_of_state` of Task 2 is the
generic lemma `Geb.TreeScanner.step_of_state`
(`TreeScanner/Steps.lean:95`) restated, since importing that module
would drag the scanner into this closure. Hoisting both to a shared
module is a separate branch's concern; say so in the final report.

## Commit ordering

One commit per task, in task order. Each commit builds
(`lake build Geb.Prototypes.Computability.SizeBounded.Machine`) and
lints with no `sorry` and no error.

---

### Task 1: the register layout (`Register.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Register.lean`
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine.lean`
- Modify: `Geb/Prototypes/Computability/SizeBounded.lean` (add
  `public import Geb.Prototypes.Computability.SizeBounded.Machine`)

**Interfaces:**

- Produces: `Geb.SizeBounded.Machine.tapeOf : List Bool → ℤ → Option Bool`;
  `tapeOf_nil`, `tapeOf_cons`, `tapeOf_of_lt`, `tapeOf_of_le`,
  `tapeOf_neg`, `tapeOf_update_none`, `tapeOf_injective`;
  `drop_length_sub_succ`, `reverse_take_succ`;
  `Parked : Cfg k Bool State input → Prop`;
  `Holds : Cfg k Bool State input → (Fin k → List Bool) → Prop`;
  `Bounded : (Fin k → List Bool) → ℕ → Prop`.

- [ ] **Step 1: Write the module with the definitions and the theorem
  statements, proofs as `_`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

set_option doc.verso true

/-!
# Registers of the machine calculus

A work tape holds a bitstring in reversed layout: cell {lit}`z` holds the
{lit}`z`th element of the word's reverse for {lit}`0 ≤ z < length`, and every
other cell is blank. Cell {lit}`0` is the word's last element and cell
{lit}`length - 1` its head, so that consing a bit is one write at the first
blank cell. A register valuation assigns a word to every tape; the predicates
on configurations that every program of the calculus starts from and returns
to are that every head is at cell {lit}`0` and that the tapes hold a
valuation, and a valuation is bounded when every word's length is at most
the bound.

# Main definitions

* {lit}`tapeOf` — the tape contents of a register holding a word.
* {lit}`Parked` — every work head at cell {lit}`0`.
* {lit}`Holds` — the tapes hold a valuation.
* {lit}`Bounded` — every word of a valuation is within a bound.

# Main statements

* {lit}`tapeOf_nil`, {lit}`tapeOf_cons`, {lit}`tapeOf_update_none` — the
  layout of the empty word, consing as one {name}`Function.update`, and
  blanking the head's cell as its inverse.
* {lit}`tapeOf_of_lt`, {lit}`tapeOf_of_le`, {lit}`tapeOf_neg` — the cell
  contents inside, beyond and before the word.
* {lit}`tapeOf_injective` — the layout determines the word.
* {lit}`drop_length_sub_succ`, {lit}`reverse_take_succ` — the list equations
  the copying phases step by.

# Tags

Turing machine, register, bitstring
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The tape contents of a register holding {lit}`w`: cell {lit}`z` holds
{lit}`w.reverse[z]` for {lit}`0 ≤ z < w.length` and is blank elsewhere. -/
@[expose] def tapeOf (w : List Bool) : ℤ → Option Bool :=
  fun z ↦ if 0 ≤ z then w.reverse[z.toNat]? else none

/-- The empty word's register is blank. -/
theorem tapeOf_nil : tapeOf [] = fun _ ↦ none := _

/-- Consing a bit writes it at the cell after the word. -/
theorem tapeOf_cons (b : Bool) (w : List Bool) :
    tapeOf (b :: w) = Function.update (tapeOf w) (w.length : ℤ) (some b) := _

/-- Inside the word a cell holds the corresponding element of the reverse. -/
theorem tapeOf_of_lt (w : List Bool) (z : ℤ) (h0 : 0 ≤ z) (h : z < w.length) :
    tapeOf w z = some (w.reverse[z.toNat]'(by simp; omega)) := _

/-- Beyond the word every cell is blank. -/
theorem tapeOf_of_le (w : List Bool) (z : ℤ) (h : w.length ≤ z) : tapeOf w z = none := _

/-- Before cell zero every cell is blank. -/
theorem tapeOf_neg (w : List Bool) (z : ℤ) (h : z < 0) : tapeOf w z = none := _

/-- Blanking the head's cell drops the head. -/
theorem tapeOf_update_none (b : Bool) (w : List Bool) :
    Function.update (tapeOf (b :: w)) (w.length : ℤ) none = tapeOf w := _

/-- The layout determines the word. -/
theorem tapeOf_injective : Function.Injective tapeOf := _

/-- Dropping one element fewer conses the element at the split. -/
theorem drop_length_sub_succ (w : List Bool) (s : ℕ) (hs : s < w.length) :
    w.drop (w.length - (s + 1)) =
      w.reverse[s]'(by simp; omega) :: w.drop (w.length - s) := _

/-- The reverse of a longer prefix conses the next element. -/
theorem reverse_take_succ (w : List Bool) (s : ℕ) (hs : s < w.length) :
    (w.take (s + 1)).reverse = w[s] :: (w.take s).reverse := _

/-- Every work head at cell {lit}`0`. -/
@[expose] def Parked {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) : Prop :=
  ∀ i, cfg.workTapePos i = 0

/-- The tapes hold the valuation {lit}`σ`. -/
@[expose] def Holds {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : Prop :=
  ∀ i, cfg.workTapes i = tapeOf (σ i)

/-- Every word of the valuation has length at most {lit}`B`. -/
@[expose] def Bounded {k : ℕ} (σ : Fin k → List Bool) (B : ℕ) : Prop :=
  ∀ i, (σ i).length ≤ B

end

end Geb.SizeBounded.Machine
```

Write `Machine.lean` as an index with the header form of
`Geb/Prototypes/Computability/SizeBounded.lean`, importing
`Geb.Prototypes.Computability.SizeBounded.Machine.Register` for now, and
add the `Machine` import to `SizeBounded.lean`.

- [ ] **Step 2: Build to see the holes reported**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine.Register`
Expected: errors at each `_`, no other error.

- [ ] **Step 3: Prove the theorems**

These proofs were checked to elaborate:

```lean
theorem tapeOf_nil : tapeOf [] = fun _ ↦ none := by
  funext z
  simp [tapeOf]

theorem tapeOf_cons (b : Bool) (w : List Bool) :
    tapeOf (b :: w) = Function.update (tapeOf w) (w.length : ℤ) (some b) := by
  funext z
  unfold tapeOf
  by_cases hz : z = w.length
  · subst hz
    simp
  · rw [Function.update_of_ne hz]
    split_ifs with h0
    · rw [List.reverse_cons, List.getElem?_append]
      split_ifs with hlt
      · rfl
      · rw [List.length_reverse] at hlt
        have : z.toNat ≠ w.length := by omega
        simp only [List.getElem?_singleton, List.length_reverse]
        rw [ite_eq_right (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]
    · rfl

theorem tapeOf_of_lt (w : List Bool) (z : ℤ) (h0 : 0 ≤ z) (h : z < w.length) :
    tapeOf w z = some (w.reverse[z.toNat]'(by simp; omega)) := by
  unfold tapeOf
  rw [ite_eq_left h0, List.getElem?_eq_getElem]

theorem tapeOf_of_le (w : List Bool) (z : ℤ) (h : w.length ≤ z) : tapeOf w z = none := by
  unfold tapeOf
  split_ifs with h0
  · apply List.getElem?_eq_none
    simp
    omega
  · rfl

theorem tapeOf_neg (w : List Bool) (z : ℤ) (h : z < 0) : tapeOf w z = none := by
  unfold tapeOf
  rw [ite_eq_right (by omega)]
```

`tapeOf_update_none`: `rw [tapeOf_cons, Function.update_idem]`, then
`Function.update_eq_self_iff` or `funext` with `Function.update_apply`
and `tapeOf_of_le w w.length (le_refl _)` at the updated cell.

`tapeOf_injective`: from `tapeOf v = tapeOf w` derive
`v.reverse = w.reverse` by `List.ext_getElem?` (for each `n : ℕ`,
evaluate both sides at `(n : ℤ)`, where `tapeOf u n = u.reverse[n]?` by
`unfold tapeOf; rw [ite_eq_left (by omega)]` and `Int.toNat_natCast`),
then `List.reverse_injective`.

`drop_length_sub_succ`: `List.drop_eq_getElem_cons` at index
`w.length - (s + 1)` and `List.getElem_reverse`; the index arithmetic
by `omega`.

`reverse_take_succ`: `List.take_succ_eq_append_getElem hs` and
`List.reverse_append`, `List.reverse_singleton`, `List.singleton_append`.

If `simp` flags an unused argument, drop it: `unusedSimpArgs` is an
error under the package's `warningAsError`.

- [ ] **Step 4: Build and lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`
Expected: success, no warnings.

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the machine calculus register layout

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 2: runs and the program contract (`Program.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Program.lean`
- Modify: `Machine.lean` (import)
- Modify: `GebMeta.lean` (add
  `` `Geb.Prototypes.Computability.SizeBounded.Machine.Program `` to
  `classicalAllowedModules`, before the closing `]`).

**Interfaces:**

- Consumes: Task 1.
- Produces: `step_of_state`, `Reaches`, `Reaches.trans`, `Reaches.mono`,
  `RunsTo`, `RunsTo.mono`, `RunsTo.halt_configs`,
  `RunsTo.spaceUsedByTape_le`, `after`, `after_workTapes`,
  `after_workTapePos`, `after_inputPos`, `after_state`, `Transforms`,
  `Transforms.mono_time`, `Transforms.congr`.

- [ ] **Step 1: Write the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Register
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Runs and the program contract

A reach: from a configuration a machine arrives at another in a given number
of steps, halted at none of the earlier ones, emitting nothing, every head
within the interval from {lit}`-1` to a bound. A run: a reach whose target is
halted. The contract of a program of the calculus: from any parked
configuration holding a register valuation, a run to the parked halted
configuration holding the valuation's image under the program's transformer,
within a step bound, whenever the valuation and its image are within the
length bound. The transformer describes every register, so that sequencing
two programs composes their transformers.

The no-earlier-halt clause is what sequencing needs: the composite machine
hands over to its second component at the first halting step of its first, so
a run's step count must be that step.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs`,
{name}`Turing.MultiTapeTM.outputString` and
{name}`Turing.MultiTapeTM.spaceUsedByTape`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.MultiTapeTM.Cfg.inputSymbol`
or mathlib's {name}`Finset.image`.

# Main definitions

* {lit}`Reaches` — a reach between two configurations.
* {lit}`RunsTo` — a reach to a halted configuration.
* {lit}`after` — the parked halted configuration holding a valuation.
* {lit}`Transforms` — the program contract.

# Main statements

* {lit}`step_of_state` — a step from a known state, naming {lit}`tr`.
* {lit}`Reaches.trans` — reaches compose.
* {lit}`Reaches.mono`, {lit}`RunsTo.mono` — a larger head bound.
* {lit}`RunsTo.halt_configs` — after a run the machine stays put.
* {lit}`RunsTo.spaceUsedByTape_le` — a run's visited cells per tape are at
  most the bound plus two.
* {lit}`Transforms.mono_time`, {lit}`Transforms.congr` — the contract at a
  larger step bound and at a pointwise equal transformer.

# Tags

Turing machine, program, contract, space complexity
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- A machine's step from a known state, in the form that names {lit}`tr`. Generic
in the symbol type: at a fixed symbol type the statement's {lit}`match` compiles
to a matcher of its own and the proof by {lit}`rfl` fails. -/
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

/-- From {lit}`cfg`, {lit}`tm` arrives at {lit}`cfg'` at step {lit}`t`, halted
at no earlier step, emitting nothing, every head within {lit}`[-1, B]`
throughout. -/
structure Reaches {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop where
  /-- No step before {lit}`t` is halted. -/
  live : ∀ t' < t, (tm.configs cfg t').state ≠ none
  /-- The configuration at step {lit}`t`. -/
  configs_eq : tm.configs cfg t = cfg'
  /-- Nothing is emitted. -/
  output : tm.outputString cfg t = []
  /-- Every head stays within {lit}`[-1, B]`. -/
  pos : ∀ t' ≤ t, ∀ i, -1 ≤ (tm.configs cfg t').workTapePos i ∧
    (tm.configs cfg t').workTapePos i ≤ B

/-- A reach to a halted configuration. -/
structure RunsTo {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop extends Reaches tm cfg cfg' t B where
  /-- The target is halted. -/
  halted : cfg'.state = none

/-- Reaches compose. -/
theorem Reaches.trans {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg₁ cfg₂ : Cfg k Bool State input} {t₁ t₂ B : ℕ}
    (h₁ : Reaches tm cfg cfg₁ t₁ B) (h₂ : Reaches tm cfg₁ cfg₂ t₂ B) :
    Reaches tm cfg cfg₂ (t₁ + t₂) B := _

/-- A reach within one bound is a reach within any larger bound. -/
theorem Reaches.mono {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B B' : ℕ}
    (h : Reaches tm cfg cfg' t B) (hB : B ≤ B') : Reaches tm cfg cfg' t B' := _

/-- A run within one bound is a run within any larger bound. -/
theorem RunsTo.mono {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B B' : ℕ}
    (h : RunsTo tm cfg cfg' t B) (hB : B ≤ B') : RunsTo tm cfg cfg' t B' := _

/-- After a run the machine stays in the halted configuration. -/
theorem RunsTo.halt_configs {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B : ℕ}
    (h : RunsTo tm cfg cfg' t B) (s : ℕ) : tm.configs cfg (t + s) = cfg' := _

/-- Over a run the head of each tape visits at most {lit}`B + 2` cells. -/
theorem RunsTo.spaceUsedByTape_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B : ℕ}
    (h : RunsTo tm cfg cfg' t B) (i : Fin k) : tm.spaceUsedByTape cfg t i ≤ B + 2 := _

/-- The halted configuration with the heads and input head of {lit}`cfg` and
the tapes holding {lit}`σ`. -/
@[expose] def after {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : Cfg k Bool State input :=
  { cfg with state := none, workTapes := fun i ↦ tapeOf (σ i) }

/-- {lit}`after` holds the valuation. -/
@[simp] theorem after_workTapes {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) (i : Fin k) :
    (after cfg σ).workTapes i = tapeOf (σ i) := rfl

/-- {lit}`after` keeps the heads. -/
@[simp] theorem after_workTapePos {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) :
    (after cfg σ).workTapePos = cfg.workTapePos := rfl

/-- {lit}`after` keeps the input head. -/
@[simp] theorem after_inputPos {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) :
    (after cfg σ).inputPos = cfg.inputPos := rfl

/-- {lit}`after` is halted. -/
@[simp] theorem after_state {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : (after cfg σ).state = none := rfl

/-- The program contract: from a parked configuration in the initial state
holding a valuation {lit}`σ` within {lit}`B`, with {lit}`F σ` within {lit}`B`,
a run within {lit}`T` steps to the parked halted configuration holding
{lit}`F σ`. The bound on {lit}`F σ` is an assumption; the compiler discharges
it from non-size-increase. -/
@[expose] def Transforms {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (F : (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ) : Prop :=
  ∀ {input : List Bool} (cfg : Cfg k Bool State input) (σ : Fin k → List Bool),
    cfg.state = some tm.q₀ → Parked cfg → Holds cfg σ → Bounded σ B → Bounded (F σ) B →
    ∃ t ≤ T, RunsTo tm cfg (after cfg (F σ)) t B

/-- The contract at a larger step bound. -/
theorem Transforms.mono_time {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {F : (Fin k → List Bool) → Fin k → List Bool} {T T' B : ℕ}
    (h : Transforms tm F T B) (hT : T ≤ T') : Transforms tm F T' B := _

/-- The contract at a pointwise equal transformer. -/
theorem Transforms.congr {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {F F' : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ}
    (h : Transforms tm F T B) (hF : ∀ σ, F σ = F' σ) : Transforms tm F' T B := _

end

end Geb.SizeBounded.Machine
```

- [ ] **Step 2: Build to see the holes reported**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine.Program`

- [ ] **Step 3: Prove the theorems**

`Reaches.trans`: `configs_eq` by `rw [configs_add, h₁.configs_eq,
h₂.configs_eq]`. `live`: `intro t' ht'; by_cases h : t' < t₁`; the first
case is `h₁.live`; otherwise write `t' = t₁ + (t' - t₁)` (`omega`), `rw
[configs_add, h₁.configs_eq]`, and `h₂.live (t' - t₁) (by omega)`.
`output`: `rw [outputString_add_eq_append, h₁.output, h₁.configs_eq,
h₂.output]`. `pos`: the same split, with `configs_add`.

`Reaches.mono`, `RunsTo.mono`: copy the fields, weakening `pos` by
`Int.ofNat_le.mpr hB` (or `by omega` on the cast).

`RunsTo.halt_configs`: `rw [configs_add, h.configs_eq]; exact
configs_of_halts _ h.halted`.

`RunsTo.spaceUsedByTape_le`: `spaceUsedByTape` is the card of
`visitedByTapeHead`. Show
`tm.visitedByTapeHead cfg t i ⊆ Finset.Icc (-1 : ℤ) B` by
`intro z hz; obtain ⟨t', ht', rfl⟩ := mem_visitedByTapeHead.mp hz;
exact Finset.mem_Icc.mpr (h.pos t' (by omega) i)`, then
`(Finset.card_le_card this).trans` with `Int.card_Icc` giving
`(B + 1 - (-1)).toNat = B + 2` (close by `simp` then `omega`).
`mem_visitedByTapeHead` is in `TapeLemmas.lean` (`t' < t + 1`).

`Transforms.mono_time`, `Transforms.congr`: `intro _ cfg σ h1 h2 h3 h4
h5; obtain ⟨t, ht, r⟩ := h cfg σ h1 h2 h3 h4 (by rwa [hF] at h5 ...)`; for
`congr`, rewrite `after cfg (F σ)` to `after cfg (F' σ)` by `hF σ`.

- [ ] **Step 4: Allowlist, import in the index, build, lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add machine runs and the program contract

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 3a: sequencing, definitions and lifting lemmas (`Seq.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Seq.lean`
- Modify: `Machine.lean` (import), `GebMeta.lean` (allowlist).

**Interfaces:**

- Consumes: Task 2.
- Produces: `seq`, `liftL`, `liftR`, `seq_q₀`, `liftL_start`, `liftL_halt`,
  the `liftL_*` and `liftR_*` projection lemmas, `seq_step_left`,
  `seq_step_right`, `seq_outputSymbol_left`, `seq_outputSymbol_right`,
  `seq_configs_left`, `seq_configs_right`, `seq_outputString_left`,
  `seq_outputString_right`, `Reaches.liftL`, `Reaches.liftR`.

- [ ] **Step 1: Write the definitions and lemmas (the first group checked
  to elaborate)**

```lean
/-- Sequencing: run {lit}`P`, then {lit}`Q`. In an {lit}`inl` state the
transition is {lit}`P`'s with a halting successor replaced by {lit}`Q`'s
initial state; in an {lit}`inr` state it is {lit}`Q`'s. -/
@[expose] def seq {k : ℕ} {S₁ S₂ : Type} (P : MultiTapeTM k Bool S₁)
    (Q : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (S₁ ⊕ S₂) where
  q₀ := .inl P.q₀
  tr q inp work :=
    match q with
    | .inl q => let o := P.tr q inp work
      { o with q' := some (o.q'.elim (.inr Q.q₀) .inl) }
    | .inr q => let o := Q.tr q inp work
      { o with q' := o.q'.map .inr }

/-- A {lit}`P`-configuration lifted into {lit}`seq P Q`: a halted one becomes
{lit}`Q`'s start. -/
@[expose] def liftL {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) : Cfg k Bool (S₁ ⊕ S₂) input :=
  { cfg with state := some (cfg.state.elim (.inr Q.q₀) .inl) }

/-- A {lit}`Q`-configuration lifted into {lit}`seq P Q`. -/
@[expose] def liftR {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (cfg : Cfg k Bool S₂ input) : Cfg k Bool (S₁ ⊕ S₂) input :=
  { cfg with state := cfg.state.map .inr }

/-- A step of the composite from a lifted live {lit}`P`-configuration is the
lift of {lit}`P`'s step. -/
theorem seq_step_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (q : S₁) (hq : cfg.state = some q) :
    (seq P Q).step (liftL Q cfg) = liftL Q (P.step cfg) := by
  unfold step liftL
  simp only [hq]
  rfl

/-- A step of the composite from a lifted {lit}`Q`-configuration is the lift
of {lit}`Q`'s step. -/
theorem seq_step_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) :
    (seq P Q).step (liftR (S₁ := S₁) cfg) = liftR (Q.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt hq, step_of_halt]
    simp [liftR, hq]
  | some q =>
    unfold step liftR
    simp only [hq]
    rfl

/-- A halted {lit}`P`-configuration lifts to {lit}`Q`'s start. -/
theorem liftL_halt {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (h : cfg.state = none) :
    liftL Q cfg = liftR (S₁ := S₁) { cfg with state := some Q.q₀ } := by
  unfold liftL liftR
  rw [h]
  rfl

/-- The composite emits what {lit}`P` emits from a lifted live configuration. -/
theorem seq_outputSymbol_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (q : S₁) (hq : cfg.state = some q) :
    (seq P Q).outputSymbol (liftL Q cfg) = P.outputSymbol cfg := by
  unfold outputSymbol liftL
  simp only [hq]
  rfl

/-- The composite emits what {lit}`Q` emits from a lifted configuration. -/
theorem seq_outputSymbol_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) :
    (seq P Q).outputSymbol (liftR (S₁ := S₁) cfg) = Q.outputSymbol cfg := by
  unfold outputSymbol liftR
  cases hq : cfg.state
  · rfl
  · rfl
```

Add, with `_` proofs:

```lean
/-- The composite starts in {lit}`P`'s initial state. -/
theorem seq_q₀ {k : ℕ} {S₁ S₂ : Type} (P : MultiTapeTM k Bool S₁)
    (Q : MultiTapeTM k Bool S₂) : (seq P Q).q₀ = .inl P.q₀ := rfl

/-- A configuration of the composite in its initial state is the lift of the
same configuration in {lit}`P`'s initial state. -/
theorem liftL_start {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool (S₁ ⊕ S₂) input) (h : cfg.state = some (seq P Q).q₀) :
    cfg = liftL Q { cfg with state := some P.q₀ } := _

section Projections

variable {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
  (cfg : Cfg k Bool S₁ input) (cfg' : Cfg k Bool S₂ input)

/-- The left lift keeps the tapes. -/
@[simp] theorem liftL_workTapes : (liftL Q cfg).workTapes = cfg.workTapes := rfl

/-- The left lift keeps the heads. -/
@[simp] theorem liftL_workTapePos : (liftL Q cfg).workTapePos = cfg.workTapePos := rfl

/-- The left lift keeps the input head. -/
@[simp] theorem liftL_inputPos : (liftL Q cfg).inputPos = cfg.inputPos := rfl

/-- The left lift is live. -/
theorem liftL_state_ne_none : (liftL Q cfg).state ≠ none := _

/-- The right lift keeps the tapes. -/
@[simp] theorem liftR_workTapes : (liftR (S₁ := S₁) cfg').workTapes = cfg'.workTapes := rfl

/-- The right lift keeps the heads. -/
@[simp] theorem liftR_workTapePos :
    (liftR (S₁ := S₁) cfg').workTapePos = cfg'.workTapePos := rfl

/-- The right lift keeps the input head. -/
@[simp] theorem liftR_inputPos : (liftR (S₁ := S₁) cfg').inputPos = cfg'.inputPos := rfl

/-- The right lift's state is the mapped state. -/
@[simp] theorem liftR_state : (liftR (S₁ := S₁) cfg').state = cfg'.state.map .inr := rfl

end Projections

/-- While {lit}`P` has not halted, the composite mirrors {lit}`P`. -/
theorem seq_configs_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) :
    ∀ t, (∀ t' < t, (P.configs cfg t').state ≠ none) →
      (seq P Q).configs (liftL Q cfg) t = liftL Q (P.configs cfg t) := _

/-- The composite mirrors {lit}`Q` from a lifted {lit}`Q`-configuration. -/
theorem seq_configs_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) (t : ℕ) :
    (seq P Q).configs (liftR (S₁ := S₁) cfg) t = liftR (Q.configs cfg t) := _

/-- While {lit}`P` has not halted, the composite emits what {lit}`P` emits. -/
theorem seq_outputString_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) :
    ∀ t, (∀ t' < t, (P.configs cfg t').state ≠ none) →
      (seq P Q).outputString (liftL Q cfg) t = P.outputString cfg t := _

/-- From a lifted {lit}`Q`-configuration the composite emits what {lit}`Q`
emits. -/
theorem seq_outputString_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) (t : ℕ) :
    (seq P Q).outputString (liftR (S₁ := S₁) cfg) t = Q.outputString cfg t := _

/-- A reach of {lit}`P` lifts to a reach of the composite. -/
theorem Reaches.liftL {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S₁} (Q : MultiTapeTM k Bool S₂)
    {cfg cfg' : Cfg k Bool S₁ input} {t B : ℕ} (h : Reaches P cfg cfg' t B) :
    Reaches (seq P Q) (liftL Q cfg) (liftL Q cfg') t B := _

/-- A reach of {lit}`Q` lifts to a reach of the composite. -/
theorem Reaches.liftR {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) {Q : MultiTapeTM k Bool S₂}
    {cfg cfg' : Cfg k Bool S₂ input} {t B : ℕ} (h : Reaches Q cfg cfg' t B) :
    Reaches (seq P Q) (liftR cfg) (liftR cfg') t B := _
```

- [ ] **Step 2: Build to see the holes reported**

- [ ] **Step 3: Prove the lemmas**

`liftL_start`: `apply Cfg.ext <;> dsimp only [liftL]` closes the three
non-state goals itself; the remaining goal is `h`. Do not add a bullet
per field, which errors with no goals.

`liftL_state_ne_none`: `unfold liftL; exact Option.some_ne_none _`.

`seq_configs_left`: `Nat.rec`. Base: `configs_zero`. Step `t + 1`:
`rw [configs_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)),
configs_succ_eq_step']`; obtain `q` with `(P.configs cfg t).state = some q`
from `hlive t (by omega)` via `Option.ne_none_iff_exists'`; then
`seq_step_left`.

`seq_configs_right`: `Nat.rec` with `seq_step_right`.

`seq_outputString_left/right`: `Nat.rec` with `outputString_succ`,
the `configs` lemmas and the `outputSymbol` lemmas.

`Reaches.liftL`: `live` from `liftL_state_ne_none` after
`seq_configs_left`; `configs_eq` from `seq_configs_left` and
`h.configs_eq`; `output` from `seq_outputString_left`; `pos` from
`seq_configs_left` and `liftL_workTapePos`.

`Reaches.liftR`: likewise with the right lemmas; `live` from `h.live` and
`Option.map` of a `some` being a `some` (`Option.map_eq_none_iff`).

- [ ] **Step 4: Allowlist, import in the index, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add machine sequencing with its lifting lemmas

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 3b: sequencing, the run and contract lemmas (`Seq.lean`)

**Files:**

- Modify: `Geb/Prototypes/Computability/SizeBounded/Machine/Seq.lean`
  (append; add the two theorems to the module docstring).

**Interfaces:**

- Consumes: Task 3a.
- Produces: `RunsTo.seq`, `Transforms.seq`.

- [ ] **Step 1: Write**

```lean
/-- Runs compose: a run of {lit}`P` to {lit}`cfg₁` followed by a run of
{lit}`Q` from {lit}`cfg₁` restarted in {lit}`Q`'s initial state. -/
theorem RunsTo.seq {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S₁} {Q : MultiTapeTM k Bool S₂}
    {cfg cfg₁ : Cfg k Bool S₁ input} {cfg₂ : Cfg k Bool S₂ input} {t₁ t₂ B : ℕ}
    (h₁ : RunsTo P cfg cfg₁ t₁ B)
    (h₂ : RunsTo Q { cfg₁ with state := some Q.q₀ } cfg₂ t₂ B) :
    RunsTo (seq P Q) (liftL Q cfg) (liftR cfg₂) (t₁ + t₂) B := _

/-- Contracts compose: the composite transforms by the composite of the
transformers, provided the first transformer keeps the valuation within the
bound. -/
theorem Transforms.seq {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {Q : MultiTapeTM k Bool S₂} {F G : (Fin k → List Bool) → Fin k → List Bool} {T₁ T₂ B : ℕ}
    (hP : Transforms P F T₁ B) (hQ : Transforms Q G T₂ B)
    (hF : ∀ σ, Bounded σ B → Bounded (F σ) B) :
    Transforms (seq P Q) (fun σ ↦ G (F σ)) (T₁ + T₂) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`RunsTo.seq`: `toReaches` is
`(h₁.toReaches.liftL Q).trans (by rw [liftL_halt Q cfg₁ h₁.halted]; exact
h₂.toReaches.liftR P)`; `halted` is `liftR_state` with `h₂.halted`
(`Option.map_none`).

`Transforms.seq`: `intro _ cfg σ hq hpark hσ hB hGF`; rewrite `cfg` by
`liftL_start P Q cfg hq`; set `cfg₀ := { cfg with state := some P.q₀ }`;
`obtain ⟨t₁, ht₁, r₁⟩ := hP cfg₀ σ rfl hpark hσ hB (hF σ hB)`
(`Parked`/`Holds` of `cfg₀` are those of `cfg`, by `intro` and `rfl`);
`obtain ⟨t₂, ht₂, r₂⟩ := hQ { after cfg₀ (F σ) with state := some Q.q₀ } (F σ)
rfl hpark (fun i ↦ rfl) (hF σ hB) hGF`; the witness is `t₁ + t₂` with
`r₁.seq r₂`, whose target `liftR (after { after cfg₀ (F σ) with state :=
some Q.q₀ } (G (F σ)))` equals `after (liftL Q cfg₀) (G (F σ))` by
`Cfg.ext` and `rfl` on every field.

- [ ] **Step 4: Build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): compose machine runs and contracts under sequencing

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 3c: sequencing a family (`SeqFin.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/SeqFin.lean`
- Modify: `Machine.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2, 3a, 3b.
- Produces: `idle`, `idle_transforms`, `seqFin`, `seqFin_zero`,
  `seqFin_succ`, `composeFin`, `composeFin_zero`, `composeFin_succ`,
  `composeFin_bounded`, `Transforms.seqFin`.

- [ ] **Step 1: Write**

```lean
/-- The machine that halts at once, doing nothing. -/
@[expose] def idle {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- {lit}`idle` transforms by the identity in one step. -/
theorem idle_transforms {k : ℕ} (B : ℕ) : Transforms (idle (k := k)) (fun σ ↦ σ) 1 B := _

/-- Sequencing a family of machines indexed by {lit}`Fin m`, in index order,
by recursion on {lit}`m`. The state is an iterated binary sum, so that the
choice-free {lit}`FinEnum` instance on sums applies. -/
@[expose] def seqFin {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    ((i : Fin m) → MultiTapeTM k Bool (S i)) → Σ S' : Type, MultiTapeTM k Bool S' :=
  Nat.rec (fun _ _ ↦ ⟨Unit, idle⟩)
    (fun m ih S P ↦ ⟨(ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1 ⊕ S (Fin.last m),
      seq (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).2 (P (Fin.last m))⟩)

/-- The empty family sequences to {lit}`idle`. -/
theorem seqFin_zero {k : ℕ} (S : Fin 0 → Type) (P : (i : Fin 0) → MultiTapeTM k Bool (S i)) :
    seqFin 0 S P = ⟨Unit, idle⟩ := rfl

/-- A family of length {lit}`m + 1` sequences its first {lit}`m` members, then
its last. -/
theorem seqFin_succ {k m : ℕ} (S : Fin (m + 1) → Type)
    (P : (i : Fin (m + 1)) → MultiTapeTM k Bool (S i)) :
    seqFin (m + 1) S P =
      ⟨(seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1 ⊕ S (Fin.last m),
        seq (seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).2 (P (Fin.last m))⟩ := rfl

/-- The composite of a family of transformers, in index order. -/
@[expose] def composeFin {k : ℕ} : (m : ℕ) →
    (Fin m → (Fin k → List Bool) → Fin k → List Bool) → (Fin k → List Bool) → Fin k → List Bool :=
  Nat.rec (fun _ σ ↦ σ) (fun m ih F σ ↦ F (Fin.last m) (ih (fun i ↦ F i.castSucc) σ))

/-- The empty composite is the identity. -/
theorem composeFin_zero {k : ℕ} (F : Fin 0 → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) : composeFin 0 F σ = σ := rfl

/-- The composite of {lit}`m + 1` transformers applies the last after the
first {lit}`m`. -/
theorem composeFin_succ {k m : ℕ} (F : Fin (m + 1) → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) :
    composeFin (m + 1) F σ = F (Fin.last m) (composeFin m (fun i ↦ F i.castSucc) σ) := rfl

/-- A composite of bound-preserving transformers preserves the bound. -/
theorem composeFin_bounded {k : ℕ} (B : ℕ) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    ∀ σ, Bounded σ B → Bounded (composeFin m F σ) B := _

/-- Sequencing a family of programs transforms by the composite of their
transformers, in {lit}`m * T + 1` steps for a family of {lit}`m` programs each
within {lit}`T`. -/
theorem Transforms.seqFin {k : ℕ} (B T : ℕ) : ∀ (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i))
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i, Transforms (P i) (F i) T B) → (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    Transforms (seqFin m S P).2 (composeFin m F) (m * T + 1) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`idle_transforms`: one step by `configs_succ_eq_step', configs_zero,
step_of_state _ _ () hq`, then `Cfg.ext` with `dsimp only`, the tapes
by `funext i; exact (hσ i)`-style rewriting into `after`, the heads by
`moveInputPos_zero` and `add_zero`; `live` at `0` from `hq`; `output` by
`outputString_succ` and the `outputSymbol` computed by `unfold
outputSymbol; rw [hq]; rfl`; `pos` from `hpark`.

`composeFin_bounded`: `Nat.rec`; the step is `hF (Fin.last m) _ (ih ...)`.

`Transforms.seqFin`: `Nat.rec` on `m` with `S`, `P`, `F` and the two
hypotheses generalized (`intro m; refine Nat.rec ?_ ?_ m` after
`revert`). Base: `idle_transforms` through `Transforms.congr` (the
identity is `composeFin 0 F`). Step: `Transforms.seq (ih _ _ _ (fun i ↦
hP i.castSucc) (fun i σ ↦ hF i.castSucc σ)) (hP (Fin.last m))
(composeFin_bounded B m _ (fun i ↦ hF i.castSucc))`, then
`Transforms.mono_time` with `m * T + 1 + T ≤ (m + 1) * T + 1` by
`Nat.succ_mul` and `omega`, and `Transforms.congr` with
`composeFin_succ`.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): sequence indexed families of machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 4: the return phases (`Phase/Return.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase.lean`
  (index of the `Phase` directory)
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Return.lean`
- Modify: `Machine.lean` (import `Machine.Phase`), `GebMeta.lean`
  (allowlist `Machine.Phase.Return`).

**Interfaces:**

- Consumes: Tasks 2, 3a, 3b.
- Produces: `moveLeft i`, `retLeft i`, `returnTape i`, and
  `moveLeft_runsTo`, `retLeft_runsTo`, `returnTape_runsTo`.

Conventions for every phase machine of Tasks 4 to 7: the state type is
`Unit` or `Fin n`; a transition that touches tape `i` alone has
`workActions := fun j ↦ if j = i then <action> else (none, 0)`;
`inputMove := 0`; `outS := none`. The run lemma is stated for an arbitrary
configuration in the initial state whose tape `i` holds `tapeOf w` and
whose head `i` is at a given position, and names the halted
configuration as a structure update of the start. Its hypotheses are
the head position of `i`, the word on `i`, and, only where the machine
moves a head right, the length bound `w.length ≤ B`; every lemma takes
`hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B` for the
untouched heads.

- [ ] **Step 1: Write the machines and statements**

```lean
/-- Move the head of tape {lit}`i` one cell left and halt. -/
@[expose] def moveLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputMove := 0, workActions := fun j ↦ (none, if j = i then -1 else 0),
      outS := none, q' := none }

/-- Move the head of tape {lit}`i` left while it reads a bit; on reading a
blank, move right and halt. -/
@[expose] def retLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputMove := 0
      workActions := fun j ↦ (none, if j = i then (if (work i).isSome then -1 else 1) else 0)
      outS := none
      q' := if (work i).isSome then some () else none }

/-- Return the head of tape {lit}`i` to cell {lit}`0` from any cell of its
word or the blank after it: one unconditional move left, then {lit}`retLeft`. -/
@[expose] def returnTape {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Unit ⊕ Unit) :=
  seq (moveLeft i) (retLeft i)

/-- {lit}`moveLeft` runs one step. -/
theorem moveLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B)
    (hi : 0 ≤ cfg.workTapePos i) :
    RunsTo (moveLeft i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i - 1) }
      1 B := _

/-- {lit}`retLeft` from cell {lit}`p` of a register holding {lit}`w`, with
{lit}`-1 ≤ p < w.length`, runs {lit}`p + 2` steps and parks the head. -/
theorem retLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (p : ℤ) (hp : cfg.workTapePos i = p) (hp0 : -1 ≤ p) (hpw : p < w.length) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (retLeft i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i 0 }
      (p + 2).toNat B := _

/-- {lit}`returnTape` from cell {lit}`p` with {lit}`0 ≤ p ≤ w.length` runs
{lit}`p + 2` steps and parks the head. -/
theorem returnTape_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Unit ⊕ Unit) input) (hq : cfg.state = some (returnTape i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (p : ℤ) (hp : cfg.workTapePos i = p) (hp0 : 0 ≤ p) (hpw : p ≤ w.length) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (returnTape i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 }
      (p + 2).toNat B := _
```

- [ ] **Step 2: Build to see the holes reported**

- [ ] **Step 3: Prove**

`moveLeft_runsTo`: `configs_eq` by `configs_succ_eq_step', configs_zero,
step_of_state _ _ () hq`, then `Cfg.ext` with `dsimp only`; the tapes are
unchanged since every action's first component is `none` (the `match`
reduces by `rfl`); `workTapePos` by `funext j; by_cases j = i` and
`Function.update_apply`; `inputPos` by `moveInputPos_zero`. `live`:
`t' < 1` forces `t' = 0` and `hq`. `output`: `outputString_succ`,
`outputString` at `0` is `[]` by `rfl`, and the `outputSymbol` is `none`
by `unfold outputSymbol; rw [hq]; rfl`. `pos`: at `0` from `hpos`; at
`1` from the update and `hi`.

`retLeft_runsTo`: define the closed-form family

```lean
retCfg (s : ℕ) := { cfg with workTapePos := Function.update cfg.workTapePos i (p - s) }
```

for `s ≤ p + 1`, and prove by `Nat.rec` on `s` that
`(retLeft i).configs cfg s = retCfg s ∧ (retLeft i).outputString cfg s = []`
for `(s : ℤ) ≤ p + 1`, the step reading a bit because `p - s ≥ 0` and
`p - s < w.length` give `tapeOf w (p - s) = some _` by `tapeOf_of_lt`,
so `(work i).isSome = true`. At `s = p + 1` the head is at `-1`, reads
`none` by `tapeOf_neg`, and the step moves right to `0` with `q' := none`.
Then assemble `RunsTo` with `t = (p + 2).toNat`; `live` from the family
(state `some ()` for `s ≤ p + 1`). Rewrite the head position with
`Function.update_self` before applying the `tapeOf` lemmas. The path
clause: the head of `i` is at `p - s ∈ [-1, p]` and `p ≤ B` from `hpos`.

`returnTape_runsTo`: `RunsTo.seq (moveLeft_runsTo ...) (retLeft_runsTo ...)`
after rewriting `cfg` by `liftL_start`, with the intermediate head at
`p - 1`; the resulting configuration is `liftR` of the update, which is
the stated configuration by `Cfg.ext` (state `none.map inr = none`);
the step count `1 + (p - 1 + 2).toNat = (p + 2).toNat` by `omega` after
`Int.toNat_of_nonneg`.

- [ ] **Step 4: Write `Phase.lean`, allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the return phase machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 5: the clearing phases (`Phase/Clear.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Clear.lean`
- Modify: `Phase.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 4.
- Produces: `walkEnd i`, `blankLeft i`, `clear i`; `walkEnd_runsTo`,
  `blankLeft_runsTo`, `clear_runsTo`.

- [ ] **Step 1: Write**

```lean
/-- Move the head of tape {lit}`i` right while it reads a bit; halt on the
first blank, without moving. -/
@[expose] def walkEnd {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputMove := 0
      workActions := fun j ↦ (none, if j = i then (if (work i).isSome then 1 else 0) else 0)
      outS := none
      q' := if (work i).isSome then some () else none }

/-- Move the head of tape {lit}`i` left while it reads a bit, blanking each
bit read; on reading a blank, move right and halt. -/
@[expose] def blankLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputMove := 0
      workActions := fun j ↦
        if j = i then (if (work i).isSome then (some none, -1) else (none, 1)) else (none, 0)
      outS := none
      q' := if (work i).isSome then some () else none }

/-- Empty register {lit}`i` from a parked head: walk to its end, then blank
leftwards and park. -/
@[expose] def clear {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Unit ⊕ (Unit ⊕ Unit)) :=
  seq (walkEnd i) (seq (moveLeft i) (blankLeft i))

/-- {lit}`walkEnd` from cell {lit}`0` of a register holding {lit}`w` runs
{lit}`w.length + 1` steps to cell {lit}`w.length`. -/
theorem walkEnd_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (walkEnd i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
      (w.length + 1) B := _

/-- {lit}`blankLeft` from cell {lit}`w.length - 1` of a register holding
{lit}`w` runs {lit}`w.length + 1` steps, empties the register and parks. -/
theorem blankLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = (w.length : ℤ) - 1) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (blankLeft i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 }
      (w.length + 1) B := _

/-- {lit}`clear` from a parked register holding {lit}`w` runs
{lit}`2 * w.length + 3` steps, empties it and parks. -/
theorem clear_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Unit ⊕ (Unit ⊕ Unit)) input) (hq : cfg.state = some (clear i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (clear i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 }
      (2 * w.length + 3) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`walkEnd_runsTo`: family `{ cfg with workTapePos := Function.update
cfg.workTapePos i s }` for `s ≤ w.length`, by `Nat.rec`; the head reads
`some _` for `s < w.length` (`tapeOf_of_lt`) and `none` at
`s = w.length` (`tapeOf_of_le`), where the halting transition moves by
`0`.

`blankLeft_runsTo`: family, for `s ≤ w.length`, tape
`tapeOf (w.drop s)` and head at `w.length - 1 - s`. The step from `s` to
`s + 1` with `s < w.length` reads the bit at cell `w.length - 1 - s`, which
is the head of `w.drop s` (`List.drop_eq_getElem_cons`), writes a blank
there and moves left; `tapeOf (w.drop s)` updated at
`(w.drop (s + 1)).length` to `none` is `tapeOf (w.drop (s + 1))` by
`tapeOf_update_none` with `w.drop s = w[s] :: w.drop (s + 1)`. At
`s = w.length` the head is at `-1`, reads `none` (`tapeOf_neg`), and the
halting transition moves right to `0`. The path clause needs only that
the head of `i` moves left from `w.length - 1`, at most `B` by `hpos`.

`clear_runsTo`: `RunsTo.seq` of `walkEnd_runsTo` with
`RunsTo.seq (moveLeft_runsTo ...) (blankLeft_runsTo ...)`, `liftL_start`
first; step count `(w.length + 1) + (1 + (w.length + 1))` by `omega`;
the configurations agree by `Cfg.ext` and `Function.update_idem` where
the same tape is updated twice.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the clearing phase machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 6a: the copying phases (`Phase/Walk.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Walk.lean`
- Modify: `Phase.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 5.
- Produces: `copyWalk i j`, `revWalk i j`; `copyWalk_runsTo`,
  `revWalk_runsTo`.

- [ ] **Step 1: Write**

```lean
/-- Copy tape {lit}`i` onto tape {lit}`j` cell by cell, both heads moving
right, until {lit}`i` reads a blank; halt without moving. -/
@[expose] def copyWalk {k : ℕ} (i j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, 1)
          else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- Copy tape {lit}`i` onto tape {lit}`j` cell by cell, {lit}`i`'s head moving
left and {lit}`j`'s right, until {lit}`i` reads a blank; then move {lit}`i`
right and halt. -/
@[expose] def revWalk {k : ℕ} (i j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, -1)
          else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0, workActions := fun l ↦ (none, if l = i then 1 else 0),
        outS := none, q' := none }

/-- {lit}`copyWalk` from parked heads, {lit}`i` holding {lit}`w` and
{lit}`j` empty, runs {lit}`w.length + 1` steps; {lit}`j` then holds {lit}`w`
and both heads are at {lit}`w.length`. -/
theorem copyWalk_runsTo {k : ℕ} {input : List Bool} (i j : Fin k) (hij : i ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hi : cfg.workTapes i = tapeOf w) (hj : cfg.workTapes j = tapeOf [])
    (hpi : cfg.workTapePos i = 0) (hpj : cfg.workTapePos j = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (copyWalk i j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w)
        workTapePos :=
          Function.update (Function.update cfg.workTapePos i (w.length : ℤ)) j (w.length : ℤ) }
      (w.length + 1) B := _

/-- {lit}`revWalk` from {lit}`i`'s head at {lit}`w.length - 1` on a register
holding {lit}`w` and {lit}`j` empty and parked runs {lit}`w.length + 1`
steps; {lit}`j` then holds {lit}`w.reverse` with its head at {lit}`w.length`,
and {lit}`i`'s head is parked. -/
theorem revWalk_runsTo {k : ℕ} {input : List Bool} (i j : Fin k) (hij : i ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hi : cfg.workTapes i = tapeOf w) (hj : cfg.workTapes j = tapeOf [])
    (hpi : cfg.workTapePos i = (w.length : ℤ) - 1) (hpj : cfg.workTapePos j = 0) (B : ℕ)
    (hB : w.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (revWalk i j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w.reverse)
        workTapePos := Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) }
      (w.length + 1) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`copyWalk_runsTo`: family for `s ≤ w.length`: `j` holds
`tapeOf (w.drop (w.length - s))`, both heads at `s`. The step at
`s < w.length` reads `w.reverse[s]` on `i` by `tapeOf_of_lt`, and writing
it at `j`'s cell `s` turns `tapeOf (w.drop (w.length - s))` into
`tapeOf (w.drop (w.length - (s + 1)))` by `drop_length_sub_succ` and
`tapeOf_cons` (the cell index is `(w.drop (w.length - s)).length = s`,
by `List.length_drop` and `omega`). At `s = w.length`, `i` reads `none`
and the halting transition moves nothing; `w.drop 0 = w`.

`revWalk_runsTo`: family for `s ≤ w.length`: `i`'s head at
`w.length - 1 - s`, `j`'s head at `s`, and `j` holding
`tapeOf (w.take s).reverse`, whose cells are `w.take s`. At step
`s < w.length` the cell `i` reads is `w.reverse[w.length - 1 - s]`, which
is `w[s]` by `List.getElem_reverse`, and writing it at `j`'s cell `s`
gives `tapeOf (w.take (s + 1)).reverse` by `reverse_take_succ` and
`tapeOf_cons` (the cell index is `((w.take s).reverse).length = s`). At
`s = w.length`, `i` reads `none` at `-1` and the halting transition moves
`i` right to `0`; `w.take w.length = w` by `List.take_length`.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the copying phase machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 6b: the successor phase (`Phase/Sbs.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Sbs.lean`
- Modify: `Phase.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 5; `Geb.SizeBounded.sbsSem` from
  `Geb/Prototypes/Computability/SizeBounded/Basic.lean` (import it).
- Produces: `sbsWalk b x y j`, `sbsWalk_runsTo`.

- [ ] **Step 1: Write**

```lean
/-- Copy tape {lit}`x` onto tape {lit}`j` as {lit}`copyWalk` does, moving
{lit}`y`'s head right alongside while it reads a bit; when {lit}`x` reads a
blank, write {lit}`b` on {lit}`j` and move its head right if {lit}`y` still
reads a bit, and halt. -/
@[expose] def sbsWalk {k : ℕ} (b : Bool) (x y j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work x with
    | some c =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some c), 1) else if l = x then (none, 1)
          else if l = y then (none, if (work y).isSome then 1 else 0) else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0
        workActions := fun l ↦
          if l = j then (if (work y).isSome then (some (some b), 1) else (none, 0)) else (none, 0)
        outS := none, q' := none }

/-- {lit}`sbsWalk` from parked heads, {lit}`x` holding {lit}`u`, {lit}`y`
holding {lit}`v` and {lit}`j` empty, runs {lit}`u.length + 1` steps;
{lit}`j` then holds {lit}`sbsSem b u v` with its head after it, {lit}`x`'s
head is at {lit}`u.length` and {lit}`y`'s at the smaller of the two lengths. -/
theorem sbsWalk_runsTo {k : ℕ} {input : List Bool} (b : Bool) (x y j : Fin k)
    (hxy : x ≠ y) (hxj : x ≠ j) (hyj : y ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (u v : List Bool) (hx : cfg.workTapes x = tapeOf u) (hy : cfg.workTapes y = tapeOf v)
    (hj : cfg.workTapes j = tapeOf [])
    (hpx : cfg.workTapePos x = 0) (hpy : cfg.workTapePos y = 0) (hpj : cfg.workTapePos j = 0)
    (B : ℕ) (hu : u.length ≤ B) (hv : v.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (sbsWalk b x y j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b u v))
        workTapePos :=
          Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y (min
            u.length v.length : ℕ)) j ((sbsSem b u v).length : ℤ) }
      (u.length + 1) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

Family for `s ≤ u.length` as for `copyWalk` on `x` and `j`, with `y`'s
head at `min s v.length`. `unfold sbsSem`; at `s = u.length`, `x` reads
`none`; `y` reads `some _` exactly when `u.length < v.length`
(`tapeOf_of_lt` / `tapeOf_of_le` at `min`), which is the condition
`u.length + 1 ≤ v.length` of `sbsSem`; in that case the halting
transition writes `b` at `j`'s cell `u.length`, so `j` holds
`tapeOf (b :: u)` by `tapeOf_cons`, and its head moves to
`u.length + 1`; otherwise nothing is written and `j` holds `tapeOf u`.
Split with `by_cases h : u.length + 1 ≤ v.length` and `rw [ite_eq_left h]`
/ `rw [ite_eq_right h]` on the `sbsSem` and the `min`. The path clause
needs `u.length + 1 ≤ B` in the first branch, which follows from
`u.length + 1 ≤ v.length ≤ B`.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the successor phase machine

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 7: the writing phases (`Phase/Write.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Write.lean`
- Modify: `Phase.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 5.
- Produces: `writeBit b i`, `constWalk w i`; `writeBit_runsTo`,
  `constWalk_runsTo`.

- [ ] **Step 1: Write**

```lean
/-- Write {lit}`b` at the head of tape {lit}`i`, without moving, and halt. -/
@[expose] def writeBit {k : ℕ} (b : Bool) (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputMove := 0
      workActions := fun j ↦ if j = i then (some (some b), 0) else (none, 0)
      outS := none, q' := none }

/-- Write {lit}`w` on tape {lit}`i` from the head rightwards in reversed
layout: state {lit}`s` writes {lit}`w.reverse[s]` and moves right, and state
{lit}`w.length` halts without moving. -/
@[expose] def constWalk {k : ℕ} (w : List Bool) (i : Fin k) :
    MultiTapeTM k Bool (Fin (w.length + 1)) where
  q₀ := 0
  tr s _ _ :=
    if h : s.val < w.length then
      { inputMove := 0
        workActions := fun j ↦
          if j = i then (some (some (w.reverse[s.val]'(by simp; omega))), 1) else (none, 0)
        outS := none, q' := some ⟨s.val + 1, by omega⟩ }
    else
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- {lit}`writeBit` at cell {lit}`w.length` of a register holding {lit}`w`
runs one step and leaves it holding {lit}`b :: w`. -/
theorem writeBit_runsTo {k : ℕ} {input : List Bool} (b : Bool) (i : Fin k)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w) (hp : cfg.workTapePos i = (w.length : ℤ))
    (B : ℕ) (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (writeBit b i) cfg
      { cfg with state := none, workTapes := Function.update cfg.workTapes i (tapeOf (b :: w)) }
      1 B := _

/-- {lit}`constWalk` from a parked empty register runs {lit}`w.length + 1`
steps and leaves it holding {lit}`w` with its head at {lit}`w.length`. -/
theorem constWalk_runsTo {k : ℕ} {input : List Bool} (w : List Bool) (i : Fin k)
    (cfg : Cfg k Bool (Fin (w.length + 1)) input) (hq : cfg.state = some 0)
    (hw : cfg.workTapes i = tapeOf []) (hp : cfg.workTapePos i = 0) (B : ℕ)
    (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (constWalk w i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf w)
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
      (w.length + 1) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`writeBit_runsTo`: one step; the tape update is `tapeOf_cons` read
right to left; the path clause is `hpos` since no head moves.

`constWalk_runsTo`: family for `s ≤ w.length`: state `some ⟨s, _⟩`, tape
`tapeOf (w.drop (w.length - s))`, head at `s`; the step uses
`drop_length_sub_succ` and `tapeOf_cons` as `copyWalk` does. The
transition is a `dite` on `s < w.length`; resolve with `dite_eq_left` /
`dite_eq_right`.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the writing phase machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8a: `copy` and `appendBit` (`Primitives/Copy.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Primitives.lean`
  (index)
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Primitives/Copy.lean`
- Modify: `Machine.lean` (import `Machine.Primitives`), `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 7.
- Produces: `copy i j`, `appendBit b i`, `copy_transforms`,
  `appendBit_transforms`.

Conventions for Tasks 8a to 8d: each primitive is a `seq` chain of
phase machines; its theorem is `Transforms` with the transformer a
`Function.update` of the valuation. The proof pattern:
`intro _ cfg σ hq hpark hσ hB hFB`; rewrite `cfg` by `liftL_start` at
each `seq` layer; chain `RunsTo.seq` through the phases, each phase
applied to the configuration the previous one produced (a structure
update of `cfg`), whose projections are computed by
`Function.update_apply`, `Function.update_self`,
`Function.update_of_ne` and the disjointness hypotheses; the words on
the registers come from `hσ`, their bounds from `hB`, and the bound on
the written word from `hFB` at the output register
(`Function.update_self`). The witness `t` is the sum of the phase
counts, at most the stated bound by `omega`. The final configuration
equals `after cfg (Function.update σ j ...)` by `Cfg.ext` and `funext`
with `Function.update_apply`, `tapeOf` of an updated valuation being
the updated tape; the heads, `Function.update (...) j 0`, equal
`cfg.workTapePos` by `funext`, `Function.update_apply` and `hpark`,
not by `Cfg.ext` alone.

- [ ] **Step 1: Write**

```lean
/-- Copy register {lit}`i` into register {lit}`j`: clear {lit}`j`, copy, park
both. -/
@[expose] def copy {k : ℕ} (i j : Fin k) :=
  seq (clear j) (seq (copyWalk i j) (seq (returnTape i) (returnTape j)))

/-- Cons {lit}`b` onto register {lit}`i`: walk to its end, write, park. -/
@[expose] def appendBit {k : ℕ} (b : Bool) (i : Fin k) :=
  seq (walkEnd i) (seq (writeBit b i) (returnTape i))

/-- {lit}`copy` transforms the valuation by copying {lit}`i` to {lit}`j`, in
{lit}`5 * B + 12` steps. -/
theorem copy_transforms {k : ℕ} (i j : Fin k) (hij : i ≠ j) (B : ℕ) :
    Transforms (copy i j) (fun σ ↦ Function.update σ j (σ i)) (5 * B + 12) B := _

/-- {lit}`appendBit` transforms the valuation by consing {lit}`b` onto
{lit}`i`, in {lit}`2 * B + 5` steps. -/
theorem appendBit_transforms {k : ℕ} (b : Bool) (i : Fin k) (B : ℕ) :
    Transforms (appendBit b i) (fun σ ↦ Function.update σ i (b :: σ i)) (2 * B + 5) B := _
```

The phase counts: `copy` is `clear j` (`2 * (σ j).length + 3`),
`copyWalk` (`(σ i).length + 1`), `returnTape i` and `returnTape j` from
`(σ i).length` (`(σ i).length + 2` each), total at most `5 * B + 8`.
`appendBit` is `walkEnd i` (`(σ i).length + 1`), `writeBit` (`1`),
`returnTape i` from `(σ i).length` (`(σ i).length + 2`), total at most
`2 * B + 4`. State the theorems with the bounds above, which leave
slack.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove** as the conventions say. For `appendBit`,
  `returnTape_runsTo`'s `p ≤ w.length` with `p = (σ i).length` and
  `w = b :: σ i` is `List.length_cons` and `omega`; `hFB` is not needed,
  so bind it as `_`. Of the primitives only `const` uses `hFB`.

- [ ] **Step 4: Write `Primitives.lean`, allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the copy and append primitives

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8b: `const` (`Primitives/Const.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Primitives/Const.lean`
- Modify: `Primitives.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 7.
- Produces: `const w j`, `const_transforms`.

- [ ] **Step 1: Write**

```lean
/-- Write the constant {lit}`w` into register {lit}`j`: clear, write, park. -/
@[expose] def const {k : ℕ} (w : List Bool) (j : Fin k) :=
  seq (clear j) (seq (constWalk w j) (returnTape j))

/-- {lit}`const` transforms the valuation by setting {lit}`j` to {lit}`w`, in
{lit}`4 * B + 9` steps. The bound {lit}`w.length ≤ B` is the contract's
assumption on the transformed valuation. -/
theorem const_transforms {k : ℕ} (w : List Bool) (j : Fin k) (B : ℕ) :
    Transforms (const w j) (fun σ ↦ Function.update σ j w) (4 * B + 9) B := _
```

Phase counts: `clear j` (`2 * (σ j).length + 3`), `constWalk`
(`w.length + 1`), `returnTape j` from `w.length` (`w.length + 2`); total
at most `4 * B + 6`. `w.length ≤ B` is `hFB j` after
`Function.update_self`.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove** as the conventions say.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the constant primitive

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8c: `sbs` (`Primitives/Sbs.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Primitives/Sbs.lean`
- Modify: `Primitives.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 7.
- Produces: `sbs b x y j`, `sbs_transforms`.

- [ ] **Step 1: Write**

```lean
/-- The size-bounded successor into register {lit}`j`: clear, walk, park all
three. -/
@[expose] def sbs {k : ℕ} (b : Bool) (x y j : Fin k) :=
  seq (clear j) (seq (sbsWalk b x y j) (seq (returnTape x) (seq (returnTape y) (returnTape j))))

/-- {lit}`sbs` transforms the valuation by setting {lit}`j` to the
size-bounded successor of {lit}`x` bounded by {lit}`y`, in
{lit}`7 * B + 16` steps. -/
theorem sbs_transforms {k : ℕ} (b : Bool) (x y j : Fin k) (hxy : x ≠ y) (hxj : x ≠ j)
    (hyj : y ≠ j) (B : ℕ) :
    Transforms (sbs b x y j) (fun σ ↦ Function.update σ j (sbsSem b (σ x) (σ y)))
      (7 * B + 16) B := _
```

Phase counts: `clear j` (`2 * (σ j).length + 3`), `sbsWalk`
(`(σ x).length + 1`), `returnTape x` from `(σ x).length`, `returnTape y`
from `min (σ x).length (σ y).length` (at most `(σ y).length`),
`returnTape j` from `(sbsSem b (σ x) (σ y)).length` (at most `B` by
`hFB j`); total at most `6 * B + 10`.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove** as the conventions say; `Matrix`-free, since the
  transformer reads `σ x` and `σ y` directly.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the size-bounded successor primitive

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8d: `copyRev` (`Primitives/CopyRev.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Primitives/CopyRev.lean`
- Modify: `Primitives.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 7.
- Produces: `copyRev i j`, `copyRev_transforms`.

- [ ] **Step 1: Write**

```lean
/-- Copy the reverse of register {lit}`i` into register {lit}`j`: clear
{lit}`j`, walk {lit}`i` to its end and one back, copy leftwards, park
{lit}`j`. -/
@[expose] def copyRev {k : ℕ} (i j : Fin k) :=
  seq (clear j) (seq (walkEnd i) (seq (moveLeft i) (seq (revWalk i j) (returnTape j))))

/-- {lit}`copyRev` transforms the valuation by setting {lit}`j` to the
reverse of {lit}`i`, in {lit}`5 * B + 12` steps. -/
theorem copyRev_transforms {k : ℕ} (i j : Fin k) (hij : i ≠ j) (B : ℕ) :
    Transforms (copyRev i j) (fun σ ↦ Function.update σ j (σ i).reverse) (5 * B + 12) B := _
```

Phase counts: `clear j` (`2 * (σ j).length + 3`), `walkEnd i`
(`(σ i).length + 1`), `moveLeft` (`1`), `revWalk` (`(σ i).length + 1`),
`returnTape j` from `(σ i).length` (`(σ i).length + 2`); total at most
`5 * B + 8`. `revWalk_runsTo` leaves `i`'s head at `0`, so no return of
`i` is needed.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove** as the conventions say.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the reversing copy primitive

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9a: the loop machine and its body lifts (`Loop/Basic.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Loop.lean`
  (index)
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Loop/Basic.lean`
- Modify: `Machine.lean` (import `Machine.Loop`), `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2, 3a, 3b.
- Produces: `caseLoop R bodyF bodyT`, `liftBodyF`, `liftBodyT`,
  `liftBodyF_halt`, `liftBodyT_halt`, `caseLoop_step_bodyF`,
  `caseLoop_step_bodyT`, `caseLoop_configs_bodyF`,
  `caseLoop_configs_bodyT`, `caseLoop_outputString_bodyF`,
  `caseLoop_outputString_bodyT`, `Reaches.liftBodyF`, `Reaches.liftBodyT`.
  The four control-phase lemmas are Task 9a', in `Loop/Phases.lean`.

The loop reads the recursion word from register `R` holding its
reverse: the bit to process is `R`'s word's head, which is `R`'s last
cell. The control automaton, states `Fin 4`:

- state `0` (seek): `R` reads a bit: move `R` right; reads blank: move
  `R` left, go to `1`.
- state `1` (back): `R` reads blank (the register was empty and the head
  is at `-1`): move right and halt; reads bit `c`: write blank, move
  left, go to `2` if `c = false`, `3` if `c = true`.
- states `2`, `3` (return with the bit remembered): `R` reads a bit:
  move left; reads blank: move right and enter the body for the bit,
  in its initial state.
- body states: the body's transition, its halting successor replaced by
  state `0`.

- [ ] **Step 1: Write**

```lean
/-- The loop over register {lit}`R`: peel the head bit of {lit}`R`'s word
from its last cell, run the body for that bit, repeat; halt when {lit}`R` is
empty. -/
@[expose] def caseLoop {k : ℕ} {SF ST : Type} (R : Fin k) (bodyF : MultiTapeTM k Bool SF)
    (bodyT : MultiTapeTM k Bool ST) : MultiTapeTM k Bool (Fin 4 ⊕ (SF ⊕ ST)) where
  q₀ := .inl 0
  tr q inp work :=
    match q with
    | .inl ⟨0, _⟩ =>
      { inputMove := 0
        workActions := fun j ↦ (none, if j = R then (if (work R).isSome then 1 else -1) else 0)
        outS := none
        q' := some (.inl (if (work R).isSome then 0 else 1)) }
    | .inl ⟨1, _⟩ =>
      match work R with
      | none =>
        { inputMove := 0, workActions := fun j ↦ (none, if j = R then 1 else 0),
          outS := none, q' := none }
      | some c =>
        { inputMove := 0
          workActions := fun j ↦ if j = R then (some none, -1) else (none, 0)
          outS := none
          q' := some (.inl (if c then 3 else 2)) }
    | .inl ⟨2, _⟩ =>
      { inputMove := 0
        workActions := fun j ↦ (none, if j = R then (if (work R).isSome then -1 else 1) else 0)
        outS := none
        q' := some (if (work R).isSome then .inl 2 else .inr (.inl bodyF.q₀)) }
    | .inl ⟨3, _⟩ =>
      { inputMove := 0
        workActions := fun j ↦ (none, if j = R then (if (work R).isSome then -1 else 1) else 0)
        outS := none
        q' := some (if (work R).isSome then .inl 3 else .inr (.inr bodyT.q₀)) }
    | .inr (.inl q) => let o := bodyF.tr q inp work
      { o with q' := some (o.q'.elim (.inl 0) (fun q ↦ .inr (.inl q))) }
    | .inr (.inr q) => let o := bodyT.tr q inp work
      { o with q' := some (o.q'.elim (.inl 0) (fun q ↦ .inr (.inr q))) }

/-- A body configuration lifted into the loop: a halted one becomes the seek
state. -/
@[expose] def liftBodyF {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool SF input) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with state := some (cfg.state.elim (.inl 0) (fun q ↦ .inr (.inl q))) }

/-- As {lit}`liftBodyF`, for the body of the bit {lit}`true`. -/
@[expose] def liftBodyT {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool ST input) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with state := some (cfg.state.elim (.inl 0) (fun q ↦ .inr (.inr q))) }

/-- A halted body configuration lifts to the seek state. -/
theorem liftBodyF_halt {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool SF input)
    (h : cfg.state = none) :
    liftBodyF (ST := ST) cfg = { cfg with state := some (.inl 0) } := _

/-- As {lit}`liftBodyF_halt`, for the body of the bit {lit}`true`. -/
theorem liftBodyT_halt {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool ST input)
    (h : cfg.state = none) :
    liftBodyT (SF := SF) cfg = { cfg with state := some (.inl 0) } := _

/-- A step of the loop from a lifted live body configuration is the lift of
the body's step. -/
theorem caseLoop_step_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) (q : SF) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).step (liftBodyF (ST := ST) cfg) =
      liftBodyF (ST := ST) (bodyF.step cfg) := _

/-- As {lit}`caseLoop_step_bodyF`, for the body of the bit {lit}`true`. -/
theorem caseLoop_step_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) (q : ST) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).step (liftBodyT (SF := SF) cfg) =
      liftBodyT (SF := SF) (bodyT.step cfg) := _

/-- While the body has not halted, the loop mirrors it. -/
theorem caseLoop_configs_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) :
    ∀ t, (∀ t' < t, (bodyF.configs cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).configs (liftBodyF (ST := ST) cfg) t =
        liftBodyF (ST := ST) (bodyF.configs cfg t) := _

/-- As {lit}`caseLoop_configs_bodyF`, for the body of the bit {lit}`true`. -/
theorem caseLoop_configs_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) :
    ∀ t, (∀ t' < t, (bodyT.configs cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).configs (liftBodyT (SF := SF) cfg) t =
        liftBodyT (SF := SF) (bodyT.configs cfg t) := _

/-- While the body has not halted, the loop emits what the body emits. -/
theorem caseLoop_outputString_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) :
    ∀ t, (∀ t' < t, (bodyF.configs cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).outputString (liftBodyF (ST := ST) cfg) t =
        bodyF.outputString cfg t := _

/-- As {lit}`caseLoop_outputString_bodyF`, for the body of the bit
{lit}`true`. -/
theorem caseLoop_outputString_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) :
    ∀ t, (∀ t' < t, (bodyT.configs cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).outputString (liftBodyT (SF := SF) cfg) t =
        bodyT.outputString cfg t := _

/-- A reach of the body lifts to a reach of the loop. -/
theorem Reaches.liftBodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    {bodyF : MultiTapeTM k Bool SF} (bodyT : MultiTapeTM k Bool ST)
    {cfg cfg' : Cfg k Bool SF input} {t B : ℕ} (h : Reaches bodyF cfg cfg' t B) :
    Reaches (caseLoop R bodyF bodyT) (liftBodyF cfg) (liftBodyF cfg') t B := _

/-- As {lit}`Reaches.liftBodyF`, for the body of the bit {lit}`true`. -/
theorem Reaches.liftBodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) {bodyT : MultiTapeTM k Bool ST}
    {cfg cfg' : Cfg k Bool ST input} {t B : ℕ} (h : Reaches bodyT cfg cfg' t B) :
    Reaches (caseLoop R bodyF bodyT) (liftBodyT cfg) (liftBodyT cfg') t B := _
```

If the `match` on `.inl ⟨0, _⟩` does not elaborate, match on `.inl s`
and dispatch with `if s = 0 then ... else if s = 1 then ...`, as
`treeScanner` does with named `Fin 4` states.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

The `liftBody*_halt`, `caseLoop_step_body*`, `caseLoop_configs_body*`,
`caseLoop_outputString_body*` and `Reaches.liftBody*` lemmas follow the
proofs of their `Seq.lean` counterparts (`liftL_halt`, `seq_step_left`,
`seq_configs_left`, `seq_outputString_left`, `Reaches.liftL`) with the
`match` on the loop's state in place of `seq`'s.

- [ ] **Step 4: Write `Loop.lean`, allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the recursion loop machine and its body lifts

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9a': the loop's control phases (`Loop/Phases.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Loop/Phases.lean`
- Modify: `Loop.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Task 9a.
- Produces: `caseLoop_seek`, `caseLoop_back`, `caseLoop_ret`, `caseLoop_exit`.

- [ ] **Step 1: Write**

```lean
/-- The seek phase: from the seek state with {lit}`R` holding {lit}`c :: r`
and parked, {lit}`r.length + 2` steps reach the back state with {lit}`R`'s
head at cell {lit}`r.length`. -/
theorem caseLoop_seek {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (c : Bool) (r : List Bool) (hR : cfg.workTapes R = tapeOf (c :: r))
    (hp : cfg.workTapePos R = 0) (B : ℕ) (hB : r.length + 1 ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (r.length : ℤ) }
      (r.length + 2) B := _

/-- The back phase: from the back state with {lit}`R` holding {lit}`c :: r`
and its head at cell {lit}`r.length`, one step blanks that cell, so that
{lit}`R` holds {lit}`r`, moves left, and enters the return state for
{lit}`c`. -/
theorem caseLoop_back {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 1))
    (c : Bool) (r : List Bool) (hR : cfg.workTapes R = tapeOf (c :: r))
    (hp : cfg.workTapePos R = (r.length : ℤ)) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (.inl (if c then 3 else 2))
        workTapes := Function.update cfg.workTapes R (tapeOf r)
        workTapePos := Function.update cfg.workTapePos R ((r.length : ℤ) - 1) }
      1 B := _

/-- The return phase: from the return state for {lit}`c` with {lit}`R`
holding {lit}`r` and its head at cell {lit}`r.length - 1`,
{lit}`r.length + 1` steps park the head and enter the body for {lit}`c` in
its initial state. -/
theorem caseLoop_ret {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (c : Bool)
    (hq : cfg.state = some (.inl (if c then 3 else 2)))
    (r : List Bool) (hR : cfg.workTapes R = tapeOf r)
    (hp : cfg.workTapePos R = (r.length : ℤ) - 1) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (if c then .inr (.inr bodyT.q₀) else .inr (.inl bodyF.q₀))
        workTapePos := Function.update cfg.workTapePos R 0 }
      (r.length + 1) B := _

/-- The exit: from the seek state with {lit}`R` empty and parked, two steps
halt with every head where it was. -/
theorem caseLoop_exit {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (hR : cfg.workTapes R = tapeOf []) (hp : cfg.workTapePos R = 0) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (caseLoop R bodyF bodyT) cfg { cfg with state := none } 2 B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`caseLoop_seek`: family for `s ≤ r.length + 1`: state `.inl 0`, head of
`R` at `s`; the head reads a bit for `s ≤ r.length` (the word has length
`r.length + 1`, `tapeOf_of_lt`) and moves right; at `s = r.length + 1` it
reads `none` (`tapeOf_of_le`), moves left to `r.length` and the state
becomes `.inl 1`. Total `r.length + 2` steps.

`caseLoop_back`: one step by `step_of_state`; `R` reads
`some c` at cell `r.length` (`tapeOf_of_lt` and `List.reverse_cons` with
`List.getElem_append_right`, or directly `tapeOf_cons` and
`Function.update_self`); the write is `tapeOf_update_none`.

`caseLoop_ret`: family for `s ≤ r.length`: head of `R` at
`r.length - 1 - s`, state unchanged; at `s = r.length` the head is at
`-1`, reads `none`, moves right to `0`, and the state becomes the body's
start; `cases c` to resolve the `if`.

`caseLoop_exit`: two `configs_succ_eq_step'` rewrites and
`step_of_state`; the first step reads `none` at cell `0` (`tapeOf_nil`),
moves left to `-1`, state `.inl 1`; the second reads `none` at `-1`,
moves right to `0`, halts. `Cfg.ext` with `Function.update_idem` and
`Function.update_eq_self` for the head.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove the recursion loop's control phases

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9b: one iteration (`Loop/Iter.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Loop/Iter.lean`
- Modify: `Loop.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 9a and 9a'.
- Produces: `caseLoop_iter`.

- [ ] **Step 1: Write**

```lean
/-- The loop's one iteration: from the seek state, parked, holding a
valuation whose {lit}`R` is {lit}`c :: r`, the control peels {lit}`c`, runs the
body for {lit}`c` from its initial state on the valuation with {lit}`R` set
to {lit}`r`, and returns to the seek state, parked, holding the body's
transformed valuation. -/
theorem caseLoop_iter {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (FF FT : (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ)
    (hF : Transforms bodyF FF T B) (hT : Transforms bodyT FT T B)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (σ : Fin k → List Bool) (c : Bool) (r : List Bool) (hR : σ R = c :: r)
    (hpark : Parked cfg) (hσ : Holds cfg σ) (hB : Bounded σ B)
    (hb : Bounded ((if c then FT else FF) (Function.update σ R r)) B) :
    ∃ t ≤ T + 2 * r.length + 6,
      Reaches (caseLoop R bodyF bodyT) cfg
        { after cfg ((if c then FT else FF) (Function.update σ R r)) with
          state := some (.inl 0) } t B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`caseLoop_seek` (with `hR` from `hσ R` and `hR`, `hB R` for the length
bound) `.trans` `caseLoop_back` `.trans` `caseLoop_ret`, then `cases c`;
in each case the body's contract at the configuration `caseLoop_ret`
produces, restated as a body configuration `cfgb` with state the body's
`q₀` (it is parked, and holds `Function.update σ R r` by
`Function.update_apply` on the tapes: `R` holds `tapeOf r` from
`caseLoop_back`'s update and every other register holds `σ i` by `hσ`);
`Bounded (Function.update σ R r) B` from `hB` and `hR` (the length of
`r` is less than that of `c :: r`); the run lifts by `Reaches.liftBodyF`
or `Reaches.liftBodyT`, whose start `liftBodyF cfgb` is `caseLoop_ret`'s
target by `Cfg.ext` and whose end, by `liftBodyF_halt`, is the stated
configuration. The step count is `(r.length + 2) + 1 + (r.length + 1) + t`
with `t ≤ T`.

- [ ] **Step 4: Allowlist, import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove one iteration of the recursion loop

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9c: the loop's contract (`Loop/Transforms.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Loop/Transforms.lean`
- Modify: `Loop.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 9a, 9b.
- Produces: `loopF`, `loopF_nil`, `loopF_cons`, `loopF_bounded`,
  `Transforms.caseLoop`.

- [ ] **Step 1: Write**

```lean
/-- The valuation after the loop on the word {lit}`r`: for each bit of
{lit}`r` in order, set {lit}`R` to the rest and apply the body's transformer
for that bit. -/
@[expose] def loopF {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool) :
    List Bool → (Fin k → List Bool) → Fin k → List Bool :=
  List.rec (fun σ ↦ σ) (fun c r ih σ ↦ ih ((if c then FT else FF) (Function.update σ R r)))

/-- The loop on the empty word is the identity. -/
theorem loopF_nil {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) : loopF R FF FT [] σ = σ := rfl

/-- The loop on {lit}`c :: r` runs the body for {lit}`c` at {lit}`R = r`, then
the loop on {lit}`r`. -/
theorem loopF_cons {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (c : Bool) (r : List Bool) (σ : Fin k → List Bool) :
    loopF R FF FT (c :: r) σ = loopF R FF FT r ((if c then FT else FF) (Function.update σ R r)) :=
  rfl

/-- The loop's transformer preserves the bound when both bodies' do. -/
theorem loopF_bounded {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (B : ℕ) (hFb : ∀ σ, Bounded σ B → Bounded (FF σ) B)
    (hTb : ∀ σ, Bounded σ B → Bounded (FT σ) B) :
    ∀ (r : List Bool) (σ : Fin k → List Bool), r.length ≤ B → Bounded σ B →
      Bounded (loopF R FF FT r σ) B := _

/-- The loop transforms the valuation by {lit}`loopF` at the word on {lit}`R`,
within {lit}`B * (T + 2 * B + 6) + 3` steps, provided each body transforms
within {lit}`T`, keeps {lit}`R`, and keeps the bound. -/
theorem Transforms.caseLoop {k : ℕ} {SF ST : Type} (R : Fin k)
    {bodyF : MultiTapeTM k Bool SF} {bodyT : MultiTapeTM k Bool ST}
    {FF FT : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ}
    (hF : Transforms bodyF FF T B) (hT : Transforms bodyT FT T B)
    (hFR : ∀ σ, FF σ R = σ R) (hTR : ∀ σ, FT σ R = σ R)
    (hFb : ∀ σ, Bounded σ B → Bounded (FF σ) B) (hTb : ∀ σ, Bounded σ B → Bounded (FT σ) B) :
    Transforms (caseLoop R bodyF bodyT) (fun σ ↦ loopF R FF FT (σ R) σ)
      (B * (T + 2 * B + 6) + 3) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`loopF_bounded`: `List.rec` on `r` with `σ` generalized; the step is the
induction hypothesis at `(if c then FT else FF) (Function.update σ R r)`,
bounded by `hFb` / `hTb` (`cases c`) from `Bounded (Function.update σ R r) B`.

`Transforms.caseLoop`: first prove the auxiliary statement, by
`List.rec` on `r` with `cfg` and `σ` generalized:

```lean
∀ (r : List Bool) {input : List Bool} (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input)
    (σ : Fin k → List Bool), cfg.state = some (.inl 0) → σ R = r → Parked cfg → Holds cfg σ →
    Bounded σ B →
    ∃ t ≤ r.length * (T + 2 * B + 6) + 2,
      RunsTo (caseLoop R bodyF bodyT) cfg (after cfg (loopF R FF FT r σ)) t B
```

Base `[]`: `caseLoop_exit` with `hR := (hσ R).trans (by rw [hr])`; the
target `{ cfg with state := none }` is `after cfg σ` by `Cfg.ext` and
`hσ`. Step `c :: r`: `caseLoop_iter` with `hb` from `hFb` / `hTb` at
`Function.update σ R r` (`cases c`), then the induction hypothesis at the
iteration's target configuration and the valuation
`(if c then FT else FF) (Function.update σ R r)`, whose `R` is `r` by
`hFR` / `hTR` and `Function.update_self`, parked by `after_workTapePos`
and `hpark`, holding the valuation by `after_workTapes`; assemble the
run by
`Reaches.trans` and the halted clause of the inner run; the targets
agree by `Cfg.ext` (`after` of `after` with a state override); the
count by `List.length_cons`, then `rw [Nat.succ_mul]`, then `omega`,
since `omega` alone treats the two products as unrelated atoms.

Then the theorem: `intro _ cfg σ hq hpark hσ hB _`; apply the auxiliary
statement at `r := σ R`, and weaken the count by `hB R` and `omega`
(`Nat.mul_le_mul_right`).

- [ ] **Step 4: Allowlist, import, build, lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove the recursion loop's contract

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 10: plan exit check

- [ ] **Step 1: Confirm the fallback trigger did not fire**

The spec's § Fallback: the route is abandoned if the combinator proofs
need a closed-form configuration family per expression rather than per
primitive. At the end of Task 9c every family written is per phase
machine (`retLeft`, `walkEnd`, `blankLeft`, `copyWalk`, `revWalk`,
`sbsWalk`, `constWalk`, the loop's control phases), and `seq`,
`RunsTo.seq`, `Transforms.seq`, `Transforms.seqFin`, `caseLoop_iter` and
`Transforms.caseLoop` are generic. If any task required a family for a
composite, stop and report it as the trigger.

- [ ] **Step 2: Run the pre-push checklist**

Run: `scripts/pre-push.sh`
Expected: pass. Fix what it reports in a further commit.

- [ ] **Step 3: Report**

State which tasks are complete, the step-count bounds each contract
carries, the `step_of_state` duplicate, and any deviation from the plan,
for the user's review before plan 2 is written.
