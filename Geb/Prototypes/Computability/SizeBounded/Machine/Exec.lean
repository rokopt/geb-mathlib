/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Std.Data.HashMap.Lemmas
import Geb.Prototypes.Computability.SizeBounded.Machine.Program

set_option doc.verso true

/-!
# An executable configuration

A {name}`Turing.MultiTapeTM.Cfg` carries its work tapes and head positions as
functions, so {name}`Turing.MultiTapeTM.step` builds each successor's fields as
closures over its predecessor's: reading one cell after {lit}`t` steps re-enters
the transition function at each of the {lit}`t` earlier configurations, and the
cost of an iteration is exponential in the step count. An executable
configuration holds each tape as a {name}`Std.HashMap` from cells to bits, blank
where absent, and the heads as a {name}`Vector`, and computes every field once
per step, so the cost of an iteration is linear in the step count.

{lit}`toCfg` sends an executable configuration to the configuration it denotes,
{lit}`toCfg_execStep` and {lit}`toCfg_execStep_iterate` say that the executable
step and its iterates denote {name}`Turing.MultiTapeTM.step` and
{name}`Turing.MultiTapeTM.configs`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its statements
mention {name}`Turing.MultiTapeTM.step`, which depends on {lit}`Classical.choice`
through {name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`ExecCfg` — a configuration with materialized tapes and heads.
* {lit}`ExecCfg.toCfg` — the configuration it denotes.
* {lit}`ExecCfg.init` — the initial executable configuration.
* {lit}`writeCell` — a tape after one action at a cell.
* {lit}`execStep`, {lit}`execOutputSymbol` — one step and the symbol it emits.

# Main statements

* {lit}`toCfg_init` — the initial executable configuration denotes the initial
  configuration.
* {lit}`toCfg_execStep`, {lit}`toCfg_execStep_iterate` — the executable step and
  its iterates denote the step and the configurations.
* {lit}`execOutputSymbol_eq` — the emitted symbol is the denoted one.

# Tags

Turing machine, configuration, execution, hash map
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- A configuration with materialized tapes: each tape a finite map from cells
to bits, blank where absent, the heads a vector. -/
structure ExecCfg (k : ℕ) (State : Type) (input : List Bool) where
  /-- The state, {lit}`none` when halted. -/
  state : Option State
  /-- The input head's position, shifted by one as in {name}`Turing.MultiTapeTM.Cfg`. -/
  inputPos : Fin (input.length + 2)
  /-- The tapes. -/
  tapes : Vector (Std.HashMap ℤ Bool) k
  /-- The heads. -/
  heads : Vector ℤ k

/-- The configuration an executable configuration denotes. -/
@[expose] def ExecCfg.toCfg {k : ℕ} {State : Type} {input : List Bool}
    (c : ExecCfg k State input) : Cfg k Bool State input :=
  { state := c.state
    inputPos := c.inputPos
    workTapes := fun i z ↦ c.tapes[i][z]?
    workTapePos := fun i ↦ c.heads[i] }

/-- The initial executable configuration: blank tapes, parked heads. -/
@[expose] def ExecCfg.init {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (input : List Bool) : ExecCfg k State input :=
  ⟨some tm.q₀, 1, Vector.replicate k ∅, Vector.replicate k 0⟩

/-- A tape after one action at a cell: unchanged, erased, or written. -/
@[expose] def writeCell (tape : Std.HashMap ℤ Bool) (z : ℤ) :
    Option (Option Bool) → Std.HashMap ℤ Bool
  | none => tape
  | some none => tape.erase z
  | some (some b) => tape.insert z b

/-- One step, with every field computed once. -/
@[expose] def execStep {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (c : ExecCfg k State input) : ExecCfg k State input :=
  match c.state with
  | none => c
  | some q =>
    let o := tm.tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols
    { state := o.q'
      inputPos := moveInputPos c.inputPos o.inputMove
      tapes := Vector.ofFn fun i ↦ writeCell c.tapes[i] c.heads[i] (o.workActions i).1
      heads := Vector.ofFn fun i ↦ c.heads[i] + (o.workActions i).2 }

/-- The symbol emitted by one step. -/
@[expose] def execOutputSymbol {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) : Option Bool :=
  match c.state with
  | none => none
  | some q => (tm.tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols).outS

/-- A cell of a tape after a writing action: the tape's cell map, updated. -/
theorem getElem?_writeCell (tape : Std.HashMap ℤ Bool) (y z : ℤ) (s : Option Bool) :
    (writeCell tape y (some s))[z]? = Function.update (fun w ↦ tape[w]?) y s z := by
  rw [Function.update_apply]
  cases s with
  | none =>
    simp only [writeCell, Std.HashMap.getElem?_erase]
    by_cases hz : z = y
    · subst hz
      simp
    · have hzy : y ≠ z := fun h ↦ hz h.symm
      simp [hz, hzy]
  | some b =>
    simp only [writeCell, Std.HashMap.getElem?_insert]
    by_cases hz : z = y
    · subst hz
      simp
    · have hzy : y ≠ z := fun h ↦ hz h.symm
      simp [hz, hzy]

/-- The initial executable configuration denotes the initial configuration. -/
theorem toCfg_init {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) (input : List Bool) :
    (ExecCfg.init tm input).toCfg = tm.initCfg input := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i z
    simp only [ExecCfg.toCfg, ExecCfg.init, Fin.getElem_fin, Vector.getElem_replicate,
      Std.HashMap.getElem?_empty, initCfg]
  · funext i
    simp only [ExecCfg.toCfg, ExecCfg.init, Fin.getElem_fin, Vector.getElem_replicate, initCfg]

/-- One executable step denotes one step. -/
theorem toCfg_execStep {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (c : ExecCfg k State input) : (execStep tm c).toCfg = tm.step c.toCfg := by
  cases hq : c.state with
  | none =>
    rw [step_of_halt (cfg := c.toCfg) hq]
    unfold execStep
    rw [hq]
  | some q =>
    rw [step_of_state tm c.toCfg q hq]
    simp only [execStep, hq]
    set o := tm.tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols
    apply Cfg.ext
    · rfl
    · rfl
    · funext i z
      simp only [ExecCfg.toCfg, Fin.getElem_fin, Vector.getElem_ofFn]
      cases (o.workActions i).1 with
      | none => rfl
      | some s => exact getElem?_writeCell c.tapes[i] c.heads[i] z s
    · funext i
      simp only [ExecCfg.toCfg, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The emitted symbol is the denoted configuration's. -/
theorem execOutputSymbol_eq {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) :
    execOutputSymbol tm c = tm.outputSymbol c.toCfg := by
  cases hq : c.state with
  | none => simp only [execOutputSymbol, outputSymbol, ExecCfg.toCfg, hq]
  | some q => simp only [execOutputSymbol, outputSymbol, ExecCfg.toCfg, hq]

/-- Iterated executable steps denote the configurations. -/
theorem toCfg_execStep_iterate {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) :
    ∀ t : ℕ, ((execStep tm)^[t] c).toCfg = tm.configs c.toCfg t :=
  Nat.rec rfl fun t ih ↦ by
    rw [Function.iterate_succ_apply', toCfg_execStep, ih, configs_succ_eq_step']

end

end Geb.SizeBounded.Machine
