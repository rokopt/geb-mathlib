/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Prototypes.Computability.MultiTape.OfTr
public import Geb.Prototypes.Computability.MultiTape.OutputString
import all Init.Data.Nat.Control
import Std.Data.HashMap.Lemmas

set_option doc.verso true in
/-!
# An executable configuration

A {name}`Turing.Cfg` carries its work tapes and head positions as
functions, so a step builds each successor's fields as closures over its
predecessor's: reading one cell after {lit}`t` steps re-enters the transition
function at each of the {lit}`t` earlier configurations, and the cost of an
iteration is exponential in the step count. An executable configuration holds
each tape as a {name}`Std.HashMap` from cells to bits, blank where absent, the
heads as a {name}`Vector`, and the output tape reversed, so that a step extends it
at the front, and computes every field once per step, so the cost of an
iteration is linear in the step count.

The executable step is driven by a transition function rather than by a machine:
CSLib selects a machine's transition {name}`Turing.MultiTapeTM.tr` by choice, so
it does not evaluate, while a transition function built from computable
transitions does. {lit}`toCfg` sends an executable configuration to the
configuration it denotes; {lit}`toCfg_execStep` and
{lit}`toCfg_execStep_iterate` say that the executable step and its iterates
denote the step {name}`Turing.MultiTapeTM.stepOfTr` and its iterates, and
{lit}`toCfg_execStep_iterate_eq_runFrom` that they denote the run of any machine
whose transition agrees with the function.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its statements
mention {name}`Turing.MultiTapeTM.runFrom` and {name}`Turing.MultiTapeTM.tr`,
which depend on {lit}`Classical.choice`.

# Main definitions

* {lit}`ExecCfg` — a configuration with materialized tapes and heads.
* {lit}`ExecCfg.toCfg` — the configuration it denotes.
* {lit}`ExecCfg.init` — the initial executable configuration in a given state.
* {lit}`writeCell` — a tape after one action at a cell.
* {lit}`execStep`, {lit}`execOutputSymbol` — one step by a transition function
  and the symbol it emits.
* {lit}`stepUntilHalt` — the run to a halt within a fuel, with its output.
* {lit}`stepUntilHaltTR` — a bounded fold that stops when the run halts.

# Main statements

* {lit}`toCfg_init` — the initial executable configuration denotes the initial
  configuration.
* {lit}`toCfg_execStep`, {lit}`toCfg_execStep_iterate` — the executable step and
  its iterates denote {name}`Turing.MultiTapeTM.stepOfTr` and its iterates.
* {lit}`toCfg_execStep_iterate_eq_runFrom` — the iterates denote the run of a
  machine whose transition agrees with the transition function.
* {lit}`execOutputSymbol_eq`, {lit}`outputSymbol_eq_execOutputSymbol` — the
  emitted symbol is the one the denoted configuration selects, and the one a
  machine whose transition agrees with the function emits.
* {lit}`stepUntilHalt_eq_stepUntilHaltTR` — the compiler's replacement of the
  fuel recursor by the bounded fold preserves its value.

# Tags

Turing machine, configuration, execution, hash map
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- A configuration with materialized tapes: each tape a finite map from cells
to bits, blank where absent, the heads a vector. -/
structure ExecCfg (k : ℕ) (State : Type) (input : List Bool) where
  /-- The state, {lit}`none` when halted. -/
  state : Option State
  /-- The input head's position, shifted by one as in {name}`Turing.Cfg`. -/
  inputPos : Fin (input.length + 2)
  /-- The tapes. -/
  tapes : Vector (Std.HashMap ℤ Bool) k
  /-- The heads. -/
  heads : Vector ℤ k
  /-- The output tape, reversed. -/
  outputRev : List Bool

/-- The configuration an executable configuration denotes. -/
@[expose] def ExecCfg.toCfg {k : ℕ} {State : Type} {input : List Bool}
    (c : ExecCfg k State input) : Cfg k Bool State input :=
  { state := c.state
    inputPos := c.inputPos
    workTapes := fun i z ↦ c.tapes[i][z]?
    workTapePos := fun i ↦ c.heads[i]
    output := c.outputRev.reverse }

/-- The initial executable configuration in the state {lit}`q₀`: blank tapes,
parked heads. -/
@[expose] def ExecCfg.init {k : ℕ} {State : Type} (q₀ : State) (input : List Bool) :
    ExecCfg k State input :=
  ⟨some q₀, 1, Vector.replicate k ∅, Vector.replicate k 0, []⟩

/-- A tape after one action at a cell: unchanged, erased, or written. -/
@[expose] def writeCell (tape : Std.HashMap ℤ Bool) (z : ℤ) :
    Option (Option Bool) → Std.HashMap ℤ Bool
  | none => tape
  | some none => tape.erase z
  | some (some b) => tape.insert z b

/-- One step by the transition function {lit}`tr`, with every field computed
once. -/
@[expose] def execStep {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State)
    (c : ExecCfg k State input) : ExecCfg k State input :=
  match c.state with
  | none => c
  | some q =>
    let o := tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols
    { state := o.state
      inputPos := moveInputPos c.inputPos o.inputTape
      tapes := Vector.ofFn fun i ↦ writeCell c.tapes[i] c.heads[i] (o.workTapes i).1
      heads := Vector.ofFn fun i ↦ c.heads[i] + (o.workTapes i).2
      outputRev := o.output.toList.reverse ++ c.outputRev }

/-- The symbol emitted by one step by the transition function {lit}`tr`. -/
@[expose] def execOutputSymbol {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State)
    (c : ExecCfg k State input) : Option Bool :=
  match c.state with
  | none => none
  | some q => (tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols).output

/-- Step by the transition function {lit}`tr` until halted, collecting the output
in reverse; {lit}`none` when the fuel runs out first. -/
@[expose] def stepUntilHalt {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State) :
    ℕ → ExecCfg k State input → List Bool → Option (List Bool) :=
  Nat.rec (fun _ _ ↦ none) fun _ ih c acc ↦
    match c.state with
    | none => some acc.reverse
    | some _ => ih (execStep tr c) ((execOutputSymbol tr c).toList.reverse ++ acc)

/-- A bounded fold that stops at the first halted configuration without
allocating a continuation for unused fuel. -/
@[expose] def stepUntilHaltTR {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State) (fuel : ℕ)
    (c : ExecCfg k State input) (acc : List Bool) : Option (List Bool) :=
  match Nat.foldM (m := Except (List Bool)) fuel (fun _ _ (c, acc) ↦
      match c.state with
      | none => .error acc.reverse
      | some _ => .ok (execStep tr c, (execOutputSymbol tr c).toList.reverse ++ acc))
      (c, acc) with
  | .error output => some output
  | .ok _ => none

/-- The bounded fold implements the fuel recursor. -/
@[csimp] theorem stepUntilHalt_eq_stepUntilHaltTR : @stepUntilHalt = @stepUntilHaltTR := by
  funext k State input tr fuel c acc
  unfold stepUntilHaltTR Nat.foldM
  have loop : ∀ n (h : n ≤ fuel) (c : ExecCfg k State input) (acc : List Bool),
      stepUntilHalt tr n c acc =
        match Nat.foldM.loop fuel (fun _ _ (c, acc) ↦
            match c.state with
            | none => Except.error acc.reverse
            | some _ => Except.ok
                (execStep tr c, (execOutputSymbol tr c).toList.reverse ++ acc)) n h (c, acc) with
        | .error output => some output
        | .ok _ => none := by
    refine Nat.rec (fun _ _ _ ↦ rfl) ?_
    intro n ih h c acc
    cases hs : c.state with
    | none => simp [stepUntilHalt, Nat.foldM.loop, hs, bind, Except.bind]
    | some q =>
      simpa [stepUntilHalt, Nat.foldM.loop, hs, bind, Except.bind] using
        ih (Nat.le_of_succ_le h) (execStep tr c)
          ((execOutputSymbol tr c).toList.reverse ++ acc)
  exact loop fuel (Nat.le_refl _) c acc

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

/-- The initial executable configuration in the state {lit}`q₀` denotes the initial
configuration in that state. -/
theorem toCfg_init {k : ℕ} {State : Type} (q₀ : State) (input : List Bool) :
    (ExecCfg.init (k := k) q₀ input).toCfg = Cfg.init q₀ input := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i z
    simp only [ExecCfg.toCfg, ExecCfg.init, Fin.getElem_fin, Vector.getElem_replicate,
      Std.HashMap.getElem?_empty, Cfg.init]
  · funext i
    simp only [ExecCfg.toCfg, ExecCfg.init, Fin.getElem_fin, Vector.getElem_replicate, Cfg.init]
  · rfl

/-- One executable step denotes one step by {name}`Turing.MultiTapeTM.stepOfTr`. -/
theorem toCfg_execStep {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State)
    (c : ExecCfg k State input) : (execStep tr c).toCfg = stepOfTr tr c.toCfg := by
  have hq' : c.toCfg.state = c.state := rfl
  unfold execStep stepOfTr
  cases hq : c.state with
  | none => simp only [hq', hq]
  | some q =>
    simp only [hq', hq]
    unfold Action.apply
    set o := tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols
    apply Cfg.ext
    · rfl
    · rfl
    · funext i z
      simp only [ExecCfg.toCfg, Fin.getElem_fin, Vector.getElem_ofFn]
      cases (o.workTapes i).1 with
      | none => rfl
      | some s => exact getElem?_writeCell c.tapes[i] c.heads[i] z s
    · funext i
      simp only [ExecCfg.toCfg, Fin.getElem_fin, Vector.getElem_ofFn]
    · simp only [ExecCfg.toCfg, List.reverse_append, List.reverse_reverse]

/-- The emitted symbol is the one the denoted configuration's state and symbols
select. -/
theorem execOutputSymbol_eq {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State)
    (c : ExecCfg k State input) :
    execOutputSymbol tr c = match c.toCfg.state with
      | none => none
      | some q => (tr q c.toCfg.inputSymbol c.toCfg.workTapeSymbols).output := rfl

/-- A machine whose transition agrees with {lit}`tr` emits, from the denoted
configuration, the symbol an executable step emits. -/
theorem outputSymbol_eq_execOutputSymbol {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State}
    {tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State}
    (h : ∀ q inp work, tm.tr q inp work = tr q inp work) (c : ExecCfg k State input) :
    tm.outputSymbol c.toCfg = execOutputSymbol tr c := by
  have hq' : c.toCfg.state = c.state := rfl
  unfold outputSymbol execOutputSymbol
  cases hq : c.state with
  | none => simp only [hq', hq]
  | some q =>
    simp only [hq', hq]
    exact congrArg Action.output (h q _ _)

/-- Iterated executable steps denote the iterates of
{name}`Turing.MultiTapeTM.stepOfTr`. -/
theorem toCfg_execStep_iterate {k : ℕ} {State : Type} {input : List Bool}
    (tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State)
    (c : ExecCfg k State input) :
    ∀ t : ℕ, ((execStep tr)^[t] c).toCfg = (stepOfTr tr)^[t] c.toCfg :=
  Nat.rec rfl fun t ih ↦ by
    rw [Function.iterate_succ_apply', toCfg_execStep, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- Iterated executable steps denote the run of a machine whose transition agrees
with {lit}`tr`. -/
theorem toCfg_execStep_iterate_eq_runFrom {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State}
    {tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State}
    (h : ∀ q inp work, tm.tr q inp work = tr q inp work) (c : ExecCfg k State input) (t : ℕ) :
    ((execStep tr)^[t] c).toCfg = tm.runFrom c.toCfg t := by
  rw [toCfg_execStep_iterate, runFrom_eq_stepOfTr h]

end

end Geb.SizeBounded.Machine
