/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Prototypes.Computability.MultiTape.RunFrom

set_option doc.verso true in
/-!
# The output emitted along a segment of a run

CSLib records a multi-tape machine's output on the configuration itself, as the field
{name}`Turing.Cfg.output` that each step extends by the symbol it emits. This module defines
the output a machine emits along a segment of a run, {lit}`outputString`: the concatenation of
the symbols emitted at each of the first {lit}`t` steps from a configuration, whatever that
configuration's own output tape holds. A machine built by composition is reasoned about
segment by segment, so the segment form is the one the prototypes' step lemmas state, and
{lit}`runFrom_output` relates it to the output tape. The symbol a single step emits,
{lit}`outputSymbol`, is read off the transition CSLib derives from the machine's transition
relation, which CSLib selects by choice, so it and every definition built on it are
noncomputable.

## Main definitions

* {lit}`Turing.MultiTapeTM.outputSymbol`: the symbol (optionally) emitted by one step.
* {lit}`Turing.MultiTapeTM.outputString`: the output emitted along the first {lit}`t` steps
  from a configuration.

## Main statements

* {lit}`Turing.MultiTapeTM.step_output`: one step appends the symbol it emits to the output
  tape.
* {lit}`Turing.MultiTapeTM.runFrom_output`: the output tape after {lit}`t` steps is the
  initial output tape followed by the output emitted along those steps.
* {lit}`Turing.MultiTapeTM.outputString_succ` and
  {lit}`Turing.MultiTapeTM.outputString_add_eq_append`: the emitted output composes along
  the run.
* {lit}`Turing.MultiTapeTM.outputString_halt` and
  {lit}`Turing.MultiTapeTM.outputString_eq_of_halt`: a halted machine emits nothing.

## Tags

Turing machine, output tape
-/

set_option doc.verso true

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The symbol (optionally) emitted by one step of {lit}`tm` from configuration {lit}`cfg`:
nothing from a halted configuration, and otherwise the output of the transition taken. -/
noncomputable def outputSymbol (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- A halted configuration emits nothing. -/
@[simp]
lemma outputSymbol_of_halt {tm : MultiTapeTM k Symbol State} {cfg : Cfg k Symbol State input}
    (h_halt : cfg.state = none) : tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  cases h : cfg.state with
  | none => simp [outputSymbol, h]
  | some q => simp [step_of_state h, outputSymbol, h, Action.apply]

/-- The string the machine {lit}`tm` emits starting in configuration {lit}`cfg₀` and
executing for {lit}`t` steps: the concatenation of the symbols (optionally) emitted at each of
the first {lit}`t` steps. -/
noncomputable def outputString (tm : MultiTapeTM k Symbol State)
    (cfg₀ : Cfg k Symbol State input) (t : ℕ) : List Symbol :=
  (List.range t).flatMap fun t' ↦ (tm.outputSymbol (tm.runFrom cfg₀ t')).toList

/-- The output emitted in {lit}`t + 1` steps is the output emitted in {lit}`t` steps followed
by the symbol (optionally) emitted at step {lit}`t`. -/
lemma outputString_succ (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (t : ℕ) :
    tm.outputString cfg (t + 1) =
      tm.outputString cfg t ++ (tm.outputSymbol (tm.runFrom cfg t)).toList := by
  simp [outputString, List.range_succ, List.flatMap_append]

/-- From a halting configuration, a machine emits nothing. -/
lemma outputString_halt (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (h_halt : cfg.state = none) (t : ℕ) :
    tm.outputString cfg t = [] := by
  refine Nat.rec (by simp [outputString]) (fun t ih ↦ ?_) t
  simp [outputString_succ, ih, h_halt]

/-- The output emitted in {lit}`t₁ + t₂` steps is the output emitted in the first {lit}`t₁`
steps followed by the output emitted in the next {lit}`t₂`. -/
lemma outputString_add_eq_append (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t₁ t₂ : ℕ) :
    tm.outputString cfg (t₁ + t₂) =
      tm.outputString cfg t₁ ++ tm.outputString (tm.runFrom cfg t₁) t₂ := by
  refine Nat.rec (by simp [outputString]) (fun t ih ↦ ?_) t₂
  rw [show t₁ + (t + 1) = (t₁ + t) + 1 by omega]
  simp [outputString_succ, ih, runFrom, ← Function.iterate_add_apply, Nat.add_comm]

/-- The emitted output does not change after the machine has halted. -/
lemma outputString_eq_of_halt (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.outputString cfg t = tm.outputString cfg τ := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [outputString_add_eq_append, outputString_halt _ _ hhalt]
  simp

/-- The output tape after {lit}`t` steps is the initial output tape followed by the output
emitted along those steps. -/
lemma runFrom_output (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (t : ℕ) :
    (tm.runFrom cfg t).output = cfg.output ++ tm.outputString cfg t := by
  refine Nat.rec (by simp [outputString]) (fun t ih ↦ ?_) t
  rw [runFrom_succ_eq_step', step_output, ih, outputString_succ, List.append_assoc]

/-- From the initial configuration, whose output tape is empty, the output tape after
{lit}`t` steps is the emitted output. -/
lemma initCfg_runFrom_output (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    (tm.runFrom (tm.initCfg input) t).output = tm.outputString (tm.initCfg input) t := by
  rw [runFrom_output]
  rfl

end Turing.MultiTapeTM
