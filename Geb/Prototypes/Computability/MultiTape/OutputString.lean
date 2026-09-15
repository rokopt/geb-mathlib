/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

set_option doc.verso true in
/-!
# The output emitted along a segment of a run

CSLib records a multi-tape machine's output on the configuration itself, as the field
{name}`Turing.Cfg.output` that each step extends by the symbol it emits. This module defines
the output a machine emits along a segment of a run, {lit}`outputString`: the concatenation of
the symbols emitted at each of the first {lit}`t` steps from a configuration, whatever that
configuration's own output tape holds. A machine built by composition is reasoned about
segment by segment, so the segment form is the one the prototypes' step lemmas state, and
{lit}`runFrom_output` relates it to the output tape.

## Main definitions

* {lit}`Turing.MultiTapeTM.outputString`: the output emitted along the first {lit}`t` steps
  from a configuration.

## Main statements

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

/-- The string the machine {lit}`tm` emits starting in configuration {lit}`cfg₀` and
executing for {lit}`t` steps: the concatenation of the symbols (optionally) emitted at each of
the first {lit}`t` steps. -/
def outputString (tm : MultiTapeTM k Symbol State) (cfg₀ : Cfg k Symbol State input)
    (t : ℕ) : List Symbol :=
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
