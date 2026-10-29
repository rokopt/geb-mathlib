/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Tactic.TypeStar

set_option doc.verso true in
/-!
# The runs of a machine given by its transition function

CSLib defines a deterministic machine by a transition relation and the proof that the relation
is the graph of a function. It recovers the function, {name}`Turing.MultiTapeTM.tr`, and from
it the step {name}`Turing.MultiTapeTM.step`, by choice, so neither reduces, and a run cannot be
evaluated. A machine built by {name}`Turing.MultiTapeTM.ofTr` from a transition function has a
step given by that function, {lit}`stepOfTr`, which reduces wherever the function does. This
module states that it is the step of every machine whose transition agrees with the function,
the machine {lit}`ofTr q₀ tr` among them, so that a run of such a machine is evaluated
through that function.

## Main definitions

* {lit}`Turing.MultiTapeTM.stepOfTr`: the step a transition function determines.

## Main statements

* {lit}`Turing.MultiTapeTM.step_eq_stepOfTr`, {lit}`Turing.MultiTapeTM.runFrom_eq_stepOfTr`: a
  machine whose transition agrees with {lit}`tr` steps, and runs, by {lit}`stepOfTr tr`.
* {lit}`Turing.MultiTapeTM.step_ofTr`: the step of {lit}`ofTr q₀ tr` is {lit}`stepOfTr tr`.
* {lit}`Turing.MultiTapeTM.runFrom_ofTr`: a run of {lit}`ofTr q₀ tr` is an iterate of
  {lit}`stepOfTr tr`.

## Tags

Turing machine, transition function, evaluation
-/

set_option doc.verso true

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The step the transition function {lit}`tr` determines: a halted configuration is fixed,
and a live one takes the action {lit}`tr` assigns to its state and the symbols it reads. -/
def stepOfTr (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- A machine whose transition agrees with {lit}`tr` steps by the step {lit}`tr` determines. -/
theorem step_eq_stepOfTr {tm : MultiTapeTM k Symbol State}
    {tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State}
    (h : ∀ q input work, tm.tr q input work = tr q input work)
    (cfg : Cfg k Symbol State input) : tm.step cfg = stepOfTr tr cfg := by
  cases hq : cfg.state with
  | none => rw [step_of_halt hq, stepOfTr, hq]
  | some q => rw [step_of_state hq, h, stepOfTr, hq]

/-- A run of a machine whose transition agrees with {lit}`tr` iterates the step {lit}`tr`
determines. -/
theorem runFrom_eq_stepOfTr {tm : MultiTapeTM k Symbol State}
    {tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State}
    (h : ∀ q input work, tm.tr q input work = tr q input work)
    (cfg : Cfg k Symbol State input) (t : ℕ) : tm.runFrom cfg t = (stepOfTr tr)^[t] cfg := by
  unfold runFrom
  rw [show tm.step = stepOfTr (input := input) tr from funext (step_eq_stepOfTr h)]

/-- The step of the machine built from {lit}`tr` is the step {lit}`tr` determines. -/
theorem step_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : (ofTr q₀ tr).step cfg = stepOfTr tr cfg :=
  step_eq_stepOfTr (tr_ofTr q₀ tr) cfg

/-- A run of the machine built from {lit}`tr` iterates the step {lit}`tr` determines. -/
theorem runFrom_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofTr q₀ tr).runFrom cfg t = (stepOfTr tr)^[t] cfg :=
  runFrom_eq_stepOfTr (tr_ofTr q₀ tr) cfg t

end Turing.MultiTapeTM
