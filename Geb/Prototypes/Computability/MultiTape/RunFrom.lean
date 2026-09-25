/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

set_option doc.verso true in
/-!
# Iteration equations for the runs of a multi-tape machine

CSLib defines the configuration {name}`Turing.MultiTapeTM.runFrom` reaches after {lit}`t` steps
as the {lit}`t`-fold iterate of {name}`Turing.MultiTapeTM.step`, whose laws are mathlib's lemmas
on {name}`Nat.iterate`. This module states those laws at {name}`Turing.MultiTapeTM.runFrom`, so
that a proof rewriting along a run matches hypotheses stated about
{name}`Turing.MultiTapeTM.runFrom` without unfolding it.

## Main statements

* {lit}`Turing.MultiTapeTM.runFrom_zero`, {lit}`Turing.MultiTapeTM.runFrom_succ_eq_step`,
  {lit}`Turing.MultiTapeTM.runFrom_succ_eq_step'` and {lit}`Turing.MultiTapeTM.runFrom_add`:
  the iterate laws.
* {lit}`Turing.MultiTapeTM.runFrom_comm_of_step`: a map of configurations commuting with the
  steps of two machines commutes with their runs.
* {lit}`Turing.MultiTapeTM.runFrom_of_halt`: a run from a halted configuration stays there.

## Tags

Turing machine, iteration
-/

set_option doc.verso true

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol} {tm : MultiTapeTM k Symbol State}

/-- A run of no steps stays at its configuration. -/
@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} : tm.runFrom cfg 0 = cfg :=
  Function.iterate_zero_apply tm.step cfg

/-- A run of {lit}`t + 1` steps is a run of {lit}`t` steps from the configuration one step
later. -/
lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t :=
  Function.iterate_succ_apply tm.step t cfg

/-- A run of {lit}`t + 1` steps is one step after a run of {lit}`t` steps. -/
lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) :=
  Function.iterate_succ_apply' tm.step t cfg

/-- A run of {lit}`a + b` steps is a run of {lit}`b` steps from the configuration reached after
{lit}`a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply tm.step b a cfg

/-- A map {lit}`f` of configurations that commutes with the steps of two machines commutes
with their runs. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c ↦ (hstep c).symm) n cfg).symm

/-- A run from a halted configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

end Turing.MultiTapeTM
