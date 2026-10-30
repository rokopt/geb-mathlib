/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.Lemma

set_option doc.verso true in
/-!
# Resource bounds from a halted deterministic run

CSLib states the time and space bounds of a computation over the computation paths of a
machine's transition relation: {name}`Turing.MultiTapeNTM.RunsInTime` bounds the length after
which every path has halted, and {name}`Turing.MultiTapeNTM.RunsInSpace` bounds the work-tape
cells every path visits, whatever its length. A deterministic machine has one path of each
length, the iterate of {name}`Turing.MultiTapeTM.step`, and a path continued past the
machine's halt repeats the halted configuration and visits no further cell. So a single run
that has halted bounds both: its length the time, and the number of cells it visited,
{name}`Turing.MultiTapeNTM.RunPath.space`, the space. CSLib states the bound on time,
{name}`Turing.MultiTapeTM.runsInTime_of_halted`; this module states the bound on space and the
resulting computation.

## Main statements

* {lit}`Turing.MultiTapeTM.space_eq_sum`: the space of a run is the sum over the work tapes of
  the cells each head visits.
* {lit}`Turing.MultiTapeTM.visitedByTapeHead_subset_of_halted`: once a run has halted, a
  run of any length visits no cell the halted run did not.
* {lit}`Turing.MultiTapeTM.runsInSpace_of_halted`: a halted run bounds the space of every
  computation path.
* {lit}`Turing.MultiTapeTM.computesInTimeAndSpace_iff`: a deterministic machine computes an
  output within time {lit}`t` and space {lit}`s` exactly when its run of {lit}`t` steps has
  halted with that output, having visited at most {lit}`s` work-tape cells.
* {lit}`Turing.MultiTapeTM.computesInTimeAndSpace_of_halted`: a run halted within the time
  bound, with the given output and within the space bound, is a computation within those
  bounds.

## Tags

Turing machine, time complexity, space complexity
-/

set_option doc.verso true

@[expose] public section

namespace Turing.MultiTapeTM

open MultiTapeNTM (RunPath)

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol} {tm : MultiTapeTM k Symbol State}

/-- The space of the first {lit}`t` steps from {lit}`cfg` is the sum over the work tapes of the
cells each head visits. -/
lemma space_eq_sum (cfg : Cfg k Symbol State input) (t : ℕ) :
    (RunPath.ofDeterministic tm cfg t).space =
      ∑ i, (RunPath.ofDeterministic tm cfg t).spaceUsedByTape i :=
  rfl

/-- Once the run from {lit}`cfg` has halted after {lit}`t` steps, a run of any length from
{lit}`cfg` visits only cells the first {lit}`t` steps visited. -/
lemma visitedByTapeHead_subset_of_halted {cfg : Cfg k Symbol State input} {t : ℕ}
    (hhalt : (tm.runFrom cfg t).Halted) (T : ℕ) (i : Fin k) :
    (RunPath.ofDeterministic tm cfg T).visitedByTapeHead i ⊆
      (RunPath.ofDeterministic tm cfg t).visitedByTapeHead i := by
  intro z hz
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ?_
  by_cases hn : (n : ℕ) ≤ t
  · exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, Finset.mem_univ _, rfl⟩
  · exact ⟨Fin.last t, Finset.mem_univ _,
      congrArg (fun c ↦ c.workTapePos i)
        (runFrom_eq_of_halt tm cfg (Nat.le_of_not_le hn) hhalt).symm⟩

/-- A run from the initial configuration that has halted after {lit}`t` steps having visited
at most {lit}`s` work-tape cells bounds the space of every computation path by {lit}`s`. -/
lemma runsInSpace_of_halted {t s : ℕ} (hhalt : (tm.runFrom (tm.initCfg input) t).Halted)
    (hs : (RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s) :
    tm.RunsInSpace input s := by
  intro p
  rw [p.eq_ofDeterministic]
  refine le_trans (?_ : (RunPath.ofDeterministic tm (tm.initCfg input) p.time).space ≤ _) hs
  exact Finset.sum_le_sum fun i _ ↦
    Finset.card_le_card (visitedByTapeHead_subset_of_halted hhalt p.time i)

/-- A run from the initial configuration that has halted after {lit}`t'` steps, with output
{lit}`output`, having visited {lit}`s'` work-tape cells, computes {lit}`output` within every
time bound at least {lit}`t'` and every space bound at least {lit}`s'`. -/
theorem computesInTimeAndSpace_of_halted {output : List Symbol} {t' t s' s : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg input) t').Halted)
    (hout : (tm.runFrom (tm.initCfg input) t').output = output)
    (hspace : (RunPath.ofDeterministic tm (tm.initCfg input) t').space = s')
    (ht : t' ≤ t) (hs : s' ≤ s) :
    tm.ComputesInTimeAndSpace input output t s :=
  ⟨⟨t', hhalt, hout⟩, (runsInTime_of_halted hhalt).mono ht,
    runsInSpace_of_halted hhalt (hspace ▸ hs)⟩

/-- A deterministic machine computes {lit}`output` from {lit}`input` within time {lit}`t` and
space {lit}`s` exactly when its run of {lit}`t` steps from the initial configuration has halted
with output {lit}`output`, having visited at most {lit}`s` work-tape cells. -/
theorem computesInTimeAndSpace_iff {output : List Symbol} {t s : ℕ} :
    tm.ComputesInTimeAndSpace input output t s ↔
      (tm.runFrom (tm.initCfg input) t).Halted ∧
        (tm.runFrom (tm.initCfg input) t).output = output ∧
        (RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s := by
  refine ⟨fun ⟨⟨u, hu, hout⟩, htime, hspace⟩ ↦ ?_,
    fun ⟨hhalt, hout, hs⟩ ↦ computesInTimeAndSpace_of_halted hhalt hout rfl le_rfl hs⟩
  let p := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hhalt : (tm.runFrom (tm.initCfg input) t).Halted :=
    computationPath_last_eq_runFrom p ▸ htime p le_rfl
  refine ⟨hhalt, ?_, hspace p⟩
  rcases Nat.le_total u t with hut | htu
  · rw [runFrom_eq_of_halt tm _ hut hu, hout]
  · rw [← runFrom_eq_of_halt tm _ htu hhalt, hout]

end Turing.MultiTapeTM
