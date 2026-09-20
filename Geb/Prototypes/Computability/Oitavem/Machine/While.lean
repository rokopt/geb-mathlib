/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Loops with output

The configuration invariant for a finite loop may include a growing write-only
output. The existing loop construction preserves the body's work-space bound
without requiring that the body emit nothing.

## Main statements

* {lit}`arrives_liftBody` transports a halting body computation into its loop.
* {lit}`arrives_whileNonblank` proves a loop's full configuration invariant.

## Implementation notes

These statements use CSLib's configurations and inherit their
{lit}`Classical.choice` dependency. This module is included in
{lit}`GebMeta.classicalAllowedModules`.

## Tags

Turing machine, loop invariant, write-only output, logarithmic space
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace.Machine

public section

/-- A halting body computation returns to the loop test, preserving its entire
configuration, including output. -/
theorem arrives_liftBody {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    {P : MultiTapeTM k Bool S} {cfg cfg' : Cfg k Bool S input} {t B : ℕ}
    (h : Arrives P cfg cfg' t B) (hh : cfg'.state = none) :
    Arrives (whileNonblank p P) (liftBody cfg) { cfg' with state := some (.inl ()) } t B where
  live := fun t' ht' ↦ by
    rw [whileNonblank_runFrom_body p P cfg t' (fun s hs ↦ h.live s (by omega))]
    exact liftBody_state_ne_none _
  runFrom_eq := by
    rw [whileNonblank_runFrom_body p P cfg t h.live, h.runFrom_eq, liftBody_halt cfg' hh]
  pos := fun t' ht' i ↦ by
    rw [whileNonblank_runFrom_body p P cfg t' (fun s hs ↦ h.live s (by omega)),
      liftBody_workTapePos]
    exact h.pos t' ht' i

/-- A family of body computations determines the loop's final configuration and
bounds its running time and work-head positions, even when the body emits output. -/
theorem arrives_whileNonblank {k : ℕ} {S : Type} {input : List Bool}
    (p : Probe k) (P : MultiTapeTM k Bool S) (B T : ℕ) :
    ∀ (N : ℕ) (c : ℕ → Cfg k Bool S input),
      (∀ j < N, probeOf p (c j) ≠ none) → probeOf p (c N) = none →
      (∀ j < N, ∃ t ≤ T, Arrives P { c j with state := some P.q₀ }
        { c (j + 1) with state := none } t B) →
      (∀ i, -1 ≤ (c 0).workTapePos i ∧ (c 0).workTapePos i ≤ B) →
      ∃ t ≤ N * (T + 1) + 1,
        Arrives (whileNonblank p P) { c 0 with state := some (.inl ()) }
          { c N with state := none } t B := by
  refine Nat.rec (fun c _ hexit _ hpos ↦ ⟨1, by omega, ?_⟩)
    (fun N ih c hin hexit hrun hpos ↦ ?_)
  · exact (whileNonblank_exit p P _ rfl hexit B hpos).toArrives
  · obtain ⟨t, ht, r⟩ := hrun 0 (by omega)
    have r₁ := whileNonblank_enter p P { c 0 with state := some (.inl ()) }
      rfl (hin 0 (by omega)) B hpos
    have r₂ := arrives_liftBody p r rfl
    have hpos1 : ∀ i, -1 ≤ (c 1).workTapePos i ∧ (c 1).workTapePos i ≤ B := by
      intro i
      have := r.pos t (le_refl _) i
      rwa [r.runFrom_eq] at this
    obtain ⟨t', ht', r₃⟩ := ih (fun i ↦ c (i + 1)) (fun i hi ↦ hin (i + 1) (by omega))
      hexit (fun i hi ↦ hrun (i + 1) (by omega)) hpos1
    refine ⟨1 + t + t', ?_, (r₁.toArrives.trans r₂).trans r₃⟩
    rw [Nat.succ_mul]
    omega

end

end Geb.Oitavem.Machine
