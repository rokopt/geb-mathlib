/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
public import Geb.Prototypes.Computability.Oitavem.Machine.Generated
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
* {lit}`EmitsIn.whileReg` gives a subroutine contract from indexed valuations and output.

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

/-- An indexed valuation and output invariant gives a reusable emitting loop contract.
The body restores its heads after each call, and each iteration appends its output. -/
theorem EmitsIn.whileReg {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ} (R : Fin k)
    (hP : EmitsIn P Pre F W T B) (Pre₀ : List Bool → (Fin k → List Bool) → Prop)
    (N : List Bool → (Fin k → List Bool) → ℕ) (Nb : ℕ → ℕ)
    (V : List Bool → (Fin k → List Bool) → ℕ → Fin k → List Bool)
    (Out : List Bool → (Fin k → List Bool) → ℕ → List Bool)
    (hN : ∀ input σ, Pre₀ input σ → N input σ ≤ Nb input.length)
    (hzero : ∀ input σ, Pre₀ input σ → V input σ 0 = σ ∧ Out input σ 0 = [])
    (hiter : ∀ input σ, Pre₀ input σ → ∀ j < N input σ,
      V input σ j R ≠ [] ∧ Pre input (V input σ j) ∧
        F input (V input σ j) = V input σ (j + 1) ∧
        Out input σ j ++ W input (V input σ j) = Out input σ (j + 1))
    (hexit : ∀ input σ, Pre₀ input σ → V input σ (N input σ) R = []) :
    EmitsIn (whileNonblank (some R) P) Pre₀ (fun input σ ↦ V input σ (N input σ))
      (fun input σ ↦ Out input σ (N input σ)) (fun n ↦ Nb n * (T n + 1) + 1) B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  let c : ℕ → Cfg k Bool S input := fun j ↦
    { cfg with state := none, workTapes := fun i ↦ tapeOf (V input σ j i)
               output := cfg.output ++ Out input σ j }
  have hbnd : ∀ j ≤ N input σ, Bounded (V input σ j) (B input.length) := by
    refine Nat.rec (fun _ ↦ (hzero input σ hp).1.symm ▸ hB) (fun j ih hj ↦ ?_)
    have hi := hiter input σ hp j (by omega)
    rw [← hi.2.2.1]
    exact (hP input { c j with state := some P.q₀ } _ rfl hpark hpos (fun _ ↦ rfl)
      hi.2.1 (ih (by omega))).1
  have hprobe (j : ℕ) : probeOf (some R) (c j) = tapeOf (V input σ j R) 0 := by
    change tapeOf (V input σ j R) (cfg.workTapePos R) = _
    rw [hpark R]
  obtain ⟨t, ht, hr⟩ := arrives_whileNonblank (some R) P (B input.length) (T input.length)
    (N input σ) c
    (by
      intro j hj hz
      rw [hprobe] at hz
      exact (hiter input σ hp j hj).1 ((tapeOf_zero_eq_none_iff _).mp hz))
    (by rw [hprobe]; exact (tapeOf_zero_eq_none_iff _).mpr (hexit input σ hp))
    (by
      intro j hj
      have hi := hiter input σ hp j hj
      obtain ⟨_, t, ht, he⟩ := hP input { c j with state := some P.q₀ } _
        rfl hpark hpos (fun _ ↦ rfl) hi.2.1 (hbnd j (by omega))
      refine ⟨t, ht, (he.congr_target ?_).toArrives⟩
      apply Cfg.ext
      · rfl
      · rfl
      · exact congrArg (fun v i ↦ tapeOf (v i)) hi.2.2.1
      · rfl
      · change (cfg.output ++ Out input σ j) ++ W input (V input σ j) =
          cfg.output ++ Out input σ (j + 1)
        rw [List.append_assoc, hi.2.2.2])
    (by
      intro i
      change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length
      rw [hpark i]
      constructor <;> omega)
  have hstart : { c 0 with state := some (.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      change tapeOf (V input σ 0 i) = cfg.workTapes i
      rw [(hzero input σ hp).1, hσ]
    · rfl
    · change cfg.output ++ Out input σ 0 = cfg.output
      rw [(hzero input σ hp).2, List.append_nil]
  rw [hstart] at hr
  refine ⟨hbnd _ le_rfl, t,
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hN input σ hp)) 1),
    ⟨hr, ?_, rfl⟩⟩
  apply List.append_cancel_left (as := cfg.output)
  rw [← runFrom_output, hr.runFrom_eq]

end

end Geb.Oitavem.Machine
