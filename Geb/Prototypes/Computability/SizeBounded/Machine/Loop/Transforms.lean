/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Basic
import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Phases
import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Iter

set_option doc.verso true

/-!
# The recursion loop's contract

{lit}`loopF` is the transformer of {name}`Geb.SizeBounded.Machine.caseLoop`:
recursion on the word of the register {lit}`R` applies, for each bit in
order, the body's transformer for that bit to the valuation with {lit}`R`
set to the word's remaining tail. The loop transforms by it, within a step
bound linear in the length bound and in the bodies' step bound, and the
transformer preserves the length bound when both bodies' do.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statement mentions {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`loopF` — the loop's transformer.

# Main statements

* {lit}`loopF_nil`, {lit}`loopF_cons` — the recursive equations of
  {lit}`loopF`.
* {lit}`loopF_bounded` — the loop's transformer preserves the length bound.
* {lit}`Transforms.caseLoop` — the loop's contract.

# Tags

Turing machine, loop, recursion, register
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

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
      Bounded (loopF R FF FT r σ) B := by
  refine List.rec ?_ ?_
  · intro σ _ hσ
    rw [loopF_nil]
    exact hσ
  · intro c r ih σ hlen hσ
    rw [List.length_cons] at hlen
    have hupd : Bounded (Function.update σ R r) B := by
      intro i
      by_cases hi : i = R
      · subst hi
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hi]
        exact hσ i
    have hb : Bounded ((if c then FT else FF) (Function.update σ R r)) B := by
      cases c with
      | false => exact hFb _ hupd
      | true => exact hTb _ hupd
    rw [loopF_cons]
    exact ih _ (by omega) hb

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
      (B * (T + 2 * B + 6) + 3) B := by
  have aux : ∀ (r input : List Bool)
      (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (σ : Fin k → List Bool),
      cfg.state = some (.inl 0) → σ R = r → Parked cfg → Holds cfg σ → Bounded σ B →
      ∃ t ≤ r.length * (T + 2 * B + 6) + 2,
        RunsTo (Machine.caseLoop R bodyF bodyT) cfg (after cfg (loopF R FF FT r σ)) t B := by
    intro r
    refine List.rec ?_ ?_ r
    · intro input cfg σ hq hr hpark hσ hB
      have hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ (B : ℤ) := by
        intro j
        rw [hpark j]
        constructor <;> omega
      have htarget : after cfg σ = { cfg with state := none } := by
        apply Cfg.ext
        · rfl
        · rfl
        · funext i
          exact (hσ i).symm
        · rfl
      refine ⟨2, by omega, ?_⟩
      rw [loopF_nil, htarget]
      exact caseLoop_exit R bodyF bodyT cfg hq ((hσ R).trans (by rw [hr])) (hpark R) B hpos
    · intro c r ih input cfg σ hq hr hpark hσ hB
      have hlen : r.length + 1 ≤ B := by
        have h := hB R
        rw [hr, List.length_cons] at h
        exact h
      have hupd : Bounded (Function.update σ R r) B := by
        intro i
        by_cases hi : i = R
        · subst hi
          rw [Function.update_self]
          omega
        · rw [Function.update_of_ne hi]
          exact hB i
      have hb : Bounded ((if c then FT else FF) (Function.update σ R r)) B := by
        cases c with
        | false => exact hFb _ hupd
        | true => exact hTb _ hupd
      have hR' : ((if c then FT else FF) (Function.update σ R r)) R = r := by
        cases c with
        | false => exact (hFR _).trans (Function.update_self ..)
        | true => exact (hTR _).trans (Function.update_self ..)
      obtain ⟨t₁, ht₁, hreach⟩ :=
        caseLoop_iter R bodyF bodyT FF FT T B hF hT cfg hq σ c r hr hpark hσ hB hb
      obtain ⟨t₂, ht₂, hrun⟩ := ih _
        { after cfg ((if c then FT else FF) (Function.update σ R r)) with
          state := some (.inl 0) }
        ((if c then FT else FF) (Function.update σ R r)) rfl hR' (fun i ↦ hpark i)
        (fun _ ↦ rfl) hb
      refine ⟨t₁ + t₂, ?_, ⟨hreach.trans hrun.toReaches, hrun.halted⟩⟩
      rw [List.length_cons, Nat.succ_mul]
      omega
  intro _ cfg σ hq hpark hσ hB _
  obtain ⟨t, ht, hrun⟩ := aux (σ R) _ cfg σ hq rfl hpark hσ hB
  refine ⟨t, ?_, hrun⟩
  have hmul : (σ R).length * (T + 2 * B + 6) ≤ B * (T + 2 * B + 6) :=
    Nat.mul_le_mul_right _ (hB R)
  omega

end

end Geb.SizeBounded.Machine
