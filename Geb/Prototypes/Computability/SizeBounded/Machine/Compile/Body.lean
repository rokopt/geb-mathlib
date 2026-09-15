/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family

set_option doc.verso true

/-!
# The transformer of a recursion body

One turn of the recursion loop runs the step programs into the scratch
registers, copies the scratch registers into the value registers, and extends
the processed suffix by the bounded successor of the recursion argument.
{lit}`srnBody_transforms` reads the resulting valuation off the parts: the
steps write above the value registers, so
{name}`Geb.SizeBounded.Machine.composeFin_fresh` gives each scratch register
the step's meaning on the environment the body passes, and
{name}`Geb.SizeBounded.Machine.composeFin_of_lt` leaves every register below
the first scratch register alone; the copies act as the simultaneous copy of
{name}`Geb.SizeBounded.Machine.composeFin_copy`; and the two final updates are
read by {name}`Function.update_self` and {name}`Function.update_of_ne`.

# Main statements

* {lit}`srnBody_transforms` — the recursion body transforms the valuation as
  its parts do.

# Tags

Turing machine, compilation, recursion, register allocation, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem)
open Geb.SizeBounded (sbsSem length_sbsSem_le)

public section

/-- The recursion body transforms the valuation as its parts do: each step's value
into its scratch register, then into its value register; the processed suffix
extended by the bounded successor; every register below the first fresh one
unchanged. Stated for a bit {lit}`i`, step programs each correct for a step
meaning, and the register allocation of the compiler. -/
theorem srnBody_transforms {k a b : ℕ} (i : Bool) (free : ℕ)
    (hk : free + (2 * b + 3) ≤ k) (params : Fin a → Fin k) (X : Fin k)
    (hparams : ∀ p, (params p).val < free) (hX : X.val < free)
    (steps : Fin b → Prog k) (hstep : Fin b → Sem (b + a + 1)) (T B : ℕ)
    (hsteps : ∀ l, ∃ F : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (steps l).tm F T B ∧
      (∀ σ, F σ ⟨free + 3 + b + l, by have := l.isLt; omega⟩ =
        hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params))) ∧
      (∀ σ (r : Fin k), r.val < free + (2 * b + 3) →
        r ≠ ⟨free + 3 + b + l, by have := l.isLt; omega⟩ → F σ r = σ r) ∧
      (∀ σ, Bounded σ B → Bounded (F σ) B)) :
    ∃ G : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (srnBody i ⟨free + 1, by omega⟩ X ⟨free + 2, by omega⟩
        (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩)
        (fun l ↦ ⟨free + 3 + b + l, by have := l.isLt; omega⟩) steps).tm G
        (b * T + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16) + (5 * B + 12)) B ∧
      (∀ σ, G σ ⟨free + 1, by omega⟩ = sbsSem i (σ ⟨free + 1, by omega⟩) (σ X)) ∧
      (∀ σ (l : Fin b), G σ ⟨free + 3 + l, by have := l.isLt; omega⟩ =
        hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params))) ∧
      (∀ σ (r : Fin k), r.val < free + 1 → G σ r = σ r) ∧
      (∀ σ, Bounded σ B → Bounded (G σ) B) := by
  choose F hFT hFout hFframe hFB using hsteps
  -- the registers the body allocates are pairwise distinct
  have hVX : (⟨free + 1, by omega⟩ : Fin k) ≠ X := by
    refine Fin.ne_of_val_ne ?_
    change free + 1 ≠ X.val
    omega
  have hVTmp : (⟨free + 1, by omega⟩ : Fin k) ≠ ⟨free + 2, by omega⟩ := by
    refine Fin.ne_of_val_ne ?_
    change free + 1 ≠ free + 2
    omega
  have hXTmp : X ≠ (⟨free + 2, by omega⟩ : Fin k) := by
    refine Fin.ne_of_val_ne ?_
    change X.val ≠ free + 2
    omega
  have hTmpV : (⟨free + 2, by omega⟩ : Fin k) ≠ ⟨free + 1, by omega⟩ := by
    refine Fin.ne_of_val_ne ?_
    change free + 2 ≠ free + 1
    omega
  have hscr : ∀ l : Fin b, (⟨free + 3 + b + l, by have := l.isLt; omega⟩ : Fin k) ≠
      ⟨free + 3 + l, by have := l.isLt; omega⟩ := by
    intro l
    have := l.isLt
    refine Fin.ne_of_val_ne ?_
    change free + 3 + b + (l : ℕ) ≠ free + 3 + (l : ℕ)
    omega
  have hvalsV : ∀ l : Fin b, (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) ≠
      ⟨free + 1, by omega⟩ := by
    intro l
    refine Fin.ne_of_val_ne ?_
    change free + 3 + (l : ℕ) ≠ free + 1
    omega
  have hvalsTmp : ∀ l : Fin b, (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) ≠
      ⟨free + 2, by omega⟩ := by
    intro l
    refine Fin.ne_of_val_ne ?_
    change free + 3 + (l : ℕ) ≠ free + 2
    omega
  have hVvals : ∀ l : Fin b, (⟨free + 1, by omega⟩ : Fin k) ≠
      ⟨free + 3 + l, by have := l.isLt; omega⟩ := fun l ↦ Ne.symm (hvalsV l)
  have hXvals : ∀ l : Fin b, X ≠ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) := by
    intro l
    refine Fin.ne_of_val_ne ?_
    change X.val ≠ free + 3 + (l : ℕ)
    omega
  -- the value registers are distinct, and none of them is a scratch register
  have hvalsInj : Function.Injective
      (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k)) := by
    intro l l' h
    have hv : free + 3 + (l : ℕ) = free + 3 + (l' : ℕ) := congrArg Fin.val h
    exact Fin.ext (by omega)
  have hds : ∀ l l' : Fin b, (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) ≠
      ⟨free + 3 + b + l', by have := l'.isLt; omega⟩ := by
    intro l l' h
    have hv : free + 3 + (l : ℕ) = free + 3 + b + (l' : ℕ) := congrArg Fin.val h
    have := l.isLt
    omega
  have hcc := composeFin_copy (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k))
    (fun l : Fin b ↦ (⟨free + 3 + b + l, by have := l.isLt; omega⟩ : Fin k)) hvalsInj hds
  -- the steps change nothing below the scratch registers
  have hFlo : ∀ (l : Fin b) (σ : Fin k → List Bool) (r : Fin k), r.val < free + 3 + b →
      F l σ r = σ r := by
    intro l σ r hr
    have := l.isLt
    refine hFframe l σ r (by omega) (Fin.ne_of_val_ne ?_)
    change r.val ≠ free + 3 + b + (l : ℕ)
    omega
  have hsF : ∀ (σ : Fin k → List Bool) (r : Fin k), r.val < free + 3 + b →
      composeFin b F σ r = σ r := composeFin_of_lt (free + 3 + b) b F hFlo
  have hsFV : ∀ σ : Fin k → List Bool,
      composeFin b F σ ⟨free + 1, by omega⟩ = σ ⟨free + 1, by omega⟩ := by
    intro σ
    refine hsF σ _ ?_
    change free + 1 < free + 3 + b
    omega
  have hsFX : ∀ σ : Fin k → List Bool, composeFin b F σ X = σ X := fun σ ↦ hsF σ X (by omega)
  -- the environment a step reads lies below the scratch registers
  have henv := srnEnv_lt free hk params hparams
  have hg : ∀ (l : Fin b) (σ σ' : Fin k → List Bool),
      (∀ r : Fin k, r.val < free + 3 + b → σ r = σ' r) →
      hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params)) =
        hstep l (σ' ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params)) :=
    fun l σ σ' h ↦ congrArg (hstep l) (funext fun j ↦ h _ (henv j))
  have hsVal : ∀ (σ : Fin k → List Bool) (l : Fin b),
      composeFin b F σ ⟨free + 3 + b + l, by have := l.isLt; omega⟩ =
        hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params)) :=
    composeFin_fresh (free + 3 + b) b (by omega) F
      (fun l σ ↦ hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
        (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params)))
      hg hFout (fun l σ r hr hne ↦ hFframe l σ r (by omega) hne)
  have hcopiesB : ∀ σ : Fin k → List Bool, Bounded σ B →
      Bounded (composeFin b (fun l (σ : Fin k → List Bool) ↦ Function.update σ
        (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k)
        (σ ⟨free + 3 + b + l, by have := l.isLt; omega⟩)) σ) B :=
    composeFin_bounded B b _ (fun _ _ hσ ↦ hσ.update (hσ _))
  refine ⟨_, Transforms.mono_time (Transforms.seq
    (Transforms.seqFin B T b _ _ F hFT hFB)
    (Transforms.seq
      (Transforms.seqFin B (5 * B + 12) b _ _
        (fun l (σ : Fin k → List Bool) ↦ Function.update σ
          (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k)
          (σ ⟨free + 3 + b + l, by have := l.isLt; omega⟩))
        (fun l ↦ copy_transforms _ _ (hscr l) B)
        (fun _ _ hσ ↦ hσ.update (hσ _)))
      (Transforms.seq
        (sbs_transforms i ⟨free + 1, by omega⟩ X ⟨free + 2, by omega⟩ hVX hVTmp hXTmp B)
        (copy_transforms ⟨free + 2, by omega⟩ ⟨free + 1, by omega⟩ hTmpV B)
        (fun _ hσ ↦ hσ.update (length_sbsSem_le i (hσ _) (hσ _))))
      hcopiesB)
    (composeFin_bounded B b F hFB)) (by omega), ?_, ?_, ?_, ?_⟩
  · intro σ
    rw [Function.update_self, Function.update_self, (hcc _).2 _ hVvals, hsFV,
      (hcc _).2 _ hXvals, hsFX]
  · intro σ l
    rw [Function.update_of_ne (hvalsV l), Function.update_of_ne (hvalsTmp l), (hcc _).1 l,
      hsVal]
  · intro σ r hr
    have hrV : r ≠ (⟨free + 1, by omega⟩ : Fin k) := by
      refine Fin.ne_of_val_ne ?_
      change r.val ≠ free + 1
      omega
    have hrTmp : r ≠ (⟨free + 2, by omega⟩ : Fin k) := by
      refine Fin.ne_of_val_ne ?_
      change r.val ≠ free + 2
      omega
    have hrvals : ∀ l : Fin b, r ≠ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) := by
      intro l
      refine Fin.ne_of_val_ne ?_
      change r.val ≠ free + 3 + (l : ℕ)
      omega
    rw [Function.update_of_ne hrV, Function.update_of_ne hrTmp, (hcc _).2 r hrvals,
      hsF σ r (by omega)]
  · intro σ hσ
    have h2 := hcopiesB _ (composeFin_bounded B b F hFB σ hσ)
    refine Bounded.update (Bounded.update h2 ?_) ?_
    · exact length_sbsSem_le i (h2 _) (h2 _)
    · exact Bounded.update h2 (length_sbsSem_le i (h2 _) (h2 _)) _

end

end Geb.SizeBounded.Machine
