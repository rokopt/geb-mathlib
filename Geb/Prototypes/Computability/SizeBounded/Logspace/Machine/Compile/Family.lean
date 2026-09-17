/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family

set_option doc.verso true in
/-!
# Valuations after a family of fresh register writers

A compiled substitution or recursion node runs a family of programs, each
writing its own fresh logical register, two tapes, above a watermark
{lit}`lo` and reading only tapes below it. {lit}`composeFin_fresh2` reads the
valuation the composite {name}`Geb.SizeBounded.Machine.composeFin` of such a
family produces off its members: the fresh register of member {lit}`l`, the
tapes {lit}`lo + 2 * l` and {lit}`lo + 2 * l + 1`, holds the member's two
outputs on the original valuation. It is the two-tape form of
{name}`Geb.SizeBounded.Machine.composeFin_fresh`, which
{name}`Geb.SizeBounded.Machine.composeFin_of_lt` serves unchanged.

# Main statements

* {lit}`composeFin_fresh2` — the composite leaves the fresh register of each
  member holding the member's outputs on the original valuation.

# Tags

Turing machine, composition, register allocation, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded.Machine (composeFin composeFin_zero composeFin_succ composeFin_of_lt)

public section

/-- A family whose member {lit}`l` writes the values {lit}`g₀ l` and {lit}`g₁ l`
of the tapes below {lit}`lo` into the tapes {lit}`lo + 2 * l` and
{lit}`lo + 2 * l + 1` and changes no other tape below {lit}`lo + 2 * m` leaves
those tapes holding the values of the original valuation's tapes below
{lit}`lo`. -/
theorem composeFin_fresh2 {k : ℕ} (lo : ℕ) : ∀ (m : ℕ) (hm : lo + 2 * m ≤ k)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool)
    (g₀ g₁ : Fin m → (Fin k → List Bool) → List Bool),
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g₀ l σ = g₀ l σ') →
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g₁ l σ = g₁ l σ') →
    (∀ l σ, F l σ ⟨lo + 2 * l, by have := l.isLt; omega⟩ = g₀ l σ) →
    (∀ l σ, F l σ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ = g₁ l σ) →
    (∀ (l : Fin m) σ (i : Fin k), i.val < lo + 2 * m → i ≠ ⟨lo + 2 * l, by have := l.isLt; omega⟩ →
      i ≠ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ → F l σ i = σ i) →
    ∀ σ (l : Fin m),
      composeFin m F σ ⟨lo + 2 * l, by have := l.isLt; omega⟩ = g₀ l σ ∧
      composeFin m F σ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ = g₁ l σ :=
  Nat.rec (fun _ _ _ _ _ _ _ _ _ _ l ↦ l.elim0)
    (fun m ih hm F g₀ g₁ hg₀ hg₁ hF₀ hF₁ hframe σ ↦ by
      have hlo : ∀ (l : Fin (m + 1)) τ (i : Fin k), i.val < lo → F l τ i = τ i := by
        intro l τ i hi
        refine hframe l τ i (by omega) (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_)
        · change (i : ℕ) ≠ lo + 2 * (l : ℕ)
          omega
        · change (i : ℕ) ≠ lo + 2 * (l : ℕ) + 1
          omega
      have hbelow : ∀ (i : Fin k), i.val < lo →
          composeFin m (fun j ↦ F j.castSucc) σ i = σ i :=
        composeFin_of_lt lo m (fun j ↦ F j.castSucc) (fun l ↦ hlo l.castSucc) σ
      refine Fin.lastCases ?_ ?_
      · rw [composeFin_succ]
        exact ⟨(hF₀ (Fin.last m) _).trans (hg₀ _ _ _ hbelow),
          (hF₁ (Fin.last m) _).trans (hg₁ _ _ _ hbelow)⟩
      · intro l
        have hl := l.isLt
        rw [composeFin_succ,
          hframe (Fin.last m) _ _ (by simp only [Fin.val_castSucc]; omega)
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega)),
          hframe (Fin.last m) _ _ (by simp only [Fin.val_castSucc]; omega)
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))]
        exact ih (by omega) (fun j ↦ F j.castSucc) (fun j ↦ g₀ j.castSucc) (fun j ↦ g₁ j.castSucc)
          (fun j ↦ hg₀ j.castSucc) (fun j ↦ hg₁ j.castSucc) (fun j ↦ hF₀ j.castSucc)
          (fun j ↦ hF₁ j.castSucc)
          (fun j τ i hi hne hne' ↦ hframe j.castSucc τ i (by omega) hne hne') σ l)

end

end Geb.SizeBounded.Logspace.Machine
