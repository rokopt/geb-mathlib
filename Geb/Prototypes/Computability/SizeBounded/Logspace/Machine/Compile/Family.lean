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

* {lit}`composeFin_pres` — a composite of members preserving a predicate
  preserves it.
* {lit}`composeFin_fresh2` — the composite leaves the fresh register of each
  member holding the member's outputs on the original valuation.
* {lit}`composeFin_copy2` — a family of register copies acts as the
  simultaneous copy.

# Tags

Turing machine, composition, register allocation, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded.Machine (composeFin composeFin_zero composeFin_succ composeFin_of_lt)

public section

/-- A composite of members each preserving a predicate preserves it. -/
theorem composeFin_pres {k : ℕ} (P : (Fin k → List Bool) → Prop) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ l σ, P σ → P (F l σ)) → ∀ σ, P σ → P (composeFin m F σ) :=
  Nat.rec (fun _ _ _ h ↦ h)
    (fun m ih F hF σ hσ ↦ by
      rw [composeFin_succ]
      exact hF _ _ (ih (fun j ↦ F j.castSucc) (fun l ↦ hF l.castSucc) σ hσ))

/-- A family whose member {lit}`l` writes the values {lit}`g₀ l` and {lit}`g₁ l`
of the tapes below {lit}`lo` into the tapes {lit}`lo + 2 * l` and
{lit}`lo + 2 * l + 1`, on valuations satisfying a predicate every member
preserves, and changes no other tape below {lit}`lo + 2 * m`, leaves those
tapes holding the values of the original valuation's tapes below {lit}`lo`. -/
theorem composeFin_fresh2 {k : ℕ} (lo : ℕ) (P : (Fin k → List Bool) → Prop) : ∀ (m : ℕ)
    (hm : lo + 2 * m ≤ k) (F : Fin m → (Fin k → List Bool) → Fin k → List Bool)
    (g₀ g₁ : Fin m → (Fin k → List Bool) → List Bool),
    (∀ l σ, P σ → P (F l σ)) →
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g₀ l σ = g₀ l σ') →
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g₁ l σ = g₁ l σ') →
    (∀ l σ, P σ → F l σ ⟨lo + 2 * l, by have := l.isLt; omega⟩ = g₀ l σ) →
    (∀ l σ, P σ → F l σ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ = g₁ l σ) →
    (∀ (l : Fin m) σ (i : Fin k), i.val < lo + 2 * m → i ≠ ⟨lo + 2 * l, by have := l.isLt; omega⟩ →
      i ≠ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ → F l σ i = σ i) →
    ∀ σ, P σ → ∀ (l : Fin m),
      composeFin m F σ ⟨lo + 2 * l, by have := l.isLt; omega⟩ = g₀ l σ ∧
      composeFin m F σ ⟨lo + 2 * l + 1, by have := l.isLt; omega⟩ = g₁ l σ :=
  Nat.rec (fun _ _ _ _ _ _ _ _ _ _ _ _ l ↦ l.elim0)
    (fun m ih hm F g₀ g₁ hP hg₀ hg₁ hF₀ hF₁ hframe σ hσ ↦ by
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
      have hPm : P (composeFin m (fun j ↦ F j.castSucc) σ) :=
        composeFin_pres P m (fun j ↦ F j.castSucc) (fun l ↦ hP l.castSucc) σ hσ
      refine Fin.lastCases ?_ ?_
      · rw [composeFin_succ]
        exact ⟨(hF₀ (Fin.last m) _ hPm).trans (hg₀ _ _ _ hbelow),
          (hF₁ (Fin.last m) _ hPm).trans (hg₁ _ _ _ hbelow)⟩
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
          (fun j ↦ hP j.castSucc) (fun j ↦ hg₀ j.castSucc) (fun j ↦ hg₁ j.castSucc)
          (fun j ↦ hF₀ j.castSucc) (fun j ↦ hF₁ j.castSucc)
          (fun j τ i hi hne hne' ↦ hframe j.castSucc τ i (by omega) hne hne') σ hσ l)

/-- A family of register copies into distinct destinations, none a source tape,
leaves each destination register holding its source's original tapes and every
other tape unchanged. -/
theorem composeFin_copy2 {k m : ℕ} (dst src : Fin m → Fin 2 → Fin k)
    (hdst : Function.Injective fun x : Fin m × Fin 2 ↦ dst x.1 x.2)
    (hds : ∀ l b l' b', dst l b ≠ src l' b') :
    ∀ (σ : Fin k → List Bool),
      (∀ l b, composeFin m (fun l σ ↦ Function.update (Function.update σ (dst l 0) (σ (src l 0)))
        (dst l 1) (σ (src l 1))) σ (dst l b) = σ (src l b)) ∧
      (∀ (i : Fin k), (∀ l b, i ≠ dst l b) →
        composeFin m (fun l σ ↦ Function.update (Function.update σ (dst l 0) (σ (src l 0)))
          (dst l 1) (σ (src l 1))) σ i = σ i) := by
  refine Nat.rec (motive := fun m ↦ ∀ (dst src : Fin m → Fin 2 → Fin k),
    (Function.Injective fun x : Fin m × Fin 2 ↦ dst x.1 x.2) →
    (∀ l b l' b', dst l b ≠ src l' b') → ∀ (σ : Fin k → List Bool),
      (∀ l b, composeFin m (fun l σ ↦ Function.update (Function.update σ (dst l 0) (σ (src l 0)))
        (dst l 1) (σ (src l 1))) σ (dst l b) = σ (src l b)) ∧
      (∀ (i : Fin k), (∀ l b, i ≠ dst l b) →
        composeFin m (fun l σ ↦ Function.update (Function.update σ (dst l 0) (σ (src l 0)))
          (dst l 1) (σ (src l 1))) σ i = σ i))
    (fun _ _ _ _ _ ↦ ⟨fun l ↦ l.elim0, fun _ _ ↦ rfl⟩) ?_ m dst src hdst hds
  intro n ih dst src hdst hds σ
  have h01 : dst (Fin.last n) 0 ≠ dst (Fin.last n) 1 := fun h ↦ by
    have := congrArg Prod.snd (@hdst (Fin.last n, 0) (Fin.last n, 1) h)
    exact absurd this (by change (0 : Fin 2) ≠ 1; decide)
  have hlast : ∀ (j : Fin n) (b b' : Fin 2), dst j.castSucc b ≠ dst (Fin.last n) b' := by
    intro j b b' h
    have := congrArg Prod.fst (@hdst (j.castSucc, b) (Fin.last n, b') h)
    have hj := j.isLt
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at this
    omega
  have hsub := ih (fun l ↦ dst l.castSucc) (fun l ↦ src l.castSucc)
    (fun x y h ↦ by
      have := @hdst (x.1.castSucc, x.2) (y.1.castSucc, y.2) h
      have h1 := congrArg Prod.fst this
      have h2 := congrArg Prod.snd this
      exact Prod.ext (Fin.castSucc_injective n h1) h2)
    (fun l b l' b' ↦ hds l.castSucc b l'.castSucc b') σ
  constructor
  · intro l b
    refine Fin.lastCases (motive := fun l ↦ ∀ b, composeFin (n + 1) _ σ (dst l b) = σ (src l b))
      (fun b ↦ ?_) (fun j b ↦ ?_) l b
    · rw [composeFin_succ]
      have hs0 := hsub.2 (src (Fin.last n) 0) (fun l b ↦ (hds l.castSucc b (Fin.last n) 0).symm)
      have hs1 := hsub.2 (src (Fin.last n) 1) (fun l b ↦ (hds l.castSucc b (Fin.last n) 1).symm)
      match b with
      | 0 =>
        rw [Function.update_of_ne h01, Function.update_self]
        exact hs0
      | 1 =>
        rw [Function.update_self]
        exact hs1
    · rw [composeFin_succ, Function.update_of_ne (hlast j b 1), Function.update_of_ne (hlast j b 0)]
      exact hsub.1 j b
  · intro i hi
    rw [composeFin_succ, Function.update_of_ne (hi (Fin.last n) 1),
      Function.update_of_ne (hi (Fin.last n) 0)]
    exact hsub.2 i (fun l b ↦ hi l.castSucc b)

end

end Geb.SizeBounded.Logspace.Machine
