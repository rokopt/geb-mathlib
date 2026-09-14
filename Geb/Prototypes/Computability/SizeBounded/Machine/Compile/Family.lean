/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.SeqFin

set_option doc.verso true

/-!
# Valuations after a family of fresh writers

A compiled substitution or recursion node runs a family of programs, each
writing its own fresh register above a watermark {lit}`lo` and reading only
registers below it. The statements here read off the valuation the composite
{name}`Geb.SizeBounded.Machine.composeFin` of such a family produces: every
register below {lit}`lo` is unchanged, and the fresh register {lit}`lo + l`
holds the member {lit}`l`'s output on the original valuation. A family of
copies into distinct destinations, none of them a source, acts as the
simultaneous copy.
{lit}`srnEnv_injective` supplies the injectivity of the register environment a
recursion step passes to its body.

# Main statements

* {lit}`composeFin_of_lt` — a family that changes nothing below {lit}`lo`
  composes to a transformer that changes nothing below {lit}`lo`.
* {lit}`composeFin_fresh` — the composite leaves the fresh register
  {lit}`lo + l` holding the member {lit}`l`'s output on the original
  valuation.
* {lit}`composeFin_copy` — a family of copies into distinct destinations,
  none a source, acts as the simultaneous copy.
* {lit}`srnEnv_injective` — the environment of a recursion step is injective.

# Tags

Turing machine, composition, register allocation, injectivity
-/

namespace Geb.SizeBounded.Machine

public section

/-- A family each of whose members changes nothing below {lit}`lo` leaves every
register below {lit}`lo` unchanged. -/
theorem composeFin_of_lt {k : ℕ} (lo : ℕ) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ l σ (i : Fin k), i.val < lo → F l σ i = σ i) →
    ∀ σ (i : Fin k), i.val < lo → composeFin m F σ i = σ i :=
  Nat.rec (fun _ _ _ _ _ ↦ rfl)
    (fun m ih F hF σ i hi ↦ by
      rw [composeFin_succ, hF (Fin.last m) _ i hi]
      exact ih (fun j ↦ F j.castSucc) (fun l ↦ hF l.castSucc) σ i hi)

/-- A family whose member {lit}`l` writes the value {lit}`g l` of the registers
below {lit}`lo` into the register {lit}`lo + l` and changes no other register
below {lit}`lo + m` leaves register {lit}`lo + l` holding {lit}`g l` of the
original valuation's registers below {lit}`lo`. -/
theorem composeFin_fresh {k : ℕ} (lo : ℕ) : ∀ (m : ℕ) (hm : lo + m ≤ k)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool)
    (g : Fin m → (Fin k → List Bool) → List Bool),
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g l σ = g l σ') →
    (∀ l σ, F l σ ⟨lo + l, by have := l.isLt; omega⟩ = g l σ) →
    (∀ (l : Fin m) σ (i : Fin k), i.val < lo + m → i ≠ ⟨lo + l, by have := l.isLt; omega⟩ →
      F l σ i = σ i) →
    ∀ σ (l : Fin m), composeFin m F σ ⟨lo + l, by have := l.isLt; omega⟩ = g l σ :=
  Nat.rec (fun _ _ _ _ _ _ _ l ↦ l.elim0)
    (fun m ih hm F g hg hFg hframe σ ↦ by
      have hlo : ∀ (l : Fin (m + 1)) τ (i : Fin k), i.val < lo → F l τ i = τ i := by
        intro l τ i hi
        refine hframe l τ i (by omega) (Fin.ne_of_val_ne ?_)
        change (i : ℕ) ≠ lo + (l : ℕ)
        omega
      have hbelow : ∀ (i : Fin k), i.val < lo →
          composeFin m (fun j ↦ F j.castSucc) σ i = σ i :=
        composeFin_of_lt lo m (fun j ↦ F j.castSucc) (fun l ↦ hlo l.castSucc) σ
      refine Fin.lastCases ?_ ?_
      · rw [composeFin_succ]
        exact (hFg (Fin.last m) _).trans (hg _ _ _ hbelow)
      · intro l
        have hl := l.isLt
        rw [composeFin_succ,
          hframe (Fin.last m) _ _ (by simp only [Fin.val_castSucc]; omega)
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))]
        exact ih (by omega) (fun j ↦ F j.castSucc) (fun j ↦ g j.castSucc)
          (fun j ↦ hg j.castSucc) (fun j ↦ hFg j.castSucc)
          (fun j τ i hi hne ↦ hframe j.castSucc τ i (by omega) hne) σ l)

/-- A family of copies into distinct destinations, none a source, leaves each
destination holding its source's original value and every other register
unchanged. -/
theorem composeFin_copy {k m : ℕ} (dst src : Fin m → Fin k)
    (hdst : Function.Injective dst) (hds : ∀ l l', dst l ≠ src l') :
    ∀ (σ : Fin k → List Bool),
      (∀ l, composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ (dst l) =
        σ (src l)) ∧
      (∀ (i : Fin k), (∀ l, i ≠ dst l) →
        composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ i = σ i) := by
  refine Nat.rec (motive := fun m ↦ ∀ (dst src : Fin m → Fin k), Function.Injective dst →
    (∀ l l', dst l ≠ src l') → ∀ (σ : Fin k → List Bool),
      (∀ l, composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ (dst l) =
        σ (src l)) ∧
      (∀ (i : Fin k), (∀ l, i ≠ dst l) →
        composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ i = σ i))
    (fun _ _ _ _ _ ↦ ⟨fun l ↦ l.elim0, fun _ _ ↦ rfl⟩) ?_ m dst src hdst hds
  intro n ih dst src hdst hds σ
  have hlast : ∀ j : Fin n, dst j.castSucc ≠ dst (Fin.last n) := by
    intro j h
    have hj := j.isLt
    have := hdst h
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at this
    omega
  have hsub := ih (fun l ↦ dst l.castSucc) (fun l ↦ src l.castSucc)
    (fun l l' h ↦ Fin.castSucc_injective n (hdst h))
    (fun l l' ↦ hds l.castSucc l'.castSucc) σ
  constructor
  · refine Fin.lastCases ?_ ?_
    · rw [composeFin_succ, Function.update_self]
      exact hsub.2 (src (Fin.last n)) (fun l ↦ (hds l.castSucc (Fin.last n)).symm)
    · intro j
      rw [composeFin_succ, Function.update_of_ne (hlast j)]
      exact hsub.1 j
  · intro i hi
    rw [composeFin_succ, Function.update_of_ne (hi (Fin.last n))]
    exact hsub.2 i (fun l ↦ hi l.castSucc)

/-- The environment of a recursion step, the processed suffix, the value registers
and the parameters, is injective when the parameters are and lie below the fresh
registers. -/
theorem srnEnv_injective {k a b : ℕ} (free : ℕ) (hk : free + (2 * b + 3) ≤ k)
    (params : Fin a → Fin k) (hparams : ∀ p, (params p).val < free)
    (hinj : Function.Injective params) :
    Function.Injective (Fin.cons (⟨free + 1, by omega⟩ : Fin k)
      (Fin.append (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k))
        params)) := by
  refine Fin.cons_injective_of_injective ?_ (Fin.append_injective_iff.mpr ⟨?_, hinj, ?_⟩)
  · rintro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left l =>
      rw [Fin.append_left] at hi
      simp only [Fin.mk.injEq] at hi
      omega
    | right p =>
      rw [Fin.append_right, Fin.ext_iff] at hi
      change (params p : ℕ) = free + 1 at hi
      have := hparams p
      omega
  · intro l l' h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro l p h
    rw [Fin.ext_iff] at h
    change free + 3 + (l : ℕ) = (params p : ℕ) at h
    have := hparams p
    omega

end

end Geb.SizeBounded.Machine
