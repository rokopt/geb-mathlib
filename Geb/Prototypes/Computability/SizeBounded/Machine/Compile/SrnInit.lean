/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family
public import Geb.Mathlib.Computability.Cobham.Basic

set_option doc.verso true

/-!
# The valuation entering the recursion loop

A compiled recursion node writes the reverse of its argument into the recursion
register, empties the processed suffix, and runs the family of base programs,
each writing its own value register. {lit}`srnInit_valuation` reads the
resulting valuation off the parts: the two updates and the value registers lie
at or above the first fresh register, so
{name}`Geb.SizeBounded.Machine.composeFin_of_lt` leaves every register below it
alone, and {name}`Geb.SizeBounded.Machine.composeFin_fresh` leaves each value
register holding its base's meaning at the parameters, which lie below the
updates and so are read unchanged.

# Main statements

* {lit}`srnInit_valuation` — the valuation entering the recursion loop is the
  recursion register at the reversed argument, the empty processed suffix, and
  the value registers at the bases.

# Tags

Turing machine, compilation, recursion, register allocation, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem)

public section

/-- The valuation entering the recursion loop: the recursion register holds the
reverse of the argument, the processed suffix is empty, each value register holds
its base at the parameters, and every register below the first fresh one is
unchanged. -/
theorem srnInit_valuation {k a b : ℕ} (free : ℕ) (hk : free + (2 * b + 3) ≤ k)
    (params : Fin a → Fin k) (X : Fin k) (hparams : ∀ p, (params p).val < free)
    (Fb : Fin b → (Fin k → List Bool) → Fin k → List Bool)
    (hbase : Fin b → Sem a)
    (hout : ∀ l σ, Fb l σ ⟨free + 3 + l, by have := l.isLt; omega⟩ = hbase l (σ ∘ params))
    (hframe : ∀ (l : Fin b) σ (r : Fin k), r.val < free + (2 * b + 3) →
      r ≠ ⟨free + 3 + l, by have := l.isLt; omega⟩ → Fb l σ r = σ r) :
    ∀ σ : Fin k → List Bool,
      let G := composeFin b Fb (Function.update
        (Function.update σ ⟨free, by omega⟩ (σ X).reverse) ⟨free + 1, by omega⟩ [])
      G ⟨free, by omega⟩ = (σ X).reverse ∧ G ⟨free + 1, by omega⟩ = [] ∧
        (∀ l : Fin b, G ⟨free + 3 + l, by have := l.isLt; omega⟩ = hbase l (σ ∘ params)) ∧
        (∀ r : Fin k, r.val < free → G r = σ r) := by
  -- the bases change nothing below the first value register
  have hbelow : ∀ (τ : Fin k → List Bool) (r : Fin k), r.val < free + 3 →
      composeFin b Fb τ r = τ r :=
    composeFin_of_lt (free + 3) b Fb (fun l τ r hr ↦ by
      have := l.isLt
      refine hframe l τ r (by omega) (Fin.ne_of_val_ne ?_)
      change r.val ≠ free + 3 + (l : ℕ)
      omega)
  -- each base writes its own value register, reading only registers below them
  have hfresh : ∀ (τ : Fin k → List Bool) (l : Fin b),
      composeFin b Fb τ ⟨free + 3 + l, by have := l.isLt; omega⟩ = hbase l (τ ∘ params) :=
    composeFin_fresh (free + 3) b (by omega) Fb (fun l τ ↦ hbase l (τ ∘ params))
      (fun l τ τ' h ↦ congrArg (hbase l)
        (funext fun p ↦ h (params p) (by have := hparams p; omega)))
      hout (fun l τ r hr hne ↦ hframe l τ r (by omega) hne)
  intro σ
  -- the two updates lie above the parameters and above the registers of the last clause
  have hne : ∀ r : Fin k, r.val < free →
      Function.update (Function.update σ (⟨free, by omega⟩ : Fin k) (σ X).reverse)
        (⟨free + 1, by omega⟩ : Fin k) [] r = σ r := by
    intro r hr
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by change r.val ≠ free + 1; omega)),
      Function.update_of_ne (Fin.ne_of_val_ne (by change r.val ≠ free; omega))]
  refine ⟨?_, ?_, fun l ↦ ?_, fun r hr ↦ ?_⟩
  · rw [hbelow _ _ (by change free < free + 3; omega),
      Function.update_of_ne (Fin.ne_of_val_ne (by change free ≠ free + 1; omega)),
      Function.update_self]
  · rw [hbelow _ _ (by change free + 1 < free + 3; omega), Function.update_self]
  · rw [hfresh]
    exact congrArg (hbase l) (funext fun p ↦ hne (params p) (hparams p))
  · rw [hbelow _ _ (by omega)]
    exact hne r hr

end

end Geb.SizeBounded.Machine
