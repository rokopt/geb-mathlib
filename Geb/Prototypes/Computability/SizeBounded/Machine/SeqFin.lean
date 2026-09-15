/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true

/-!
# Sequencing a family

{lit}`seqFin` sequences a family of machines indexed by {lit}`Fin m`, in
index order, by recursion on {lit}`m` via {lit}`seq`; the empty family
sequences to {lit}`idle`, the machine that halts at once doing nothing.
{lit}`composeFin` composes a family of transformers in the same order, and
{lit}`Transforms.seqFin` shows the sequenced family transforms by the
composite of the family's transformers.

# Main definitions

* {lit}`idle` — the machine that halts at once, doing nothing.
* {lit}`seqFin` — sequencing a family of machines indexed by {lit}`Fin m`.
* {lit}`seqFinEnum` — a choice-free enumeration of a sequenced family's
  state.
* {lit}`composeFin` — the composite of a family of transformers.

# Main statements

* {lit}`idle_transforms` — {lit}`idle` transforms by the identity in one
  step.
* {lit}`seqFin_zero`, {lit}`seqFin_succ` — the recursive equations of
  {lit}`seqFin`.
* {lit}`composeFin_zero`, {lit}`composeFin_succ` — the recursive equations of
  {lit}`composeFin`.
* {lit}`composeFin_bounded` — a composite of bound-preserving transformers
  preserves the bound.
* {lit}`Transforms.seqFin` — the sequenced family transforms by the
  composite of the family's transformers.

# Tags

Turing machine, sequencing, composition, recursion
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open scoped FinEnum

public section

/-- The machine that halts at once, doing nothing. -/
@[expose] def idle {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- {name}`idle` transforms by the identity in one step. -/
theorem idle_transforms {k : ℕ} (B : ℕ) : Transforms (idle (k := k)) (fun σ ↦ σ) 1 B := by
  intro _ cfg σ hq hpark hσ hB _
  have hstep : idle.configs cfg 1 = after cfg σ := by
    have e1 : idle.configs cfg 1 = idle.step (idle.configs cfg 0) :=
      configs_succ_eq_step' (tm := idle) (cfg := cfg) (t := 0)
    rw [e1, configs_zero, step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = (after cfg σ).inputPos
      rw [moveInputPos_zero, after_inputPos]
    · dsimp only
      funext i
      exact hσ i
    · change (fun i ↦ cfg.workTapePos i + (0 : ℤ)) = (after cfg σ).workTapePos
      funext i
      rw [add_zero, after_workTapePos]
  refine ⟨1, le_refl 1, ⟨⟨⟨?_, hstep, ?_⟩, ?_⟩, ?_⟩⟩
  · intro t' ht'
    have ht0 : t' = 0 := by omega
    rw [ht0, configs_zero, hq]
    exact Option.some_ne_none _
  · intro t' ht' i
    have : t' = 0 ∨ t' = 1 := by omega
    rcases this with h0 | h1
    · rw [h0, configs_zero, hpark i]
      constructor <;> omega
    · rw [h1, hstep, after_workTapePos, hpark i]
      constructor <;> omega
  · have e1 : idle.outputString cfg 1 = idle.outputString cfg 0 ++
        (idle.outputSymbol (idle.configs cfg 0)).toList :=
      outputString_succ idle cfg 0
    rw [e1, configs_zero]
    have hout : idle.outputSymbol cfg = none := by
      unfold outputSymbol
      rw [hq]
      rfl
    rw [hout]
    rfl
  · rfl

/-- Sequencing a family of machines indexed by {lit}`Fin m`, in index order,
by recursion on {lit}`m`. The state is an iterated binary sum, so that the
choice-free {lit}`FinEnum` instance on sums applies. -/
@[expose] def seqFin {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    ((i : Fin m) → MultiTapeTM k Bool (S i)) → Σ S' : Type, MultiTapeTM k Bool S' :=
  Nat.rec (fun _ _ ↦ ⟨Unit, idle⟩)
    (fun m ih S P ↦ ⟨(ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1 ⊕ S (Fin.last m),
      seq (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).2 (P (Fin.last m))⟩)

/-- The empty family sequences to {name}`idle`. -/
theorem seqFin_zero {k : ℕ} (S : Fin 0 → Type) (P : (i : Fin 0) → MultiTapeTM k Bool (S i)) :
    seqFin 0 S P = ⟨Unit, idle⟩ := rfl

/-- A family of length {lit}`m + 1` sequences its first {lit}`m` members, then
its last. -/
theorem seqFin_succ {k m : ℕ} (S : Fin (m + 1) → Type)
    (P : (i : Fin (m + 1)) → MultiTapeTM k Bool (S i)) :
    seqFin (m + 1) S P =
      ⟨(seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1 ⊕ S (Fin.last m),
        seq (seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).2 (P (Fin.last m))⟩ := rfl

/-- A choice-free enumeration of a sequenced family's state. -/
@[expose, instance_reducible] def seqFinEnum {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    (P : (i : Fin m) → MultiTapeTM k Bool (S i)) → ((i : Fin m) → FinEnum (S i)) →
    FinEnum (seqFin m S P).1 :=
  Nat.rec (fun _ _ _ ↦ FinEnum.unit)
    (fun m ih S P E ↦
      @FinEnum.finSum _ _ (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ E i.castSucc))
        (E (Fin.last m)))

/-- The composite of a family of transformers, in index order. -/
@[expose] def composeFin {k : ℕ} : (m : ℕ) →
    (Fin m → (Fin k → List Bool) → Fin k → List Bool) → (Fin k → List Bool) → Fin k → List Bool :=
  Nat.rec (fun _ σ ↦ σ) (fun m ih F σ ↦ F (Fin.last m) (ih (fun i ↦ F i.castSucc) σ))

/-- The empty composite is the identity. -/
theorem composeFin_zero {k : ℕ} (F : Fin 0 → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) : composeFin 0 F σ = σ := rfl

/-- The composite of {lit}`m + 1` transformers applies the last after the
first {lit}`m`. -/
theorem composeFin_succ {k m : ℕ} (F : Fin (m + 1) → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) :
    composeFin (m + 1) F σ = F (Fin.last m) (composeFin m (fun i ↦ F i.castSucc) σ) := rfl

/-- A composite of bound-preserving transformers preserves the bound. -/
theorem composeFin_bounded {k : ℕ} (B : ℕ) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    ∀ σ, Bounded σ B → Bounded (composeFin m F σ) B :=
  Nat.rec
    (fun F _ σ hσ ↦ by rw [composeFin_zero]; exact hσ)
    (fun m ih F hF σ hσ ↦ by
      rw [composeFin_succ]
      exact hF (Fin.last m) _ (ih (fun i ↦ F i.castSucc) (fun i ↦ hF i.castSucc) σ hσ))

/-- Sequencing a family of programs transforms by the composite of their
transformers, in {lit}`m * T + 1` steps for a family of {lit}`m` programs
each within {lit}`T`. -/
theorem Transforms.seqFin {k : ℕ} (B T : ℕ) : ∀ (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i))
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i, Transforms (P i) (F i) T B) → (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    Transforms (seqFin m S P).2 (composeFin m F) (m * T + 1) B :=
  Nat.rec
    (fun _ _ F _ _ ↦
      Transforms.mono_time
        (Transforms.congr (idle_transforms B) (fun σ ↦ (composeFin_zero F σ).symm))
        (by omega))
    (fun m ih S P F hP hF ↦
      Transforms.congr
        (Transforms.mono_time
          (Transforms.seq
            (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ F i.castSucc)
              (fun i ↦ hP i.castSucc) (fun i σ ↦ hF i.castSucc σ))
            (hP (Fin.last m))
            (composeFin_bounded B m (fun i ↦ F i.castSucc) (fun i ↦ hF i.castSucc)))
          (by rw [Nat.succ_mul]; omega))
        (fun σ ↦ (composeFin_succ F σ).symm))

end

end Geb.SizeBounded.Machine
