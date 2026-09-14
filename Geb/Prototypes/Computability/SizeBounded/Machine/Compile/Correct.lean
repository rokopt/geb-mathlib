/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Bound

set_option doc.verso true

/-!
# Correctness of the compiled programs

{lit}`Correct` is the contract a compiled expression's program meets: at every
admissible allocation of registers it transforms valuations by a function that
writes the expression's value into the output register, leaves the registers
below the first free one otherwise unchanged, and preserves the length bound,
within the step count {name}`Geb.SizeBounded.Machine.stepBound` reads off the
syntax. {lit}`CorrectSigma` states the same of an indexed pair whose indices
agree, the form the fold of {name}`Geb.SizeBounded.Machine.compile` produces.

The three base forms are the primitives, and their contracts are
{name}`Geb.SizeBounded.Machine.const_transforms`,
{name}`Geb.SizeBounded.Machine.copy_transforms` and
{name}`Geb.SizeBounded.Machine.sbs_transforms`: in each the transformer is an
update of the output register, so the frame and bound clauses come from the
equations of {name}`Function.update`.

# Main definitions

* {lit}`Correct` — the contract of a compiled expression of a given arity.
* {lit}`CorrectSigma` — the contract of an indexed pair, the indices agreeing.

# Main statements

* {lit}`Correct.transport` — the contract transports along an equality of
  arities.
* {lit}`correct_const`, {lit}`correct_proj`, {lit}`correct_sbs` — the three
  base forms meet the contract.

# Tags

Turing machine, compilation, correctness, register, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem transport)
open Geb.SizeBounded (Direction rc evalValue nsiValue sbsSem)

public section

/-- The compiled program of arity {lit}`n` computes {lit}`f` with constant
{lit}`K` and step bound {lit}`Tf`: from every admissible allocation (an injective
environment below the first free register, an output register below it and
outside the environment) and every length bound at least {lit}`K`, its machine
transforms valuations by a function that puts the value in the output register,
leaves every other register below the first free one unchanged, and preserves the
bound. -/
@[expose] def Correct {k n : ℕ} (p : Compiled k n) (f : Sem n) (K : ℕ) (Tf : ℕ → ℕ) : Prop :=
  ∀ (env : Fin n → Fin k) (out : Fin k) (free : ℕ) (hfree : free + p.regs ≤ k),
    Function.Injective env → (∀ i, (env i).val < free) → out.val < free →
    (∀ i, env i ≠ out) → ∀ B, K ≤ B →
    ∃ F : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (p.prog env out free hfree).tm F (Tf B) B ∧
      (∀ σ, F σ out = f (σ ∘ env)) ∧
      (∀ σ (i : Fin k), i.val < free → i ≠ out → F σ i = σ i) ∧
      (∀ σ, Bounded σ B → Bounded (F σ) B)

/-- Correctness of an indexed pair, the indices agreeing. -/
@[expose] def CorrectSigma {k : ℕ} (p : Σ i, Compiled k i) (m : Σ i, Sem i) (K : ℕ)
    (Tf : ℕ → ℕ) : Prop :=
  ∃ h : p.1 = m.1, Correct (transportP h p.2) m.2 K Tf

/-- Correctness transports along an equality of arities. -/
theorem Correct.transport {k i j : ℕ} (h : i = j) {p : Compiled k i} {f : Sem i} {K : ℕ}
    {Tf : ℕ → ℕ} (hp : Correct p f K Tf) : Correct (transportP h p) (transport h f) K Tf := by
  subst h
  exact hp

/-- A constant node is correct with its length as constant. -/
theorem correct_const {k n : ℕ} (w : List Bool) (c : Direction (.const n w) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.const n w) b) (s : Direction (.const n w) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.const n w) b) (K : Direction (.const n w) → ℕ)
    (Tf : Direction (.const n w) → ℕ → ℕ) :
    Correct (compileValue (.const n w) c h) (evalValue (.const n w) s hs)
      (nsiValue (.const n w) K) (stepValue (.const n w) Tf) := by
  intro _ out _ _ _ _ _ _ B hK
  refine ⟨fun σ ↦ Function.update σ out w, const_transforms w out B, fun σ ↦ ?_,
    fun σ i _ hi ↦ Function.update_of_ne hi _ _, fun σ hσ i ↦ ?_⟩
  · exact Function.update_self ..
  · change (Function.update σ out w i).length ≤ B
    rcases eq_or_ne i out with rfl | hi
    · rw [Function.update_self]
      exact hK
    · rw [Function.update_of_ne hi]
      exact hσ i

/-- A projection node is correct with constant zero. -/
theorem correct_proj {k n : ℕ} (i : Fin n) (c : Direction (.proj n i) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.proj n i) b) (s : Direction (.proj n i) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.proj n i) b) (K : Direction (.proj n i) → ℕ)
    (Tf : Direction (.proj n i) → ℕ → ℕ) :
    Correct (compileValue (.proj n i) c h) (evalValue (.proj n i) s hs)
      (nsiValue (.proj n i) K) (stepValue (.proj n i) Tf) := by
  intro env out _ _ _ _ _ hne B _
  refine ⟨fun σ ↦ Function.update σ out (σ (env i)), copy_transforms (env i) out (hne i) B,
    fun σ ↦ ?_, fun σ l _ hl ↦ Function.update_of_ne hl _ _, fun σ hσ l ↦ ?_⟩
  · exact Function.update_self ..
  · change (Function.update σ out (σ (env i)) l).length ≤ B
    rcases eq_or_ne l out with rfl | hl
    · rw [Function.update_self]
      exact hσ (env i)
    · rw [Function.update_of_ne hl]
      exact hσ l

/-- A successor node is correct with constant zero. -/
theorem correct_sbs {k : ℕ} (b : Bool) (c : Direction (.sbs b) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.sbs b) d) (s : Direction (.sbs b) → Σ i, Sem i)
    (hs : ∀ d, (s d).1 = rc (.sbs b) d) (K : Direction (.sbs b) → ℕ)
    (Tf : Direction (.sbs b) → ℕ → ℕ) :
    Correct (compileValue (.sbs b) c h) (evalValue (.sbs b) s hs)
      (nsiValue (.sbs b) K) (stepValue (.sbs b) Tf) := by
  intro env out _ _ hinj _ _ hne B _
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hxy : env 0 ≠ env 1 := fun heq ↦ h01 (hinj heq)
  refine ⟨fun σ ↦ Function.update σ out (sbsSem b (σ (env 0)) (σ (env 1))),
    sbs_transforms b (env 0) (env 1) out hxy (hne 0) (hne 1) B,
    fun σ ↦ ?_, fun σ l _ hl ↦ Function.update_of_ne hl _ _, fun σ hσ l ↦ ?_⟩
  · exact Function.update_self ..
  · change (Function.update σ out (sbsSem b (σ (env 0)) (σ (env 1))) l).length ≤ B
    rcases eq_or_ne l out with rfl | hl
    · rw [Function.update_self]
      have h0 := hσ (env 0)
      have h1 := hσ (env 1)
      unfold sbsSem
      split
      · rw [List.length_cons]
        omega
      · omega
    · rw [Function.update_of_ne hl]
      exact hσ l

end

end Geb.SizeBounded.Machine
