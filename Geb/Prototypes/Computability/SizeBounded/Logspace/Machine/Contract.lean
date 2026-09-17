/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.SeqFin

set_option doc.verso true in
/-!
# The input-reading program contract

A program of the logarithmic-space calculus reads the input tape, so its
transformer depends on the input and its precondition may too. The contract
here extends {name}`Geb.SizeBounded.Machine.Transforms` in three ways: the
transformer and the precondition take the input; the input head is at cell
{lit}`0`, the blank before the input, on entry and so on exit, since
{name}`Geb.SizeBounded.Machine.after` keeps it; and the bound on the
transformed valuation is asserted rather than assumed, so that a program
whose transformer keeps the bound only on the valuations its precondition
admits, a counter increment among them, has a contract. The step and length
bounds are functions of the input's length.

A contract of the input-independent calculus lifts to one here whose
precondition is the bound on the transformed valuation, and the contracts
compose under sequencing and the sequencing of a family, the composite's
precondition being each component's at the valuation it receives.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`TransformsIn` — the contract.
* {lit}`preFin` — the precondition of a sequenced family.

# Main statements

* {lit}`Transforms.toIn` — a contract of the input-independent calculus lifts.
* {lit}`TransformsIn.mono_pre`, {lit}`TransformsIn.mono_time`,
  {lit}`TransformsIn.congr` — the contract at a stronger precondition, a
  larger step bound, and a transformer equal where the precondition holds.
* {lit}`TransformsIn.seq`, {lit}`TransformsIn.idle`, {lit}`TransformsIn.seqFin`
  — sequencing two programs, the idle program, and a family.

# Tags

Turing machine, program, contract, input tape, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The contract: from a parked configuration in the initial state, the input
head at cell {lit}`0`, holding a valuation {lit}`σ` within {lit}`B` at the
input's length and satisfying the precondition, the transformed valuation is
within the bound and the machine runs within {lit}`T` at the input's length
to the parked halted configuration holding it. -/
@[expose] def TransformsIn {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (Pre : List Bool → (Fin k → List Bool) → Prop)
    (F : List Bool → (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ → ℕ) : Prop :=
  ∀ (input : List Bool) (cfg : Cfg k Bool State input) (σ : Fin k → List Bool),
    cfg.state = some tm.q₀ → Parked cfg → cfg.inputPos.val = 0 → Holds cfg σ → Pre input σ →
    Bounded σ (B input.length) →
    Bounded (F input σ) (B input.length) ∧
      ∃ t ≤ T input.length, RunsTo tm cfg (after cfg (F input σ)) t (B input.length)

/-- A contract of the input-independent calculus, at every length, lifts to a
contract whose precondition is the bound on the transformed valuation. -/
theorem _root_.Geb.SizeBounded.Machine.Transforms.toIn {k : ℕ} {State : Type}
    {tm : MultiTapeTM k Bool State} {F : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : ∀ n, Transforms tm F (T n) (B n)) :
    TransformsIn tm (fun input σ ↦ Bounded (F σ) (B input.length)) (fun _ ↦ F) T B := by
  intro input cfg σ hq hpark _ hσ hpre hB
  exact ⟨hpre, h input.length cfg σ hq hpark hσ hB hpre⟩

/-- The contract at a stronger precondition. -/
theorem TransformsIn.mono_pre {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {Pre Pre' : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : TransformsIn tm Pre F T B)
    (hpre : ∀ input σ, Bounded σ (B input.length) → Pre' input σ → Pre input σ) :
    TransformsIn tm Pre' F T B :=
  fun input cfg σ hq hpark hpos hσ hpre' hB ↦
    h input cfg σ hq hpark hpos hσ (hpre input σ hB hpre') hB

/-- The contract at a larger step bound. -/
theorem TransformsIn.mono_time {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T T' B : ℕ → ℕ}
    (h : TransformsIn tm Pre F T B) (hT : ∀ n, T n ≤ T' n) : TransformsIn tm Pre F T' B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨hFB, t, ht, r⟩ := h input cfg σ hq hpark hpos hσ hpre hB
  exact ⟨hFB, t, (ht.trans (hT _)), r⟩

/-- The contract at a transformer equal to the given one wherever the
precondition holds. -/
theorem TransformsIn.congr {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F F' : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : TransformsIn tm Pre F T B) (hF : ∀ input σ, Pre input σ → F input σ = F' input σ) :
    TransformsIn tm Pre F' T B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨hFB, t, ht, r⟩ := h input cfg σ hq hpark hpos hσ hpre hB
  rw [hF input σ hpre] at hFB r
  exact ⟨hFB, t, ht, r⟩

/-- Contracts compose: the composite transforms by the composite of the
transformers, its precondition being the first's at the valuation received
and the second's at the valuation the first produces. -/
theorem TransformsIn.seq {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {Q : MultiTapeTM k Bool S₂} {Pre₁ Pre₂ : List Bool → (Fin k → List Bool) → Prop}
    {F G : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T₁ T₂ B : ℕ → ℕ}
    (hP : TransformsIn P Pre₁ F T₁ B) (hQ : TransformsIn Q Pre₂ G T₂ B) :
    TransformsIn (seq P Q) (fun input σ ↦ Pre₁ input σ ∧ Pre₂ input (F input σ))
      (fun input σ ↦ G input (F input σ)) (fun n ↦ T₁ n + T₂ n) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  rw [liftL_start P Q cfg hq]
  set cfg₀ := { cfg with state := some P.q₀ }
  obtain ⟨hFB, t₁, ht₁, r₁⟩ := hP input cfg₀ σ rfl hpark hpos hσ hpre.1 hB
  obtain ⟨hGB, t₂, ht₂, r₂⟩ := hQ input { after cfg₀ (F input σ) with state := some Q.q₀ }
    (F input σ) rfl hpark hpos (fun i ↦ rfl) hpre.2 hFB
  refine ⟨hGB, t₁ + t₂, ?_, ?_⟩
  · change t₁ + t₂ ≤ T₁ input.length + T₂ input.length
    omega
  rw [show after (liftL Q cfg₀) (G input (F input σ)) =
      liftR (after { after cfg₀ (F input σ) with state := some Q.q₀ } (G input (F input σ)))
    from by apply Cfg.ext <;> rfl]
  exact r₁.seq r₂

/-- The idle program transforms by the identity in one step. -/
theorem TransformsIn.idle {k : ℕ} (B : ℕ → ℕ) :
    TransformsIn (idle (k := k)) (fun _ _ ↦ True) (fun _ σ ↦ σ) (fun _ ↦ 1) B :=
  TransformsIn.mono_pre (Transforms.toIn fun n ↦ idle_transforms (B n)) fun _ _ hB _ ↦ hB

/-- The precondition of a sequenced family: each member's at the valuation the
members before it produce. -/
@[expose] def preFin {k : ℕ} : (m : ℕ) → (Fin m → List Bool → (Fin k → List Bool) → Prop) →
    (Fin m → List Bool → (Fin k → List Bool) → Fin k → List Bool) →
    List Bool → (Fin k → List Bool) → Prop :=
  Nat.rec (fun _ _ _ _ ↦ True) fun m ih Pre F input σ ↦
    ih (fun l ↦ Pre l.castSucc) (fun l ↦ F l.castSucc) input σ ∧
      Pre (Fin.last m) input (composeFin m (fun l ↦ F l.castSucc input) σ)

/-- The precondition of the empty family. -/
theorem preFin_zero {k : ℕ} (Pre : Fin 0 → List Bool → (Fin k → List Bool) → Prop)
    (F : Fin 0 → List Bool → (Fin k → List Bool) → Fin k → List Bool) (input : List Bool)
    (σ : Fin k → List Bool) : preFin 0 Pre F input σ = True := rfl

/-- The precondition of a family of length {lit}`m + 1`. -/
theorem preFin_succ {k m : ℕ} (Pre : Fin (m + 1) → List Bool → (Fin k → List Bool) → Prop)
    (F : Fin (m + 1) → List Bool → (Fin k → List Bool) → Fin k → List Bool) (input : List Bool)
    (σ : Fin k → List Bool) :
    preFin (m + 1) Pre F input σ =
      (preFin m (fun l ↦ Pre l.castSucc) (fun l ↦ F l.castSucc) input σ ∧
        Pre (Fin.last m) input (composeFin m (fun l ↦ F l.castSucc input) σ)) := rfl

/-- Sequencing a family of programs transforms by the composite of their
transformers, in {lit}`m * T + 1` steps for a family of {lit}`m` programs each
within {lit}`T`. -/
theorem TransformsIn.seqFin {k : ℕ} (B T : ℕ → ℕ) : ∀ (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i))
    (Pre : Fin m → List Bool → (Fin k → List Bool) → Prop)
    (F : Fin m → List Bool → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i, TransformsIn (P i) (Pre i) (F i) T B) →
    TransformsIn (seqFin m S P).2 (preFin m Pre F)
      (fun input σ ↦ composeFin m (fun l ↦ F l input) σ) (fun n ↦ m * T n + 1) B :=
  Nat.rec
    (fun _ _ _ F _ ↦ by
      refine TransformsIn.mono_time (TransformsIn.congr (TransformsIn.idle B) ?_) ?_
      · exact fun input σ _ ↦ (composeFin_zero (fun l ↦ F l input) σ).symm
      · intro n
        exact Nat.le_add_left 1 _)
    (fun m ih S P Pre F hP ↦ by
      refine TransformsIn.congr (TransformsIn.mono_time (TransformsIn.seq
        (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ Pre i.castSucc)
          (fun i ↦ F i.castSucc) (fun i ↦ hP i.castSucc)) (hP (Fin.last m))) ?_) ?_
      · intro n
        rw [Nat.succ_mul]
        omega
      · exact fun input σ _ ↦ (composeFin_succ (fun l ↦ F l input) σ).symm)

end

end Geb.SizeBounded.Logspace.Machine
