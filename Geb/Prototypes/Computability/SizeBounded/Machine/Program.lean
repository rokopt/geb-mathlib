/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Register
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Runs and the program contract

A reach: from a configuration a machine arrives at another in a given number
of steps, halted at none of the earlier ones, emitting nothing, every head
within the interval from {lit}`-1` to a bound. A run: a reach whose target is
halted. The contract of a program of the calculus: from any parked
configuration holding a register valuation, a run to the parked halted
configuration holding the valuation's image under the program's transformer,
within a step bound, whenever the valuation and its image are within the
length bound. The transformer describes every register, so that sequencing
two programs composes their transformers.

The no-earlier-halt clause is what sequencing needs: the composite machine
hands over to its second component at the first halting step of its first, so
a run's step count must be that step.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs`,
{name}`Turing.MultiTapeTM.outputString` and
{name}`Turing.MultiTapeTM.spaceUsedByTape`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.MultiTapeTM.Cfg.inputSymbol`
or mathlib's {name}`Finset.image`.

# Main definitions

* {lit}`Reaches` — a reach between two configurations.
* {lit}`RunsTo` — a reach to a halted configuration.
* {lit}`after` — the parked halted configuration holding a valuation.
* {lit}`Transforms` — the program contract.

# Main statements

* {lit}`step_of_state` — a step from a known state, naming {lit}`tr`.
* {lit}`Reaches.trans` — reaches compose.
* {lit}`Reaches.mono`, {lit}`RunsTo.mono` — a larger head bound.
* {lit}`RunsTo.halt_configs` — after a run the machine stays put.
* {lit}`RunsTo.spaceUsedByTape_le` — a run's visited cells per tape are at
  most the bound plus two.
* {lit}`Transforms.mono_time`, {lit}`Transforms.congr` — the contract at a
  larger step bound and at a pointwise equal transformer.

# Tags

Turing machine, program, contract, space complexity
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- A machine's step from a known state, in the form that names {lit}`tr`. Generic
in the symbol type: at a fixed symbol type the statement's {lit}`match` compiles
to a matcher of its own and the proof by {lit}`rfl` fails. -/
theorem step_of_state {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    tm.step cfg =
      { state := (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).q'
        inputPos := moveInputPos cfg.inputPos
          (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove
        workTapes := fun i ↦
          match ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).1 with
          | none => cfg.workTapes i
          | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
        workTapePos := fun i ↦ cfg.workTapePos i +
          ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).2 } := by
  unfold step
  rw [hq]
  rfl

/-- From {lit}`cfg`, {lit}`tm` arrives at {lit}`cfg'` at step {lit}`t`, halted
at no earlier step, emitting nothing, every head within {lit}`[-1, B]`
throughout. -/
structure Reaches {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop where
  /-- No step before {lit}`t` is halted. -/
  live : ∀ t' < t, (tm.configs cfg t').state ≠ none
  /-- The configuration at step {lit}`t`. -/
  configs_eq : tm.configs cfg t = cfg'
  /-- Nothing is emitted. -/
  output : tm.outputString cfg t = []
  /-- Every head stays within {lit}`[-1, B]`. -/
  pos : ∀ t' ≤ t, ∀ i, -1 ≤ (tm.configs cfg t').workTapePos i ∧
    (tm.configs cfg t').workTapePos i ≤ B

/-- A reach to a halted configuration. -/
structure RunsTo {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop extends Reaches tm cfg cfg' t B where
  /-- The target is halted. -/
  halted : cfg'.state = none

/-- Reaches compose. -/
theorem Reaches.trans {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg₁ cfg₂ : Cfg k Bool State input} {t₁ t₂ B : ℕ}
    (h₁ : Reaches tm cfg cfg₁ t₁ B) (h₂ : Reaches tm cfg₁ cfg₂ t₂ B) :
    Reaches tm cfg cfg₂ (t₁ + t₂) B where
  configs_eq := by rw [configs_add, h₁.configs_eq, h₂.configs_eq]
  live := by
    intro t' ht'
    by_cases h : t' < t₁
    · exact h₁.live t' h
    · have ht : t' = t₁ + (t' - t₁) := by omega
      rw [ht, configs_add, h₁.configs_eq]
      exact h₂.live (t' - t₁) (by omega)
  output := by simp [outputString_add_eq_append, h₁.output, h₁.configs_eq, h₂.output]
  pos := by
    intro t' ht' i
    by_cases h : t' < t₁
    · exact h₁.pos t' (le_of_lt h) i
    · have ht : t' = t₁ + (t' - t₁) := by omega
      rw [ht, configs_add, h₁.configs_eq]
      exact h₂.pos (t' - t₁) (by omega) i

/-- A reach within one bound is a reach within any larger bound. -/
theorem Reaches.mono {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B B' : ℕ}
    (h : Reaches tm cfg cfg' t B) (hB : B ≤ B') : Reaches tm cfg cfg' t B' where
  live := h.live
  configs_eq := h.configs_eq
  output := h.output
  pos := fun t' ht' i ↦ ⟨(h.pos t' ht' i).1, (h.pos t' ht' i).2.trans (by omega)⟩

/-- A run within one bound is a run within any larger bound. -/
theorem RunsTo.mono {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B B' : ℕ}
    (h : RunsTo tm cfg cfg' t B) (hB : B ≤ B') : RunsTo tm cfg cfg' t B' where
  toReaches := h.toReaches.mono hB
  halted := h.halted

/-- After a run the machine stays in the halted configuration. -/
theorem RunsTo.halt_configs {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B : ℕ}
    (h : RunsTo tm cfg cfg' t B) (s : ℕ) : tm.configs cfg (t + s) = cfg' := by
  rw [configs_add, h.configs_eq]
  exact configs_of_halts _ h.halted

/-- Over a run the head of each tape visits at most {lit}`B + 2` cells. -/
theorem RunsTo.spaceUsedByTape_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {t B : ℕ}
    (h : RunsTo tm cfg cfg' t B) (i : Fin k) : tm.spaceUsedByTape cfg t i ≤ B + 2 := by
  have hsub : tm.visitedByTapeHead cfg t i ⊆ Finset.Icc (-1 : ℤ) B := by
    intro z hz
    obtain ⟨t', ht', rfl⟩ := mem_visitedByTapeHead.mp hz
    exact Finset.mem_Icc.mpr (h.pos t' (by omega) i)
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  unfold spaceUsedByTape
  omega

/-- The halted configuration with the heads and input head of {lit}`cfg` and
the tapes holding {lit}`σ`. -/
@[expose] def after {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : Cfg k Bool State input :=
  { cfg with state := none, workTapes := fun i ↦ tapeOf (σ i) }

/-- {name}`after` holds the valuation. -/
@[simp] theorem after_workTapes {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) (i : Fin k) :
    (after cfg σ).workTapes i = tapeOf (σ i) := rfl

/-- {name}`after` keeps the heads. -/
@[simp] theorem after_workTapePos {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) :
    (after cfg σ).workTapePos = cfg.workTapePos := rfl

/-- {name}`after` keeps the input head. -/
@[simp] theorem after_inputPos {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) :
    (after cfg σ).inputPos = cfg.inputPos := rfl

/-- {name}`after` is halted. -/
@[simp] theorem after_state {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : (after cfg σ).state = none := rfl

/-- The program contract: from a parked configuration in the initial state
holding a valuation {lit}`σ` within {lit}`B`, with {lit}`F σ` within {lit}`B`,
a run within {lit}`T` steps to the parked halted configuration holding
{lit}`F σ`. The bound on {lit}`F σ` is an assumption; the compiler discharges
it from non-size-increase. -/
@[expose] def Transforms {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (F : (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ) : Prop :=
  ∀ {input : List Bool} (cfg : Cfg k Bool State input) (σ : Fin k → List Bool),
    cfg.state = some tm.q₀ → Parked cfg → Holds cfg σ → Bounded σ B → Bounded (F σ) B →
    ∃ t ≤ T, RunsTo tm cfg (after cfg (F σ)) t B

/-- The contract at a larger step bound. -/
theorem Transforms.mono_time {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {F : (Fin k → List Bool) → Fin k → List Bool} {T T' B : ℕ}
    (h : Transforms tm F T B) (hT : T ≤ T') : Transforms tm F T' B := by
  intro _ cfg σ h1 h2 h3 h4 h5
  obtain ⟨t, ht, r⟩ := h cfg σ h1 h2 h3 h4 h5
  exact ⟨t, by omega, r⟩

/-- The contract at a pointwise equal transformer. -/
theorem Transforms.congr {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {F F' : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ}
    (h : Transforms tm F T B) (hF : ∀ σ, F σ = F' σ) : Transforms tm F' T B := by
  intro _ cfg σ h1 h2 h3 h4 h5
  obtain ⟨t, ht, r⟩ := h cfg σ h1 h2 h3 h4 (by rw [hF]; exact h5)
  exact ⟨t, ht, hF σ ▸ r⟩

end

end Geb.SizeBounded.Machine
