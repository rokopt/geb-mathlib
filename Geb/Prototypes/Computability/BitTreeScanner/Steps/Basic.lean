/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Cfg

set_option doc.verso true

/-!
# The two-pass tree scanner's steps and runs

{name}`Geb.BitTreeScanner.bitTreeScanner`'s single steps at each shape of
transition, and runs: a run is a number of steps from one configuration to
another emitting nothing, every configuration along it keeping its heads
within the space bound. Runs compose, so the machine's computation is
assembled from single steps and from inner recursions over intermediate
closed forms without a rewrite chain, and the space bound is carried along.

## Main definitions

* {lit}`Geb.BitTreeScanner.Run` — a run between two configurations.

## Main statements

* {lit}`Geb.BitTreeScanner.inputSymbol_of_inputPos`,
  {lit}`Geb.BitTreeScanner.inputSymbol_end`,
  {lit}`Geb.BitTreeScanner.inputSymbol_start` — the input symbol at any
  configuration whose head is past a prefix, short of the input's end, at
  it, or at its start.
* {lit}`Geb.BitTreeScanner.step_advance`, {lit}`Geb.BitTreeScanner.step_stay`,
  {lit}`Geb.BitTreeScanner.step_retreat`, {lit}`Geb.BitTreeScanner.step_halt`
  — a step at each shape of transition.
* {lit}`Geb.BitTreeScanner.run_step`, {lit}`Geb.BitTreeScanner.run_seq`,
  {lit}`Geb.BitTreeScanner.run_family` — a run of one step, two runs in
  sequence, and the run along a family of configurations each the step of
  the last.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the machine's behaviour under {name}`Turing.MultiTapeTM.step`,
{name}`Turing.MultiTapeTM.configs` and {name}`Turing.MultiTapeTM.outputString`,
and its statements read the input through
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`; each of those depends on
{lit}`Classical.choice` through Cslib's {lit}`Cfg.inputSymbol` and
{name}`Turing.MultiTapeTM.inputSymbolInner`, so nothing here can be stated
choice-free; the closed forms the steps land on and their head bounds, which
can, are {lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Cfg`'s.

## Tags

Turing machine, transition, run, space bound
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner
open Geb.TreeScanner (step_of_state)

section InputSymbol

variable (w : List Bool) (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb))

/-- A configuration whose input head is past a prefix short of the input's end
reads the bit at the prefix's length. -/
theorem inputSymbol_of_inputPos (k : ℕ) (h : k < w.length) (hpos : cfg.inputPos.val = k + 1) :
    cfg.inputSymbol = some (boolEmb w[k]) := by
  have hi := inputSymbolInner (cfg := cfg) k (by rw [hpos]; omega)
    (by rw [List.length_map]; exact h)
  rw [hi, List.getElem_map]

/-- A configuration whose input head is past the whole input reads blank. This
takes {name}`Turing.MultiTapeTM.Cfg.inputSymbol`'s second guard, an equality at
{lit}`ℕ`. -/
theorem inputSymbol_end (hpos : cfg.inputPos.val = w.length + 1) : cfg.inputSymbol = none := by
  have hend : (cfg.inputPos : ℕ) = (w.map boolEmb).length + 1 := by
    rw [hpos, List.length_map]
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

/-- A configuration whose input head is before the input reads blank. -/
theorem inputSymbol_start (hpos : cfg.inputPos.val = 0) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  rw [dite_eq_left (Fin.ext hpos)]

end InputSymbol

section Step

variable {input : List (Fin 4)}

/-- A step whose transition has the given successor state, input move and
actions and emits nothing. -/
theorem step_next (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q q' : Fin stateCount)
    (m : SignType) (a₀ a₁ a₂ : Act) (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols =
      { inputMove := m, workActions := ![a₀, a₁, a₂], outS := none, q' := some q' }) :
    bitTreeScanner.step cfg = next cfg q' m a₀ a₁ a₂ ∧
      bitTreeScanner.outputSymbol cfg = none := by
  obtain ⟨o₀, m₀⟩ := a₀
  obtain ⟨o₁, m₁⟩ := a₁
  obtain ⟨o₂, m₂⟩ := a₂
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    refine Cfg.ext rfl rfl ?_ ?_
    · funext i
      match i with
      | 0 => cases o₀ <;> rfl
      | 1 => cases o₁ <;> rfl
      | 2 => cases o₂ <;> rfl
    · funext i
      match i with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = none
    rw [htr]

/-- A step whose transition reads a bit: the input head advances, each tape
takes its action, nothing is emitted. -/
theorem step_advance (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q q' : Fin stateCount)
    (a₀ a₁ a₂ : Act) (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = advance q' a₀ a₁ a₂) :
    bitTreeScanner.step cfg = next cfg q' 1 a₀ a₁ a₂ ∧
      bitTreeScanner.outputSymbol cfg = none :=
  step_next cfg q q' 1 a₀ a₁ a₂ hq htr

/-- A step whose transition works without reading: the input head stays, each
tape takes its action, nothing is emitted. -/
theorem step_stay (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q q' : Fin stateCount)
    (a₀ a₁ a₂ : Act) (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = stay q' a₀ a₁ a₂) :
    bitTreeScanner.step cfg = next cfg q' 0 a₀ a₁ a₂ ∧
      bitTreeScanner.outputSymbol cfg = none :=
  step_next cfg q q' 0 a₀ a₁ a₂ hq htr

/-- A step whose transition moves back over the input: the input head
retreats, each tape takes its action, nothing is emitted. -/
theorem step_retreat (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q q' : Fin stateCount)
    (a₀ a₁ a₂ : Act) (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = retreat q' a₀ a₁ a₂) :
    bitTreeScanner.step cfg = next cfg q' (-1) a₀ a₁ a₂ ∧
      bitTreeScanner.outputSymbol cfg = none :=
  step_next cfg q q' (-1) a₀ a₁ a₂ hq htr

/-- A step whose transition resolves to a halting step halts the machine, keeps
the heads and emits the halting step's symbol. -/
theorem step_halt (cfg : Cfg 3 (Fin 4) (Fin stateCount) input) (q : Fin stateCount)
    (hq : cfg.state = some q) (b : Fin 4)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = halt b) :
    (bitTreeScanner.step cfg).state = none ∧
      (bitTreeScanner.step cfg).workTapePos = cfg.workTapePos ∧
      bitTreeScanner.outputSymbol cfg = some b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    rfl
  · rw [step_of_state _ _ q hq, htr]
    funext i
    match i with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 => exact add_zero _
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = some b
    rw [htr]
    rfl

end Step

section Run

variable (w : List Bool)

/-- A run of {lit}`m` steps from one configuration to another: the
configuration reached, nothing emitted, and the heads within the bound at
every step. -/
def Run (cfg₁ cfg₂ : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (m : ℕ) : Prop :=
  bitTreeScanner.configs cfg₁ m = cfg₂ ∧ bitTreeScanner.outputString cfg₁ m = [] ∧
    ∀ j ≤ m, HeadsLE w (bitTreeScanner.configs cfg₁ j)

variable {w}

/-- The empty run. -/
theorem run_zero (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (h : HeadsLE w cfg) :
    Run w cfg cfg 0 :=
  ⟨configs_zero, rfl, fun j hj ↦ by rw [Nat.le_zero.mp hj, configs_zero]; exact h⟩

/-- A run of one step: the step's configuration, and nothing emitted. -/
theorem run_step (cfg₁ cfg₂ : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb))
    (h : bitTreeScanner.step cfg₁ = cfg₂ ∧ bitTreeScanner.outputSymbol cfg₁ = none)
    (h₁ : HeadsLE w cfg₁) (h₂ : HeadsLE w cfg₂) : Run w cfg₁ cfg₂ 1 := by
  refine ⟨h.1, ?_, ?_⟩
  · change bitTreeScanner.outputString cfg₁ (0 + 1) = []
    rw [outputString_succ, configs_zero, h.2]
    rfl
  · intro j hj
    match j with
    | 0 => rw [configs_zero]; exact h₁
    | 1 => rw [show bitTreeScanner.configs cfg₁ 1 = cfg₂ from h.1]; exact h₂

/-- Two runs in sequence. -/
theorem run_seq (cfg₁ cfg₂ cfg₃ : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (m n : ℕ)
    (h₁ : Run w cfg₁ cfg₂ m) (h₂ : Run w cfg₂ cfg₃ n) : Run w cfg₁ cfg₃ (m + n) := by
  obtain ⟨hc₁, ho₁, hh₁⟩ := h₁
  obtain ⟨hc₂, ho₂, hh₂⟩ := h₂
  refine ⟨by rw [configs_add, hc₁, hc₂], ?_, ?_⟩
  · rw [outputString_add_eq_append, ho₁, hc₁, ho₂]
    rfl
  · intro j hj
    by_cases hjm : j ≤ m
    · exact hh₁ j hjm
    · rw [show j = m + (j - m) by omega, configs_add, hc₁]
      exact hh₂ (j - m) (by omega)

/-- The run along a family of configurations, each the step of the last,
emitting nothing, with heads within the bound. -/
theorem run_family (f : ℕ → Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (n : ℕ)
    (hstep : ∀ i, i < n →
      bitTreeScanner.step (f i) = f (i + 1) ∧ bitTreeScanner.outputSymbol (f i) = none)
    (hheads : ∀ i, i ≤ n → HeadsLE w (f i)) : Run w (f 0) (f n) n :=
  Nat.rec (motive := fun n ↦ (∀ i, i < n →
      bitTreeScanner.step (f i) = f (i + 1) ∧ bitTreeScanner.outputSymbol (f i) = none) →
      (∀ i, i ≤ n → HeadsLE w (f i)) → Run w (f 0) (f n) n)
    (fun _ hh ↦ run_zero (f 0) (hh 0 le_rfl))
    (fun n ih hs hh ↦ run_seq _ _ _ n 1
      (ih (fun i hi ↦ hs i (by omega)) (fun i hi ↦ hh i (by omega)))
      (run_step _ _ (hs n (Nat.lt_succ_self n)) (hh n (Nat.le_succ n)) (hh (n + 1) le_rfl)))
    n hstep hheads

/-- The run along a family descending from a cell to {lit}`0`. -/
theorem run_family_down (f : ℕ → Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (n : ℕ)
    (hstep : ∀ i, i < n →
      bitTreeScanner.step (f (i + 1)) = f i ∧ bitTreeScanner.outputSymbol (f (i + 1)) = none)
    (hheads : ∀ i, i ≤ n → HeadsLE w (f i)) : Run w (f n) (f 0) n := by
  have := run_family (fun i ↦ f (n - i)) n
    (fun i hi ↦ by
      have := hstep (n - (i + 1)) (by omega)
      rw [show n - (i + 1) + 1 = n - i by omega] at this
      exact this)
    (fun i _ ↦ hheads (n - i) (Nat.sub_le n i))
  rw [Nat.sub_zero, Nat.sub_self] at this
  exact this

end Run

end Geb.BitTreeScanner
