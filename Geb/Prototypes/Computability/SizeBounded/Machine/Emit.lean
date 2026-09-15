/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program

set_option doc.verso true in
/-!
# Emissions

An emission is an arrival at a halted configuration together with the word
the machine emitted on the way. A run is the emission of the empty word, so
the two contracts convert into each other, and the space bound a run enjoys
holds of an emission by the same argument: both read the head bound off
{name}`Geb.SizeBounded.Machine.Arrives`.

A machine whose configurations at the steps of a run are given in closed
form is handled by {lit}`Emits.ofFamily`: from a family {lit}`f` of live
configurations, each the step of its predecessor, whose last step is halted,
and an accumulator {lit}`o` collecting the emitted symbols, it reads off the
emission. {lit}`RunsTo.ofFamily` is the case of a family emitting nothing.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom`,
{name}`Turing.MultiTapeTM.outputString` and
{name}`Turing.MultiTapeTM.spaceUsed`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`
or mathlib's {name}`Finset.image`.

# Main definitions

* {lit}`Emits` — an arrival at a halted configuration emitting a given word.

# Main statements

* {lit}`RunsTo.toEmits`, {lit}`Emits.toRunsTo` — a run is the emission of the
  empty word.
* {lit}`Arrives.ofFamily`, {lit}`Reaches.ofFamily` — a closed-form family of
  live configurations is an arrival at its last member, and a reach when it
  emits nothing.
* {lit}`Emits.ofFamily`, {lit}`RunsTo.ofFamily` — a closed-form family of
  configurations is an emission, and a run when it emits nothing.
* {lit}`Emits.spaceUsedByTape_le`, {lit}`Emits.spaceUsed_le` — an emission's
  visited cells, per tape and in total.

# Tags

Turing machine, output, space complexity
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- An arrival at a halted configuration having emitted exactly {lit}`out`. -/
structure Emits {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (out : List Bool) (t B : ℕ) : Prop
    extends Arrives tm cfg cfg' t B where
  /-- The word emitted. -/
  output : tm.outputString cfg t = out
  /-- The target is halted. -/
  halted : cfg'.state = none

/-- A run emits nothing. -/
theorem RunsTo.toEmits {k : ℕ} {State : Type} {input : List Bool} {tm : MultiTapeTM k Bool State}
    {cfg cfg' : Cfg k Bool State input} {t B : ℕ} (h : RunsTo tm cfg cfg' t B) :
    Emits tm cfg cfg' [] t B :=
  ⟨h.toArrives, h.output, h.halted⟩

/-- Emitting nothing is a run. -/
theorem Emits.toRunsTo {k : ℕ} {State : Type} {input : List Bool} {tm : MultiTapeTM k Bool State}
    {cfg cfg' : Cfg k Bool State input} {t B : ℕ} (h : Emits tm cfg cfg' [] t B) :
    RunsTo tm cfg cfg' t B :=
  ⟨⟨h.toArrives, h.output⟩, h.halted⟩

/-- A closed-form family of live configurations, each the step of the previous,
is an arrival at its last member. -/
theorem Arrives.ofFamily {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (f : ℕ → Cfg k Bool State input) (n B : ℕ)
    (hlive : ∀ s < n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B) :
    Arrives tm (f 0) (f n) n B := by
  have key : ∀ s, s ≤ n → tm.runFrom (f 0) s = f s := by
    refine Nat.rec ?_ ?_
    · intro _
      exact runFrom_zero
    · intro s ih hs
      rw [runFrom_succ_eq_step', ih (by omega), hstep s (by omega)]
  exact ⟨fun t' ht' ↦ by rw [key t' (by omega)]; exact hlive t' ht',
    key n (le_refl n), fun t' ht' i ↦ by rw [key t' ht']; exact hpos t' ht' i⟩

/-- The family lemma for a reach: nothing emitted. -/
theorem Reaches.ofFamily {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (f : ℕ → Cfg k Bool State input) (n B : ℕ)
    (hlive : ∀ s < n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hout : ∀ s < n, tm.outputSymbol (f s) = none)
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B) :
    Reaches tm (f 0) (f n) n B := by
  have key : ∀ s ≤ n, tm.runFrom (f 0) s = f s := fun s hs ↦
    (Arrives.ofFamily tm f s B (fun t ht ↦ hlive t (by omega))
      (fun t ht ↦ hstep t (by omega)) (fun t ht ↦ hpos t (by omega))).runFrom_eq
  have hnil : ∀ s, s ≤ n → tm.outputString (f 0) s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      rfl
    · intro s ih hs
      rw [outputString_succ, ih (by omega), key s (by omega), hout s (by omega)]
      rfl
  exact ⟨Arrives.ofFamily tm f n B hlive hstep hpos, hnil n (le_refl n)⟩

/-- A closed-form family of live configurations, each the step of the previous,
the last of which steps to a halted configuration, is an emission: the accumulator
{lit}`o` collects the symbols the family emits. -/
theorem Emits.ofFamily {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (f : ℕ → Cfg k Bool State input) (o : ℕ → List Bool) (n B : ℕ)
    (cfg' : Cfg k Bool State input)
    (hlive : ∀ s ≤ n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hhalt : tm.step (f n) = cfg') (hcfg' : cfg'.state = none)
    (h0 : o 0 = []) (hout : ∀ s ≤ n, o (s + 1) = o s ++ (tm.outputSymbol (f s)).toList)
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    Emits tm (f 0) cfg' (o (n + 1)) (n + 1) B := by
  have key : ∀ s, s ≤ n → tm.runFrom (f 0) s = f s ∧ tm.outputString (f 0) s = o s := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨runFrom_zero, h0.symm⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [runFrom_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s (by omega)]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hcfg'⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact hlive t' (by omega)
  · rw [runFrom_succ_eq_step', (key n (le_refl n)).1, hhalt]
  · intro t' ht' i
    rcases Nat.lt_or_ge t' (n + 1) with h | h
    · rw [(key t' (by omega)).1]
      exact hpos t' (by omega) i
    · have : t' = n + 1 := by omega
      rw [this, runFrom_succ_eq_step', (key n (le_refl n)).1, hhalt]
      exact hpos' i
  · rw [outputString_succ, (key n (le_refl n)).1, (key n (le_refl n)).2, hout n (le_refl n)]

/-- The family lemma for a family that emits nothing. -/
theorem RunsTo.ofFamily {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (f : ℕ → Cfg k Bool State input) (n B : ℕ) (cfg' : Cfg k Bool State input)
    (hlive : ∀ s ≤ n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hhalt : tm.step (f n) = cfg') (hcfg' : cfg'.state = none)
    (hout : ∀ s ≤ n, tm.outputSymbol (f s) = none)
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    RunsTo tm (f 0) cfg' (n + 1) B :=
  (Emits.ofFamily tm f (fun _ ↦ []) n B cfg' hlive hstep hhalt hcfg' rfl
    (fun s hs ↦ by rw [hout s hs]; rfl) hpos hpos').toRunsTo

/-- Over an emission the head of each tape visits at most {lit}`B + 2` cells. -/
theorem Emits.spaceUsedByTape_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {out : List Bool}
    {t B : ℕ} (h : Emits tm cfg cfg' out t B) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ B + 2 :=
  spaceUsedByTape_le_of_pos tm cfg t B i fun t' ht' ↦ h.pos t' ht' i

/-- Over an emission the machine uses at most {lit}`k * (B + 2)` cells. -/
theorem Emits.spaceUsed_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {out : List Bool}
    {t B : ℕ} (h : Emits tm cfg cfg' out t B) : tm.spaceUsed cfg t ≤ k * (B + 2) := by
  unfold spaceUsed
  refine le_trans (Finset.sum_le_sum fun i _ ↦ h.spaceUsedByTape_le i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

end

end Geb.SizeBounded.Machine
