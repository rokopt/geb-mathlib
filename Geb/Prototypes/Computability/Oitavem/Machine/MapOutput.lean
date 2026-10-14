/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Generated

set_option doc.verso true in
/-!
# Finite-state transformations of generated words

A finite-state transducer can transform a generator's output without adding work
tapes. Each emitted digit updates its state and may emit one digit. A final transition
may emit a last digit after the generator halts. The generator's tapes and heads are
preserved exactly, including the effects of its halting transition.

## Main definitions

* {lit}`outputFold` interprets the digit transitions on a word.
* {lit}`mapOutputTr` applies the transitions while simulating a generator's
  transition, and {lit}`mapOutput` is the machine built from it.
* {lit}`mute`, with transition {lit}`muteTr`, discards a generator's output.

## Main statements

* {lit}`mapOutput_tr`, {lit}`mapOutput_ofTr` and {lit}`mute_ofTr` relate the machines
  to their transition functions.
* {lit}`mapOutput_emits` gives the exact output with one additional transition.
* {lit}`mapOutput_emitsIn` preserves the generator's subroutine contract.

## Implementation notes

The wrapper stores its additional state in finite control. A missing simulated state
selects the final transition. The contracts inherit CSLib's
{lit}`Classical.choice` dependency. {lit}`mapOutput` reads the transition CSLib
selects by choice and is noncomputable; {lit}`mapOutputTr` is computable.

## Tags

Turing machine, logarithmic space, finite-state transducer, composition
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace.Machine

public section

/-- Accumulate the state and emitted word of a digit transducer. -/
@[expose] def outputFold {A : Type} (step : A → Bool → A × Option Bool)
    (a : A) (w : List Bool) : A × List Bool :=
  w.foldl (fun p b ↦ let r := step p.1 b; (r.1, p.2 ++ r.2.toList)) (a, [])

/-- Advance a digit transducer only when the underlying generator emits. -/
@[expose] def outputNext {A : Type} (step : A → Bool → A × Option Bool)
    (a : A) (b : Option Bool) : A × Option Bool :=
  b.elim (a, none) (step a)

/-- Appending an optional digit advances the fold by one optional transition. -/
theorem outputFold_append {A : Type} (step : A → Bool → A × Option Bool)
    (a : A) (w : List Bool) (b : Option Bool) :
    outputFold step a (w ++ b.toList) =
      ((outputNext step (outputFold step a w).1 b).1,
        (outputFold step a w).2 ++ (outputNext step (outputFold step a w).1 b).2.toList) := by
  cases b <;> simp [outputFold, outputNext, List.foldl_append]

/-- The fold processes the first digit before the rest of the word. -/
theorem outputFold_cons {A : Type} (step : A → Bool → A × Option Bool)
    (a : A) (b : Bool) (w : List Bool) :
    outputFold step a (b :: w) =
      ((outputFold step (step a b).1 w).1,
        (step a b).2.toList ++ (outputFold step (step a b).1 w).2) := by
  have h := List.foldl_hom (fun (p : A × List Bool) ↦ (p.1, (step a b).2.toList ++ p.2))
    (g₁ := fun p b ↦ let r := step p.1 b; (r.1, p.2 ++ r.2.toList))
    (g₂ := fun p b ↦ let r := step p.1 b; (r.1, p.2 ++ r.2.toList))
    (l := w) (init := ((step a b).1, []))
    (fun p c ↦ by simp only [List.append_assoc])
  simpa only [outputFold, List.foldl_cons, List.nil_append, List.append_nil] using h

/-- Interpret all digit transitions and the final optional output. -/
@[expose] def outputWord {A : Type} (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) (a : A) (w : List Bool) : List Bool :=
  (outputFold step a w).2 ++ (finish (outputFold step a w).1).toList

/-- Empty input produces just the final transition's optional output. -/
@[simp] theorem outputWord_nil {A : Type} (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) (a : A) :
    outputWord step finish a [] = (finish a).toList := rfl

/-- Word interpretation obeys the transducer's digit-by-digit recursion equation. -/
theorem outputWord_cons {A : Type} (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) (a : A) (b : Bool) (w : List Bool) :
    outputWord step finish a (b :: w) =
      (step a b).2.toList ++ outputWord step finish (step a b).1 w := by
  simp only [outputWord, outputFold_cons, List.append_assoc]

/-- The transition transforming the output of the transition {lit}`trP` by the
digit transducer {lit}`step`, followed by the final optional digit {lit}`finish`. It
is not inlined, so that a partial application of it holds {lit}`trP` as an evaluated
argument rather than recomputing it at each application. -/
@[expose, noinline] def mapOutputTr {k : ℕ} {S A : Type}
    (trP : S → Option Bool → (Fin k → Option Bool) → Action k Bool S)
    (step : A → Bool → A × Option Bool) (finish : A → Option Bool) (state : A × Option S)
    (input : Option Bool) (work : Fin k → Option Bool) : Action k Bool (A × Option S) :=
  match state.2 with
  | none =>
    { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := finish state.1, state := none }
  | some q =>
    let act := trP q input work
    let r := outputNext step state.1 act.output
    { inputTape := act.inputTape, workTapes := act.workTapes,
      output := r.2, state := some (r.1, act.state) }

/-- Transform a generator's output, followed by one final optional digit: the machine
built from {name}`mapOutputTr` of its transition. -/
@[expose] noncomputable def mapOutput {k : ℕ} {S A : Type} (P : MultiTapeTM k Bool S) (a : A)
    (step : A → Bool → A × Option Bool) (finish : A → Option Bool) :
    MultiTapeTM k Bool (A × Option S) :=
  ofTr (a, some P.q₀) (mapOutputTr P.tr step finish)

/-- The transition of {name}`mapOutput` is {name}`mapOutputTr`. -/
theorem mapOutput_tr {k : ℕ} {S A : Type} (P : MultiTapeTM k Bool S) (a : A)
    (step : A → Bool → A × Option Bool) (finish : A → Option Bool) (state : A × Option S)
    (input : Option Bool) (work : Fin k → Option Bool) :
    (mapOutput P a step finish).tr state input work =
      mapOutputTr P.tr step finish state input work :=
  tr_ofTr _ _ _ _ _

/-- Transforming the output of a machine built from a transition function is the
machine built from {name}`mapOutputTr` of that function. -/
theorem mapOutput_ofTr {k : ℕ} {S A : Type} (q₀ : S)
    (tr : S → Option Bool → (Fin k → Option Bool) → Action k Bool S) (a : A)
    (step : A → Bool → A × Option Bool) (finish : A → Option Bool) :
    mapOutput (ofTr q₀ tr) a step finish = ofTr (a, some q₀) (mapOutputTr tr step finish) := by
  rw [mapOutput, tr_ofTr', q₀_ofTr]

/-- A simulated configuration with its transducer state and transformed output. -/
@[expose] def mapOutputCfg {k : ℕ} {S A : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (a : A) (out : List Bool) : Cfg k Bool (A × Option S) input :=
  { cfg with state := some (a, cfg.state), output := out }

/-- A live generator transition updates the transducer and preserves its tape action. -/
theorem mapOutput_step {k : ℕ} {S A : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (a₀ : A) (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) (cfg : Cfg k Bool S input) (a : A) (out : List Bool)
    (q : S) (hq : cfg.state = some q) :
    (mapOutput P a₀ step finish).step (mapOutputCfg cfg a out) =
      mapOutputCfg (P.step cfg) (outputNext step a (P.outputSymbol cfg)).1
        (out ++ (outputNext step a (P.outputSymbol cfg)).2.toList) := by
  rw [step_of_state _ _ (a, some q) (by simp [mapOutputCfg, hq]), step_of_state P cfg q hq,
    mapOutput_tr]
  simp only [mapOutputTr, mapOutputCfg, outputSymbol, hq]
  rfl

/-- Finite-state output transformation adds one step and preserves all work-head bounds. -/
theorem mapOutput_emits {k : ℕ} {S A : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S} {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P cfg cfg' w t B) (a : A) (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) :
    Emits (mapOutput P a step finish) (mapOutputCfg cfg a cfg.output)
      { cfg' with
        state := (none : Option (A × Option S))
        output := cfg.output ++ ((outputFold step a w).2 ++
          (finish (outputFold step a w).1).toList) }
      ((outputFold step a w).2 ++ (finish (outputFold step a w).1).toList) (t + 1) B := by
  let f (s : ℕ) := mapOutputCfg (P.runFrom cfg s)
    (outputFold step a (P.outputString cfg s)).1
    (cfg.output ++ (outputFold step a (P.outputString cfg s)).2)
  have hstart : f 0 = mapOutputCfg cfg a cfg.output := by
    change mapOutputCfg cfg a (cfg.output ++ []) = _
    rw [List.append_nil]
  have hstep (s : ℕ) (hs : s < t) : (mapOutput P a step finish).step (f s) = f (s + 1) := by
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (h.live s hs)
    dsimp only [f]
    rw [mapOutput_step _ _ _ _ _ _ _ q hq, runFrom_succ_eq_step', outputString_succ,
      outputFold_append, List.append_assoc]
  have hrun (s : ℕ) (hs : s ≤ t) :
      (mapOutput P a step finish).runFrom (mapOutputCfg cfg a cfg.output) s = f s := by
    refine Nat.rec ?_ (fun s ih hs ↦ ?_) s hs
    · intro _
      exact hstart.symm
    · rw [runFrom_succ_eq_step', ih (by omega), hstep s (by omega)]
  have hend : f t = mapOutputCfg cfg' (outputFold step a w).1
      (cfg.output ++ (outputFold step a w).2) := by
    simp only [f, h.runFrom_eq, h.output]
  have hfinish : (mapOutput P a step finish).step (f t) =
      { cfg' with
        state := (none : Option (A × Option S))
        output := cfg.output ++ ((outputFold step a w).2 ++
          (finish (outputFold step a w).1).toList) } := by
    rw [hend, step_of_state _ _ ((outputFold step a w).1, none)
      (by simp [mapOutputCfg, h.halted]), mapOutput_tr]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      exact add_zero _
    · exact List.append_assoc ..
  have hfinal : (mapOutput P a step finish).runFrom (mapOutputCfg cfg a cfg.output) (t + 1) =
      (mapOutput P a step finish).step (f t) := by
    rw [runFrom_succ_eq_step', hrun t le_rfl]
  rw [hfinish] at hfinal
  refine ⟨⟨?_, hfinal, ?_⟩, ?_, rfl⟩
  · intro s hs
    rw [hrun s (by omega)]
    exact Option.some_ne_none _
  · intro s hs i
    by_cases hst : s ≤ t
    · rw [hrun s hst]
      exact h.pos s hst i
    · have : s = t + 1 := by omega
      rw [this, hfinal]
      simpa only [h.runFrom_eq] using h.pos t le_rfl i
  · apply List.append_cancel_left (as := cfg.output)
    change (mapOutputCfg cfg a cfg.output).output ++ _ = _
    rw [← runFrom_output, hfinal]

/-- A finite-state output transformation preserves the generator's valuation contract. -/
theorem mapOutput_emitsIn {k : ℕ} {S A : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) (a : A) (step : A → Bool → A × Option Bool)
    (finish : A → Option Bool) :
    EmitsIn (mapOutput P a step finish) Pre F
      (fun input σ ↦ (outputFold step a (W input σ)).2 ++
        (finish (outputFold step a (W input σ)).1).toList) (fun n ↦ T n + 1) B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  obtain ⟨hFB, t, ht, he⟩ := hP input { cfg with state := some P.q₀ }
    σ rfl hpark hpos hσ hp hB
  have h := mapOutput_emits he a step finish
  have hstart : mapOutputCfg { cfg with state := some P.q₀ } a cfg.output = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hstart] at h
  exact ⟨hFB, t + 1, Nat.add_le_add_right ht 1, h⟩

/-- Run an emitting program while discarding every output digit. -/
@[expose] noncomputable def mute {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  mapOutput P () (fun _ _ ↦ ((), none)) (fun _ ↦ none)

/-- The transition of {name}`mute`, from the program's transition. -/
@[expose] def muteTr {k : ℕ} {S : Type}
    (trP : S → Option Bool → (Fin k → Option Bool) → Action k Bool S) :=
  mapOutputTr trP (fun (_ : Unit) _ ↦ ((), none)) (fun _ ↦ none)

/-- Muting a machine built from a transition function is the machine built from
{name}`muteTr` of that function. -/
theorem mute_ofTr {k : ℕ} {S : Type} (q₀ : S)
    (tr : S → Option Bool → (Fin k → Option Bool) → Action k Bool S) :
    mute (ofTr q₀ tr) = ofTr ((), some q₀) (muteTr tr) :=
  mapOutput_ofTr q₀ tr _ _ _

/-- Suppressing output preserves the complete valuation and space contract. -/
theorem mute_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    EmitsIn (mute P) Pre F (fun _ _ ↦ []) (fun n ↦ T n + 1) B := by
  have hnil (w : List Bool) : outputFold (fun (_ : Unit) _ ↦ ((), none)) () w = ((), []) := by
    revert w
    refine List.rec ?_ ?_
    · rfl
    · intro b w ih
      rw [outputFold_cons, ih]; rfl
  exact (mapOutput_emitsIn hP () (fun _ _ ↦ ((), none)) (fun _ ↦ none)).congr_output
    (fun _ _ _ ↦ by rw [hnil]; rfl)

end

end Geb.Oitavem.Machine
