/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true in
/-!
# The bit-reading phases

Two one-step phases move a single bit between tapes. {lit}`readBit` copies
the symbol under the input head onto a work tape's head cell, so that an
empty parked register comes to hold the input symbol's word: one bit, or the
empty word at either boundary cell. {lit}`popStep` reads a work tape's head
cell: on a bit it blanks that cell and writes the bit at another tape's head
cell, so that the head bit of one register moves to an empty register; on a
blank it moves the head one cell right, so that a head at cell {lit}`-1` of
an empty register returns to cell {lit}`0`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`readBit` — write the input symbol at one head's cell.
* {lit}`popStep` — move one bit from one head's cell to another's.

# Main statements

* {lit}`readBit_runsTo`, {lit}`popStep_runsTo_cons`,
  {lit}`popStep_runsTo_nil` — the run of each machine, naming the halted
  configuration and the step count.

# Tags

Turing machine, register, input tape, reading
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Write the input symbol, when there is one, at the head of tape {lit}`i`,
without moving, and halt. -/
@[expose] def readBit {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    { inputTape := 0
      workTapes := fun j ↦ if j = i then (inp.map some, 0) else (none, 0)
      output := none, state := none }

/-- Read the head of tape {lit}`i`: on a bit, blank it and write it at the head
of tape {lit}`j`; on a blank, move tape {lit}`i`'s head right. Halt either
way. -/
@[expose] def popStep {k : ℕ} (i j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some c =>
      { inputTape := 0
        workTapes := fun l ↦ if l = i then (some none, 0) else if l = j then (some (some c), 0)
          else (none, 0)
        output := none, state := none }
    | none =>
      { inputTape := 0, workTapes := fun l ↦ (none, if l = i then 1 else 0),
        output := none, state := none }

/-- {name}`readBit` at a parked empty register runs one step and leaves it
holding the input symbol's word. -/
theorem readBit_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hw : cfg.workTapes i = tapeOf []) (hp : cfg.workTapePos i = 0)
    (B : ℕ) (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (readBit i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf cfg.inputSymbol.toList) }
      1 B := by
  have hhalt : (readBit i).step cfg =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf cfg.inputSymbol.toList) } := by
    have htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool),
        (readBit i).tr () inp work =
          { inputTape := 0
            workTapes := fun j ↦ if j = i then (inp.map some, 0) else (none, 0)
            output := none, state := none } := fun _ _ ↦ rfl
    rw [step_of_state _ _ () hq, htr]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      dsimp only
      by_cases hj : j = i
      · rw [hj, ite_eq_left rfl]
        rcases cfg.inputSymbol with _ | b
        · change cfg.workTapes i = Function.update cfg.workTapes i (tapeOf []) i
          rw [Function.update_self, hw]
        · change Function.update (cfg.workTapes i) (cfg.workTapePos i) (some b) =
            Function.update cfg.workTapes i (tapeOf [b]) i
          rw [Function.update_self, hw, hp, tapeOf_cons]
          rfl
      · rw [ite_eq_right hj]
        change cfg.workTapes j = Function.update cfg.workTapes i (tapeOf _) j
        rw [Function.update_of_ne hj]
    · funext j
      dsimp only
      by_cases hj : j = i
      · rw [hj, ite_eq_left rfl]
        change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
        rw [SignType.coe_zero, add_zero]
      · rw [ite_eq_right hj]
        change cfg.workTapePos j + ((0 : SignType) : ℤ) = cfg.workTapePos j
        rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (readBit i).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  exact RunsTo.ofFamily (readBit i) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ j ↦ hpos j)
    (fun j ↦ hpos j)

/-- {name}`popStep` at the head bit of a register holding {lit}`c :: r`, with
a parked empty register {lit}`j`, runs one step; {lit}`i` then holds
{lit}`r` and {lit}`j` holds {lit}`[c]`. -/
theorem popStep_runsTo_cons {k : ℕ} {input : List Bool} (i j : Fin k) (hij : i ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ()) (c : Bool) (r : List Bool)
    (hw : cfg.workTapes i = tapeOf (c :: r)) (hp : cfg.workTapePos i = (r.length : ℤ))
    (hj : cfg.workTapes j = tapeOf []) (hpj : cfg.workTapePos j = 0) (B : ℕ)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (popStep i j) cfg
      { cfg with
        state := none
        workTapes :=
          Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) }
      1 B := by
  have hsym : cfg.workTapeSymbols i = some c := by
    change cfg.workTapes i (cfg.workTapePos i) = some c
    rw [hw, hp, tapeOf_cons, Function.update_self]
  have htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = some c →
      (popStep i j).tr () inp work =
        { inputTape := 0
          workTapes := fun l ↦ if l = i then (some none, 0) else if l = j then (some (some c), 0)
            else (none, 0)
          output := none, state := none } := by
    intro inp work hc
    simp only [popStep, hc]
  have hhalt : (popStep i j).step cfg =
      { cfg with
        state := none
        workTapes :=
          Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) } := by
    rw [step_of_state _ _ () hq, htr _ _ hsym]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      dsimp only
      by_cases hli : l = i
      · rw [hli, ite_eq_left rfl]
        change Function.update (cfg.workTapes i) (cfg.workTapePos i) none =
          Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) i
        rw [Function.update_of_ne hij, Function.update_self, hw, hp, tapeOf_update_none]
      · rw [ite_eq_right hli]
        by_cases hl : l = j
        · rw [hl, ite_eq_left rfl]
          change Function.update (cfg.workTapes j) (cfg.workTapePos j) (some c) =
            Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) j
          rw [Function.update_self, hj, hpj, tapeOf_cons]
          rfl
        · rw [ite_eq_right hl]
          change cfg.workTapes l =
            Function.update (Function.update cfg.workTapes i (tapeOf r)) j (tapeOf [c]) l
          rw [Function.update_of_ne hl, Function.update_of_ne hli]
    · funext l
      dsimp only
      by_cases hli : l = i
      · rw [hli, ite_eq_left rfl]
        change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
        rw [SignType.coe_zero, add_zero]
      · rw [ite_eq_right hli]
        by_cases hl : l = j
        · rw [hl, ite_eq_left rfl]
          change cfg.workTapePos j + ((0 : SignType) : ℤ) = cfg.workTapePos j
          rw [SignType.coe_zero, add_zero]
        · rw [ite_eq_right hl]
          change cfg.workTapePos l + ((0 : SignType) : ℤ) = cfg.workTapePos l
          rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (popStep i j).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    change ((popStep i j).tr () cfg.inputSymbol cfg.workTapeSymbols).output = none
    rw [htr _ _ hsym]
  exact RunsTo.ofFamily (popStep i j) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ l ↦ hpos l)
    (fun l ↦ hpos l)

/-- {name}`popStep` at cell {lit}`-1` of an empty register {lit}`i` runs one
step and moves that head to cell {lit}`0`. -/
theorem popStep_runsTo_nil {k : ℕ} {input : List Bool} (i j : Fin k)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (hw : cfg.workTapes i = tapeOf []) (hp : cfg.workTapePos i = -1) (B : ℕ)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (popStep i j) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 } 1 B := by
  have hsym : cfg.workTapeSymbols i = none := by
    change cfg.workTapes i (cfg.workTapePos i) = none
    rw [hw, hp, tapeOf_neg _ _ (by omega)]
  have htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = none →
      (popStep i j).tr () inp work =
        { inputTape := 0, workTapes := fun l ↦ (none, if l = i then 1 else 0),
          output := none, state := none } := by
    intro inp work hc
    simp only [popStep, hc]
  have hhalt : (popStep i j).step cfg =
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 } := by
    rw [step_of_state _ _ () hq, htr _ _ hsym]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext l
      change cfg.workTapePos l + ((if l = i then (1 : SignType) else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i 0 l
      by_cases hli : l = i
      · subst hli
        rw [Function.update_self, ite_eq_left rfl, SignType.coe_one, hp]
        omega
      · rw [Function.update_of_ne hli, ite_eq_right hli, SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (popStep i j).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    change ((popStep i j).tr () cfg.inputSymbol cfg.workTapeSymbols).output = none
    rw [htr _ _ hsym]
  exact RunsTo.ofFamily (popStep i j) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ l ↦ hpos l)
    (fun l ↦ update_workTapePos_bounds i hpos 0 (by omega) (by omega) l)

end

end Geb.SizeBounded.Logspace.Machine
