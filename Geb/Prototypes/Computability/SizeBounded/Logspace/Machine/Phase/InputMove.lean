/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Input
import Geb.Prototypes.Computability.SizeBounded.Machine.Emit

set_option doc.verso true in
/-!
# Input-head movement phases

Three movements of the input head, each leaving every work tape and the
output untouched. {lit}`inStepRight` moves the head one cell right;
{name}`Geb.SizeBounded.Machine.inBack`, whose run from the blank past the
input {name}`Geb.SizeBounded.Machine.inBack_runsTo` states, is here run from
any position other than the blank before the input; and {lit}`inHome` walks
the head left until it reads that blank. A logspace machine steps the input
head by these one cell per counter operation, and returns it to the blank
before the input between passes.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`inStepRight` — move the input head one cell right.
* {lit}`inHome` — walk the input head left to the blank before the input.
* {lit}`inHomeCfg` — the closed form of the walk's configurations.

# Main statements

* {lit}`inStepRight_runsTo`, {lit}`inBack_runsTo_of_pos`, {lit}`inHome_runsTo`
  — the run of each machine, naming the halted configuration and the step
  count.

# Tags

Turing machine, input tape, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Move the input head one cell right. -/
@[expose] def inStepRight {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := 1, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- Walk the input head left until it reads the blank before the input. -/
@[expose] def inHome {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    match inp with
    | some _ =>
      { inputTape := -1, workTapes := fun _ ↦ (none, 0), output := none, state := some () }
    | none => { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- {name}`inStepRight` from any position other than the blank past the input
runs one step and leaves the head one cell right. -/
theorem inStepRight_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val < input.length + 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inStepRight cfg
      { cfg with state := none, inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ } 1 B := by
  have hhalt : (inStepRight (k := k)).step { cfg with state := some () } =
      { cfg with state := none, inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ } := by
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos SignType.pos = (⟨cfg.inputPos.val + 1, by omega⟩ : Fin _)
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : ({ cfg with state := some () } : Cfg k Bool Unit input) = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · rfl
    · rfl
  have key := RunsTo.ofFamily (inStepRight (k := k)) (fun _ ↦ { cfg with state := some () }) 0 B
    { cfg with state := none, inputPos := ⟨cfg.inputPos.val + 1, by omega⟩ }
    (fun _ _ ↦ Option.some_ne_none ()) (fun _ h ↦ absurd h (by omega)) hhalt rfl
    (fun _ _ ↦ rfl) (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero] at key

/-- {name}`Geb.SizeBounded.Machine.inBack` from any position other than the
blank before the input runs one step and leaves the head one cell left. -/
theorem inBack_runsTo_of_pos {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val ≠ 0) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inBack cfg
      { cfg with
        state := none
        inputPos := ⟨cfg.inputPos.val - 1, by have := cfg.inputPos.isLt; omega⟩ } 1 B := by
  have hhalt : (inBack (k := k)).step { cfg with state := some () } =
      { cfg with
        state := none
        inputPos := ⟨cfg.inputPos.val - 1, by have := cfg.inputPos.isLt; omega⟩ } := by
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos SignType.neg =
        (⟨cfg.inputPos.val - 1, by have := cfg.inputPos.isLt; omega⟩ : Fin _)
      rw [moveInputPos_neg_of_ne_left _ (fun h ↦ hp (by rw [h, Fin.val_zero]))]
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : ({ cfg with state := some () } : Cfg k Bool Unit input) = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · rfl
    · rfl
  have key := RunsTo.ofFamily (inBack (k := k)) (fun _ ↦ { cfg with state := some () }) 0 B
    { cfg with
      state := none
      inputPos := ⟨cfg.inputPos.val - 1, by have := cfg.inputPos.isLt; omega⟩ }
    (fun _ _ ↦ Option.some_ne_none ()) (fun _ h ↦ absurd h (by omega)) hhalt rfl
    (fun _ _ ↦ rfl) (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero] at key

/-- The configuration of {name}`inHome` after {lit}`s` steps: the input head has
moved {lit}`s` cells left, stopping at the blank before the input. -/
@[expose] def inHomeCfg {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input) (s : ℕ) :
    Cfg k Bool Unit input :=
  { cfg with state := some (), inputPos := ⟨cfg.inputPos.val - s, by omega⟩ }

/-- {name}`inHome` from the input head at a symbol or at the blank before the
input runs one step per cell to that blank, plus one, and leaves the head
there. -/
theorem inHome_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val ≤ input.length) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inHome cfg { cfg with state := none, inputPos := ⟨0, by omega⟩ }
      (cfg.inputPos.val + 1) B := by
  have htrSome : ∀ (b : Bool) (work : Fin k → Option Bool),
      (inHome (k := k)).tr () (some b) work =
        { inputTape := SignType.neg, workTapes := fun _ ↦ (none, 0), output := none,
          state := some () } := fun _ _ ↦ rfl
  have htrNone : ∀ work : Fin k → Option Bool,
      (inHome (k := k)).tr () none work =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } :=
    fun _ ↦ rfl
  have hout : ∀ (inp : Option Bool) (work : Fin k → Option Bool),
      ((inHome (k := k)).tr () inp work).output = none := by
    intro inp _
    cases inp <;> rfl
  have hstep : ∀ s < cfg.inputPos.val,
      (inHome (k := k)).step (inHomeCfg cfg s) = inHomeCfg cfg (s + 1) := by
    intro s hs
    have hsym : (inHomeCfg cfg s).inputSymbol =
        some (input[cfg.inputPos.val - s - 1]'(by omega)) :=
      inputSymbolInner (cfg.inputPos.val - s - 1)
        (by change cfg.inputPos.val - s = 1 + (cfg.inputPos.val - s - 1); omega) (by omega)
    rw [step_of_state _ _ () rfl, hsym, htrSome]
    apply Cfg.ext
    · rfl
    · change moveInputPos (inHomeCfg cfg s).inputPos SignType.neg = (inHomeCfg cfg (s + 1)).inputPos
      rw [moveInputPos_neg_of_ne_left _ (fun h ↦ by
        have hv := congrArg Fin.val h
        rw [Fin.val_zero] at hv
        change cfg.inputPos.val - s = 0 at hv
        omega)]
      exact Fin.ext (by
        change cfg.inputPos.val - s - 1 = cfg.inputPos.val - (s + 1)
        omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hhalt : (inHome (k := k)).step (inHomeCfg cfg cfg.inputPos.val) =
      { cfg with state := none, inputPos := ⟨0, by omega⟩ } := by
    have hsym : (inHomeCfg cfg cfg.inputPos.val).inputSymbol = none := by
      unfold Cfg.inputSymbol
      rw [dite_eq_left (Fin.ext (by
        change cfg.inputPos.val - cfg.inputPos.val = (0 : Fin (input.length + 2)).val
        rw [Fin.val_zero]
        omega))]
    rw [step_of_state _ _ () rfl, hsym, htrNone]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_zero]
      exact Fin.ext (by change cfg.inputPos.val - cfg.inputPos.val = 0; omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : inHomeCfg cfg 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · exact Fin.ext (by change cfg.inputPos.val - 0 = cfg.inputPos.val; omega)
    · rfl
    · rfl
    · rfl
  have key := RunsTo.ofFamily (inHome (k := k)) (inHomeCfg cfg) cfg.inputPos.val B
    { cfg with state := none, inputPos := ⟨0, by omega⟩ }
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl (fun _ _ ↦ hout _ _)
    (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero] at key

end

end Geb.SizeBounded.Logspace.Machine
