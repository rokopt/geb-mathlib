/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
import Geb.Prototypes.Computability.SizeBounded.Machine.Emit
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true in
/-!
# The input-reading phases

Three phases carry the input onto a work tape. {lit}`inRight` moves the input
head right to the blank past the input, {lit}`inBack` steps it back onto the
input's last symbol, and {lit}`inLeft` walks it left to the blank before the
input, writing each symbol it reads at one register's head and advancing that
head. The register then holds the input in the reversed layout of
{name}`Geb.SizeBounded.Machine.tapeOf`, so the three in sequence load the
input into a register.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`inRight` — move the input head past the input.
* {lit}`inBack` — move the input head one cell left.
* {lit}`inLeft` — walk the input head left, writing what it reads into a
  register.
* {lit}`inRightCfg`, {lit}`inLeftCfg` — the closed forms of the two walks'
  configurations.

# Main statements

* {lit}`inRight_runsTo`, {lit}`inBack_runsTo`, {lit}`inLeft_runsTo` — the run
  of each machine, naming the halted configuration and the step count.

# Tags

Turing machine, input tape, register
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Move the input head right until it reads the blank past the input. -/
@[expose] def inRight {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    { inputTape := if inp.isSome then 1 else 0
      workTapes := fun _ ↦ (none, 0)
      output := none
      state := if inp.isSome then some () else none }

/-- Move the input head one cell left. -/
@[expose] def inBack {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := -1, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- Walk the input head left, writing each symbol read at register {lit}`j`'s
head and advancing that head, until the input head reads the blank before the
input. -/
@[expose] def inLeft {k : ℕ} (j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    match inp with
    | some b =>
      { inputTape := -1
        workTapes := fun l ↦ if l = j then (some (some b), 1) else (none, 0)
        output := none
        state := some () }
    | none => { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- The configuration of {name}`inRight` after {lit}`s` steps from the input
head at the first symbol. -/
@[expose] def inRightCfg {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input) (s : ℕ) :
    Cfg k Bool Unit input :=
  { cfg with state := some (), inputPos := ⟨min (1 + s) (input.length + 1), by omega⟩ }

/-- {name}`inRight` from the input head at the first symbol runs
{lit}`input.length + 1` steps and leaves the head past the input. -/
theorem inRight_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inRight cfg { cfg with state := none, inputPos := ⟨input.length + 1, by omega⟩ }
      (input.length + 1) B := by
  have htrSome : ∀ (b : Bool) (work : Fin k → Option Bool),
      (inRight (k := k)).tr () (some b) work =
        { inputTape := SignType.pos, workTapes := fun _ ↦ (none, 0), output := none,
          state := some () } := fun _ _ ↦ rfl
  have htrNone : ∀ work : Fin k → Option Bool,
      (inRight (k := k)).tr () none work =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } :=
    fun _ ↦ rfl
  have hstep : ∀ s < input.length,
      (inRight (k := k)).step (inRightCfg cfg s) = inRightCfg cfg (s + 1) := by
    intro s hs
    have hsym : (inRightCfg cfg s).inputSymbol = some input[s] :=
      inputSymbolInner s (by change min (1 + s) (input.length + 1) = 1 + s; omega) hs
    rw [step_of_state _ _ () rfl, hsym, htrSome]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_pos_of_ne_right _
        (by change min (1 + s) (input.length + 1) ≠ input.length + 1; omega)]
      exact Fin.ext (by
        change min (1 + s) (input.length + 1) + 1 = min (1 + (s + 1)) (input.length + 1)
        omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hhalt : (inRight (k := k)).step (inRightCfg cfg input.length) =
      { cfg with state := none, inputPos := ⟨input.length + 1, by omega⟩ } := by
    have hsym : (inRightCfg cfg input.length).inputSymbol = none := by
      have h₀ : ¬((inRightCfg cfg input.length).inputPos = 0) := fun h ↦ by
        have hv := congrArg Fin.val h
        rw [Fin.val_zero] at hv
        change min (1 + input.length) (input.length + 1) = 0 at hv
        omega
      have h₁ : ((inRightCfg cfg input.length).inputPos : ℕ) = input.length + 1 := by
        change min (1 + input.length) (input.length + 1) = input.length + 1
        omega
      unfold Cfg.inputSymbol
      rw [dite_eq_right h₀, dite_eq_left h₁]
    rw [step_of_state _ _ () rfl, hsym, htrNone]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_zero]
      exact Fin.ext (by
        change min (1 + input.length) (input.length + 1) = input.length + 1
        omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : inRightCfg cfg 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · exact Fin.ext (by change min (1 + 0) (input.length + 1) = cfg.inputPos.val; omega)
    · rfl
    · rfl
    · rfl
  have key := RunsTo.ofFamily (inRight (k := k)) (inRightCfg cfg) input.length B
    { cfg with state := none, inputPos := ⟨input.length + 1, by omega⟩ }
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl (fun _ _ ↦ rfl)
    (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero] at key

/-- {name}`inBack` from the input head past the input runs one step and leaves
the head at the last symbol, or at the blank before an empty input. -/
theorem inBack_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = input.length + 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inBack cfg { cfg with state := none, inputPos := ⟨input.length, by omega⟩ } 1 B := by
  have hhalt : (inBack (k := k)).step { cfg with state := some () } =
      { cfg with state := none, inputPos := ⟨input.length, by omega⟩ } := by
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos SignType.neg = (⟨input.length, by omega⟩ : Fin _)
      rw [moveInputPos_neg_of_ne_left _ (fun h ↦ by
        have hv := congrArg Fin.val h
        rw [Fin.val_zero] at hv
        omega)]
      exact Fin.ext (by change (cfg.inputPos : ℕ) - 1 = input.length; omega)
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
    { cfg with state := none, inputPos := ⟨input.length, by omega⟩ }
    (fun _ _ ↦ Option.some_ne_none ()) (fun _ h ↦ absurd h (by omega)) hhalt rfl
    (fun _ _ ↦ rfl) (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero] at key

/-- The configuration of {name}`inLeft` after {lit}`s` steps from the input
head at the last symbol and register {lit}`j` empty and parked: the head has
moved {lit}`s` cells left and {lit}`j` holds the last {lit}`s` symbols in the
reversed layout. -/
@[expose] def inLeftCfg {k : ℕ} {input : List Bool} (j : Fin k) (cfg : Cfg k Bool Unit input)
    (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    inputPos := ⟨input.length - s, by omega⟩
    workTapes := Function.update cfg.workTapes j (tapeOf (input.drop (input.length - s)))
    workTapePos := Function.update cfg.workTapePos j (s : ℤ) }

/-- {name}`inLeft` from the input head at the last symbol and register {lit}`j`
empty and parked runs {lit}`input.length + 1` steps; {lit}`j` then holds the
input in the reversed layout with its head at {lit}`input.length`, and the
input head is at the blank before the input. -/
theorem inLeft_runsTo {k : ℕ} {input : List Bool} (j : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = input.length)
    (hj : cfg.workTapes j = tapeOf []) (hpj : cfg.workTapePos j = 0) (B : ℕ)
    (hB : input.length ≤ B) (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo (inLeft j) cfg
      { cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input)
        workTapePos := Function.update cfg.workTapePos j (input.length : ℤ) }
      (input.length + 1) B := by
  have htrNone : ∀ work : Fin k → Option Bool,
      (inLeft j).tr () none work =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } :=
    fun _ ↦ rfl
  have hout : ∀ (inp : Option Bool) (work : Fin k → Option Bool),
      ((inLeft j).tr () inp work).output = none := by
    intro inp _
    cases inp <;> rfl
  have hstep : ∀ s < input.length,
      (inLeft j).step (inLeftCfg j cfg s) = inLeftCfg j cfg (s + 1) := by
    intro s hs
    have hsym : (inLeftCfg j cfg s).inputSymbol =
        some (input[input.length - 1 - s]'(by omega)) :=
      inputSymbolInner (input.length - 1 - s)
        (by change input.length - s = 1 + (input.length - 1 - s); omega) (by omega)
    have hlen : ((input.drop (input.length - s)).length : ℤ) = (s : ℤ) := by
      rw [List.length_drop]
      omega
    have htape : Function.update (tapeOf (input.drop (input.length - s))) (s : ℤ)
        (some (input[input.length - 1 - s]'(by omega))) =
        tapeOf (input.drop (input.length - (s + 1))) := by
      rw [drop_length_sub_succ input s hs, tapeOf_cons, hlen, List.getElem_reverse]
    have hact : ∀ l : Fin k, ((inLeft j).tr () (some (input[input.length - 1 - s]'(by omega)))
        (inLeftCfg j cfg s).workTapeSymbols).workTapes l =
        if l = j then (some (some (input[input.length - 1 - s]'(by omega))), (1 : SignType))
          else ((none : Option (Option Bool)), (0 : SignType)) := fun _ ↦ rfl
    rw [step_of_state _ _ () rfl, hsym]
    apply Cfg.ext
    · rfl
    · change moveInputPos (inLeftCfg j cfg s).inputPos SignType.neg =
        (inLeftCfg j cfg (s + 1)).inputPos
      rw [moveInputPos_neg_of_ne_left _ (fun h ↦ by
        have hv := congrArg Fin.val h
        rw [Fin.val_zero] at hv
        change input.length - s = 0 at hv
        omega)]
      exact Fin.ext (by
        change input.length - s - 1 = input.length - (s + 1)
        omega)
    · funext l
      simp only [hact l]
      by_cases hl : l = j
      · subst hl
        rw [ite_eq_left rfl]
        change Function.update
            (Function.update cfg.workTapes l (tapeOf (input.drop (input.length - s))) l)
            (Function.update cfg.workTapePos l (s : ℤ) l)
            (some (input[input.length - 1 - s]'(by omega))) =
          Function.update cfg.workTapes l (tapeOf (input.drop (input.length - (s + 1)))) l
        rw [Function.update_self, Function.update_self, Function.update_self]
        exact htape
      · rw [ite_eq_right hl]
        change Function.update cfg.workTapes j (tapeOf (input.drop (input.length - s))) l =
          Function.update cfg.workTapes j (tapeOf (input.drop (input.length - (s + 1)))) l
        rw [Function.update_of_ne hl, Function.update_of_ne hl]
    · funext l
      simp only [hact l]
      by_cases hl : l = j
      · subst hl
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapePos l (s : ℤ) l + ((1 : SignType) : ℤ) =
          Function.update cfg.workTapePos l ((s + 1 : ℕ) : ℤ) l
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hl]
        change Function.update cfg.workTapePos j (s : ℤ) l + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos j ((s + 1 : ℕ) : ℤ) l
        rw [Function.update_of_ne hl, Function.update_of_ne hl, SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hhalt : (inLeft j).step (inLeftCfg j cfg input.length) =
      { cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input)
        workTapePos := Function.update cfg.workTapePos j (input.length : ℤ) } := by
    have hsym : (inLeftCfg j cfg input.length).inputSymbol = none := by
      unfold Cfg.inputSymbol
      rw [dite_eq_left (Fin.ext (by
        change input.length - input.length = (0 : Fin (input.length + 2)).val
        rw [Fin.val_zero]
        omega))]
    rw [step_of_state _ _ () rfl, hsym, htrNone]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_zero]
      exact Fin.ext (by change input.length - input.length = 0; omega)
    · change Function.update cfg.workTapes j
          (tapeOf (input.drop (input.length - input.length))) =
        Function.update cfg.workTapes j (tapeOf input)
      rw [Nat.sub_self, List.drop_zero]
    · funext l
      change Function.update cfg.workTapePos j ((input.length : ℕ) : ℤ) l +
          ((0 : SignType) : ℤ) =
        Function.update cfg.workTapePos j (input.length : ℤ) l
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : inLeftCfg j cfg 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · exact Fin.ext (by change input.length - 0 = cfg.inputPos.val; omega)
    · change Function.update cfg.workTapes j (tapeOf (input.drop (input.length - 0))) =
        cfg.workTapes
      rw [Nat.sub_zero, List.drop_length, ← hj, Function.update_eq_self]
    · change Function.update cfg.workTapePos j (((0 : ℕ) : ℤ)) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos j by omega, Function.update_eq_self]
    · rfl
  have key := RunsTo.ofFamily (inLeft j) (inLeftCfg j cfg) input.length B
    { cfg with
      state := none
      inputPos := ⟨0, by omega⟩
      workTapes := Function.update cfg.workTapes j (tapeOf input)
      workTapePos := Function.update cfg.workTapePos j (input.length : ℤ) }
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl (fun _ _ ↦ hout _ _)
    (fun s hs l ↦ update_workTapePos_bounds j hpos (s : ℤ) (by omega) (by omega) l)
    (fun l ↦ update_workTapePos_bounds j hpos (input.length : ℤ) (by omega) (by omega) l)
  rwa [hzero] at key

end

end Geb.SizeBounded.Machine
