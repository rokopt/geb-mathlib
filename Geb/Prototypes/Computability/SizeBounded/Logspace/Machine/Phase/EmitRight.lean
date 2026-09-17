/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Emit
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Input

set_option doc.verso true in
/-!
# The suffix-emitting phase

{lit}`emitRight` walks the input head right from its current cell, emitting
each symbol it reads, and halts on reading the blank past the input. From
position {lit}`p` it emits the suffix of the input from its {lit}`p`th
symbol, which is {lit}`input.drop (p - 1)`, since position {lit}`0` is the
blank before the input. No work tape is written or moved, so the phase costs
no space.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`emitRight` — walk the input head right, emitting each symbol read.
* {lit}`emitRightCfg` — the closed form of the walk's configurations.

# Main statements

* {lit}`emitRight_emits` — the run of the machine, naming the halted
  configuration, the emitted suffix and the step count.

# Tags

Turing machine, input tape, output, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Walk the input head right, emitting each symbol read, until it reads a
blank. -/
@[expose] def emitRight {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    match inp with
    | some b =>
      { inputTape := 1, workTapes := fun _ ↦ (none, 0), output := some b, state := some () }
    | none => { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- The configuration of {name}`emitRight` after {lit}`s` steps from the input
head at position {lit}`p`: the head has moved {lit}`s` cells right and the
first {lit}`s` symbols of the suffix from {lit}`p` have been emitted. -/
@[expose] def emitRightCfg {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input) (p s : ℕ) :
    Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    inputPos := ⟨min (p + s) (input.length + 1), by omega⟩
    output := cfg.output ++ (input.drop (p - 1)).take s }

/-- {name}`emitRight` from the input head at position {lit}`p`, between the
first symbol and the blank past the input, runs {lit}`input.length + 2 - p`
steps, emits {lit}`input.drop (p - 1)`, and leaves the head past the input. -/
theorem emitRight_emits {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (p : ℕ) (hp : cfg.inputPos.val = p) (hp1 : 1 ≤ p)
    (hpn : p ≤ input.length + 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    Emits emitRight cfg
      { cfg with
        state := none
        inputPos := ⟨input.length + 1, by omega⟩
        output := cfg.output ++ input.drop (p - 1) }
      (input.drop (p - 1)) (input.length + 2 - p) B := by
  have htrSome : ∀ (b : Bool) (work : Fin k → Option Bool),
      (emitRight (k := k)).tr () (some b) work =
        { inputTape := SignType.pos, workTapes := fun _ ↦ (none, 0), output := some b,
          state := some () } := fun _ _ ↦ rfl
  have htrNone : ∀ work : Fin k → Option Bool,
      (emitRight (k := k)).tr () none work =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } :=
    fun _ ↦ rfl
  have hlen : (input.drop (p - 1)).length = input.length + 1 - p := by
    rw [List.length_drop]
    omega
  have hsym : ∀ s, (hs : s < input.length + 1 - p) →
      (emitRightCfg cfg p s).inputSymbol = some (input[p - 1 + s]'(by omega)) := fun s hs ↦
    inputSymbolInner (p - 1 + s)
      (by change min (p + s) (input.length + 1) = 1 + (p - 1 + s); omega) (by omega)
  have hsymNone : (emitRightCfg cfg p (input.length + 1 - p)).inputSymbol = none := by
    have h₀ : ¬((emitRightCfg cfg p (input.length + 1 - p)).inputPos = 0) := fun h ↦ by
      have hv := congrArg Fin.val h
      rw [Fin.val_zero] at hv
      change min (p + (input.length + 1 - p)) (input.length + 1) = 0 at hv
      omega
    have h₁ : ((emitRightCfg cfg p (input.length + 1 - p)).inputPos : ℕ) = input.length + 1 := by
      change min (p + (input.length + 1 - p)) (input.length + 1) = input.length + 1
      omega
    unfold Cfg.inputSymbol
    rw [dite_eq_right h₀, dite_eq_left h₁]
  have hstep : ∀ s < input.length + 1 - p,
      (emitRight (k := k)).step (emitRightCfg cfg p s) = emitRightCfg cfg p (s + 1) := by
    intro s hs
    rw [step_of_state _ _ () rfl, hsym s hs, htrSome]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_pos_of_ne_right _
        (by change min (p + s) (input.length + 1) ≠ input.length + 1; omega)]
      exact Fin.ext (by
        change min (p + s) (input.length + 1) + 1 = min (p + (s + 1)) (input.length + 1)
        omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · change cfg.output ++ (input.drop (p - 1)).take s ++ [input[p - 1 + s]'(by omega)] =
        cfg.output ++ (input.drop (p - 1)).take (s + 1)
      rw [List.take_succ_eq_append_getElem (by omega), List.getElem_drop, List.append_assoc]
  have hhalt : (emitRight (k := k)).step (emitRightCfg cfg p (input.length + 1 - p)) =
      { cfg with
        state := none
        inputPos := ⟨input.length + 1, by omega⟩
        output := cfg.output ++ input.drop (p - 1) } := by
    rw [step_of_state _ _ () rfl, hsymNone, htrNone]
    apply Cfg.ext
    · rfl
    · rw [moveInputPos_zero]
      exact Fin.ext (by
        change min (p + (input.length + 1 - p)) (input.length + 1) = input.length + 1
        omega)
    · rfl
    · funext i
      change cfg.workTapePos i + ((0 : SignType) : ℤ) = cfg.workTapePos i
      rw [SignType.coe_zero, add_zero]
    · change cfg.output ++ (input.drop (p - 1)).take (input.length + 1 - p) ++ [] =
        cfg.output ++ input.drop (p - 1)
      rw [← hlen, List.take_length, List.append_nil]
  have hout : ∀ s ≤ input.length + 1 - p, (input.drop (p - 1)).take (s + 1) =
      (input.drop (p - 1)).take s ++
        ((emitRight (k := k)).outputSymbol (emitRightCfg cfg p s)).toList := by
    intro s hs
    change _ = _ ++ ((emitRight (k := k)).tr () (emitRightCfg cfg p s).inputSymbol
      (emitRightCfg cfg p s).workTapeSymbols).output.toList
    rcases Nat.lt_or_ge s (input.length + 1 - p) with h | h
    · rw [hsym s h, htrSome, List.take_succ_eq_append_getElem (by omega), List.getElem_drop]
      rfl
    · rw [show s = input.length + 1 - p by omega, hsymNone, htrNone, ← hlen, List.take_length,
        List.take_of_length_le (Nat.le_succ _)]
      exact (List.append_nil _).symm
  have hzero : emitRightCfg cfg p 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · exact Fin.ext (by
        change min (p + 0) (input.length + 1) = cfg.inputPos.val
        rw [Nat.add_zero, Nat.min_eq_left hpn, hp])
    · rfl
    · rfl
    · exact List.append_nil _
  have key := Emits.ofFamily (emitRight (k := k)) (emitRightCfg cfg p)
    (fun s ↦ (input.drop (p - 1)).take s) (input.length + 1 - p) B
    { cfg with
      state := none
      inputPos := ⟨input.length + 1, by omega⟩
      output := cfg.output ++ input.drop (p - 1) }
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl rfl hout
    (fun _ _ i ↦ hpos i) (fun i ↦ hpos i)
  rwa [hzero, List.take_of_length_le (by rw [hlen]; exact Nat.le_succ _),
    show input.length + 1 - p + 1 = input.length + 2 - p by omega] at key

end

end Geb.SizeBounded.Logspace.Machine
