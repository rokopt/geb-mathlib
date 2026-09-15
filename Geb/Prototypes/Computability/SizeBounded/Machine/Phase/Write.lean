/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The writing phases

Two phases write a constant into a register. {lit}`writeBit` writes one bit
at its head's cell without moving, so that it prepends that bit to the word
of a register whose head is at the blank after the word. {lit}`constWalk`
writes a word from cell {lit}`0` rightwards, one bit per state, so that it
fills an empty register with a constant word; its bits come from its own
state rather than from a tape.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`writeBit` — write one bit at the head's cell.
* {lit}`constWalk` — write a constant word on an empty register.
* {lit}`constCfg` — the closed form of {lit}`constWalk`'s configurations.

# Main statements

* {lit}`writeBit_runsTo`, {lit}`constWalk_runsTo` — the run of each machine,
  naming the halted configuration and the step count.

# Tags

Turing machine, register, writing
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Write {lit}`b` at the head of tape {lit}`i`, without moving, and halt. -/
@[expose] def writeBit {k : ℕ} (b : Bool) (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputMove := 0
      workActions := fun j ↦ if j = i then (some (some b), 0) else (none, 0)
      outS := none, q' := none }

/-- Write {lit}`w` on tape {lit}`i` from the head rightwards in reversed
layout: state {lit}`s` writes {lit}`w.reverse[s]` and moves right, and state
{lit}`w.length` halts without moving. -/
@[expose] def constWalk {k : ℕ} (w : List Bool) (i : Fin k) :
    MultiTapeTM k Bool (Fin (w.length + 1)) where
  q₀ := 0
  tr s _ _ :=
    if h : s.val < w.length then
      { inputMove := 0
        workActions := fun j ↦
          if j = i then (some (some (w.reverse[s.val]'(by simp; omega))), 1) else (none, 0)
        outS := none, q' := some ⟨s.val + 1, by omega⟩ }
    else
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- {name}`writeBit` at cell {lit}`w.length` of a register holding {lit}`w`
runs one step and leaves it holding {lit}`b :: w`. -/
theorem writeBit_runsTo {k : ℕ} {input : List Bool} (b : Bool) (i : Fin k)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w) (hp : cfg.workTapePos i = (w.length : ℤ))
    (B : ℕ) (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (writeBit b i) cfg
      { cfg with state := none, workTapes := Function.update cfg.workTapes i (tapeOf (b :: w)) }
      1 B := by
  have hhalt : (writeBit b i).step cfg =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (b :: w)) } := by
    have htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool),
        (writeBit b i).tr () inp work =
          { inputMove := 0
            workActions := fun j ↦ if j = i then (some (some b), 0) else (none, 0)
            outS := none, q' := none } := fun _ _ ↦ rfl
    rw [step_of_state _ _ () hq, htr]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      dsimp only
      by_cases hj : j = i
      · rw [hj, ite_eq_left rfl]
        change Function.update (cfg.workTapes i) (cfg.workTapePos i) (some b) =
          Function.update cfg.workTapes i (tapeOf (b :: w)) i
        rw [Function.update_self, hw, hp, tapeOf_cons]
      · rw [ite_eq_right hj]
        change cfg.workTapes j = Function.update cfg.workTapes i (tapeOf (b :: w)) j
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
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (writeBit b i).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  exact RunsTo.ofFamily (writeBit b i) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ j ↦ hpos j)
    (fun j ↦ hpos j)

/-- The configuration of {name}`constWalk` after {lit}`s` steps from an empty
parked register. -/
@[expose] def constCfg {k : ℕ} {input : List Bool} (w : List Bool) (i : Fin k)
    (cfg : Cfg k Bool (Fin (w.length + 1)) input) (s : ℕ) :
    Cfg k Bool (Fin (w.length + 1)) input :=
  { cfg with
    state := some ⟨min s w.length, by omega⟩
    workTapes := Function.update cfg.workTapes i (tapeOf (w.drop (w.length - s)))
    workTapePos := Function.update cfg.workTapePos i (s : ℤ) }

/-- {name}`constWalk` from a parked empty register runs {lit}`w.length + 1`
steps and leaves it holding {lit}`w` with its head at {lit}`w.length`. -/
theorem constWalk_runsTo {k : ℕ} {input : List Bool} (w : List Bool) (i : Fin k)
    (cfg : Cfg k Bool (Fin (w.length + 1)) input) (hq : cfg.state = some 0)
    (hw : cfg.workTapes i = tapeOf []) (hp : cfg.workTapePos i = 0) (B : ℕ)
    (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (constWalk w i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf w)
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
      (w.length + 1) B := by
  have htrS : ∀ (s : ℕ) (hs : s < w.length) (hidx : s < w.reverse.length)
      (inp : Option Bool) (work : Fin k → Option Bool),
      (constWalk w i).tr ⟨s, by omega⟩ inp work =
        { inputMove := 0
          workActions := fun j ↦
            if j = i then (some (some (w.reverse[s]'hidx)), 1) else (none, 0)
          outS := none, q' := some ⟨s + 1, by omega⟩ } := by
    intro s hs hidx inp work
    simp only [constWalk]
    rw [dite_eq_left hs]
  have htrN : ∀ (s : ℕ) (hlt : s < w.length + 1) (hs : ¬ s < w.length)
      (inp : Option Bool) (work : Fin k → Option Bool),
      (constWalk w i).tr ⟨s, hlt⟩ inp work =
        { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none } := by
    intro s hlt hs inp work
    simp only [constWalk]
    rw [dite_eq_right hs]
  have houtS : ∀ (q : Fin (w.length + 1)) (inp : Option Bool) (work : Fin k → Option Bool),
      ((constWalk w i).tr q inp work).outS = none := by
    intro q inp work
    simp only [constWalk]
    split <;> rfl
  have hout : ∀ s : ℕ, (constWalk w i).outputSymbol (constCfg w i cfg s) = none := by
    intro s
    change ((constWalk w i).tr ⟨min s w.length, by omega⟩ (constCfg w i cfg s).inputSymbol
      (constCfg w i cfg s).workTapeSymbols).outS = none
    exact houtS _ _ _
  have hstate : ∀ (s : ℕ) (hs : s ≤ w.length),
      (constCfg w i cfg s).state = some ⟨s, by omega⟩ := by
    intro s hs
    change some (⟨min s w.length, by omega⟩ : Fin (w.length + 1)) = _
    congr 1
    apply Fin.ext
    change min s w.length = s
    omega
  have hstep : ∀ s : ℕ, s < w.length →
      (constWalk w i).step (constCfg w i cfg s) = constCfg w i cfg (s + 1) := by
    intro s hs
    have hidx : s < w.reverse.length := by simp; omega
    rw [step_of_state _ _ ⟨s, by omega⟩ (hstate s (by omega)), htrS s hs hidx _ _]
    apply Cfg.ext
    · change (some ⟨s + 1, by omega⟩ : Option (Fin (w.length + 1))) =
        some ⟨min (s + 1) w.length, by omega⟩
      congr 1
      apply Fin.ext
      change s + 1 = min (s + 1) w.length
      omega
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      dsimp only
      by_cases hj : j = i
      · rw [hj, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes i
            (tapeOf (w.drop (w.length - s))) i)
            (Function.update cfg.workTapePos i (s : ℤ) i) (some (w.reverse[s]'hidx)) =
          Function.update cfg.workTapes i (tapeOf (w.drop (w.length - (s + 1)))) i
        rw [Function.update_self, Function.update_self, Function.update_self,
          drop_length_sub_succ w s hs, tapeOf_cons,
          show (((w.drop (w.length - s)).length : ℕ) : ℤ) = (s : ℤ) by
            rw [List.length_drop]; omega]
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapes i (tapeOf (w.drop (w.length - s))) j =
          Function.update cfg.workTapes i (tapeOf (w.drop (w.length - (s + 1)))) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · funext j
      dsimp only
      by_cases hj : j = i
      · rw [hj, ite_eq_left rfl]
        change Function.update cfg.workTapePos i (s : ℤ) i + ((1 : SignType) : ℤ) =
          Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ) i
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapePos i (s : ℤ) j + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj, SignType.coe_zero, add_zero]
  have hhalt : (constWalk w i).step (constCfg w i cfg w.length) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf w)
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) } := by
    rw [step_of_state _ _ ⟨w.length, by omega⟩ (hstate w.length (le_refl _)),
      htrN w.length (by omega) (by omega) _ _]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      change Function.update cfg.workTapes i (tapeOf (w.drop (w.length - w.length))) j =
        Function.update cfg.workTapes i (tapeOf w) j
      rw [Nat.sub_self, List.drop_zero]
    · funext j
      change Function.update cfg.workTapePos i ((w.length : ℕ) : ℤ) j + ((0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i (w.length : ℤ) j
      rw [SignType.coe_zero, add_zero]
  have hzero : constCfg w i cfg 0 = cfg := by
    apply Cfg.ext
    · change some (⟨min 0 w.length, by omega⟩ : Fin (w.length + 1)) = cfg.state
      rw [hq]
      rfl
    · rfl
    · change Function.update cfg.workTapes i (tapeOf (w.drop (w.length - 0))) = cfg.workTapes
      rw [Nat.sub_zero, List.drop_length, ← hw, Function.update_eq_self]
    · change Function.update cfg.workTapePos i ((0 : ℕ) : ℤ) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega, Function.update_eq_self]
  have key := RunsTo.ofFamily (constWalk w i) (constCfg w i cfg) w.length B _
    (fun _ _ ↦ Option.some_ne_none _) hstep hhalt rfl (fun s _ ↦ hout s)
    (fun s hs j ↦ update_workTapePos_bounds i hpos (s : ℤ) (by omega) (by omega) j)
    (fun j ↦ update_workTapePos_bounds i hpos (w.length : ℤ) (by omega) (by omega) j)
  rwa [hzero] at key

end

end Geb.SizeBounded.Machine
