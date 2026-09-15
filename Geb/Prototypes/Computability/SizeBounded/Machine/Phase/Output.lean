/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Emit
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The emitting phase

One phase writes to the output tape: {lit}`emitLeft` walks a register's head
left from the cell holding the word's first element, emitting each bit it
reads, and halts on reading the blank before the word. A register holds its
word in the reversed layout of {name}`Geb.SizeBounded.Machine.tapeOf`, whose
cell {lit}`length - 1` holds the word's first element and whose cell
{lit}`0` holds its last, so the walk emits the word in order.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`emitLeft` — walk one head left, emitting each bit read.
* {lit}`emitCfg` — the closed form of the walk's configurations.

# Main statements

* {lit}`emitLeft_emits` — the run of the machine, naming the halted
  configuration, the emitted word and the step count.

# Tags

Turing machine, output, register
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Walk register {lit}`i`'s head left, emitting each bit read, until it reads a
blank. -/
@[expose] def emitLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = i then (none, -1) else (none, 0)
        outS := some b
        q' := some () }
    | none => { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- The configuration of {name}`emitLeft` after {lit}`s` steps from the head at
the last cell of a register holding {lit}`w`. -/
@[expose] def emitCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (w : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapePos := Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) }

/-- {name}`emitLeft` from the head at cell {lit}`w.length - 1` of a register
holding {lit}`w` runs {lit}`w.length + 1` steps, emits {lit}`w`, and leaves the
head at cell {lit}`-1`. -/
theorem emitLeft_emits {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = (w.length : ℤ) - 1) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Emits (emitLeft i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      w (w.length + 1) B := by
  have htrSome : ∀ (inp : Option Bool) (work : Fin k → Option Bool) (b : Bool), work i = some b →
      (emitLeft i).tr () inp work =
        { inputMove := 0
          workActions := fun l ↦ if l = i then (none, -1) else (none, 0)
          outS := some b
          q' := some () } := by
    intro inp work b h
    simp only [emitLeft, h]
  have htrNone : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = none →
      (emitLeft i).tr () inp work =
        { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none } := by
    intro inp work h
    simp only [emitLeft, h]
  have hsym : ∀ s : ℕ, (emitCfg i cfg w s).workTapeSymbols i =
      tapeOf w ((w.length : ℤ) - 1 - s) := by
    intro s
    change cfg.workTapes i (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) i) = _
    rw [Function.update_self, hw]
  have hbit : ∀ s, (hs : s < w.length) → (emitCfg i cfg w s).workTapeSymbols i = some w[s] := by
    intro s hs
    rw [hsym s, tapeOf_of_lt w ((w.length : ℤ) - 1 - s) (by omega) (by omega),
      getElem_congr_idx (show ((w.length : ℤ) - 1 - s).toNat = w.length - 1 - s by omega),
      List.getElem_reverse,
      getElem_congr_idx (show w.length - 1 - (w.length - 1 - s) = s by omega)]
  have hnone : (emitCfg i cfg w w.length).workTapeSymbols i = none := by
    rw [hsym w.length]
    exact tapeOf_neg w _ (by omega)
  have hstep : ∀ s < w.length,
      (emitLeft i).step (emitCfg i cfg w s) = emitCfg i cfg w (s + 1) := by
    intro s hs
    have hfst : ∀ l : Fin k, (((emitLeft i).tr () (emitCfg i cfg w s).inputSymbol
        (emitCfg i cfg w s).workTapeSymbols).workActions l).1 = none := by
      intro l
      rw [htrSome _ _ _ (hbit s hs)]
      simp only [apply_ite Prod.fst, ite_self]
    have hsnd : ∀ l : Fin k, (((emitLeft i).tr () (emitCfg i cfg w s).inputSymbol
        (emitCfg i cfg w s).workTapeSymbols).workActions l).2 =
        if l = i then (-1 : SignType) else 0 := by
      intro l
      rw [htrSome _ _ _ (hbit s hs)]
      simp only [apply_ite Prod.snd]
    rw [step_of_state _ _ () rfl]
    simp only [hfst, hsnd]
    rw [htrSome _ _ _ (hbit s hs)]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext l
      change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) l +
          ((if l = i then -1 else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ)) l
      by_cases hl : l = i
      · subst hl
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, SignType.coe_neg_one]
        omega
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, ite_eq_right hl,
          SignType.coe_zero, add_zero]
  have hhalt : (emitLeft i).step (emitCfg i cfg w w.length) =
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) } := by
    rw [step_of_state _ _ () rfl, htrNone _ _ hnone]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext l
      change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ)) l +
          ((0 : SignType) : ℤ) = Function.update cfg.workTapePos i (-1) l
      rw [show ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ)) = -1 by omega, SignType.coe_zero,
        add_zero]
  have hemit : ∀ s, (hs : s < w.length) →
      (emitLeft i).outputSymbol (emitCfg i cfg w s) = some w[s] := by
    intro s hs
    change ((emitLeft i).tr () (emitCfg i cfg w s).inputSymbol
      (emitCfg i cfg w s).workTapeSymbols).outS = some w[s]
    rw [htrSome _ _ _ (hbit s hs)]
  have hemitNone : (emitLeft i).outputSymbol (emitCfg i cfg w w.length) = none := by
    change ((emitLeft i).tr () (emitCfg i cfg w w.length).inputSymbol
      (emitCfg i cfg w w.length).workTapeSymbols).outS = none
    rw [htrNone _ _ hnone]
  have hout : ∀ s ≤ w.length, w.take (s + 1) =
      w.take s ++ ((emitLeft i).outputSymbol (emitCfg i cfg w s)).toList := by
    intro s hs
    rcases Nat.lt_or_ge s w.length with h | h
    · rw [hemit s h, List.take_succ_eq_append_getElem h]
      rfl
    · rw [show s = w.length by omega, hemitNone,
        List.take_of_length_le (show w.length ≤ w.length + 1 by omega),
        List.take_of_length_le (le_refl w.length)]
      exact (List.append_nil w).symm
  have hzero : emitCfg i cfg w 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) =
        cfg.workTapePos
      rw [show ((w.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega,
        Function.update_eq_self]
  have key : Emits (emitLeft i) (emitCfg i cfg w 0)
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      (w.take (w.length + 1)) (w.length + 1) B :=
    Emits.ofFamily (emitLeft i) (emitCfg i cfg w) (fun s ↦ w.take s) w.length B
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl rfl hout
      (fun s hs l ↦
        update_workTapePos_bounds i hpos ((w.length : ℤ) - 1 - s) (by omega) (by omega) l)
      (fun l ↦ update_workTapePos_bounds i hpos (-1) (by omega) (by omega) l)
  rwa [hzero, List.take_of_length_le (show w.length ≤ w.length + 1 by omega)] at key

end

end Geb.SizeBounded.Machine
