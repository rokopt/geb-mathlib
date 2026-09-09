/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Geb.Prototypes.Computability.BitTreeScanner.Machine

set_option doc.verso true

/-!
# The one-pass tree scanner's transition, resolved

{name}`Geb.BitTreeScanner.bitTreeScanner`'s transition resolved at each case of
its table, and the machine's configuration after every step shown to be the
closed form {name}`Geb.BitTreeScanner.cfgOf` at the prefix read so far. One
step against the closed form is one step of {name}`Geb.BitTreeScanner.scanStep`
against the scan, and the input's end is the emitting step, whose symbol is
{name}`Geb.BitTreeScanner.validBool` at the input.

## Main statements

* {lit}`Geb.BitTreeScanner.cfgOf_inputSymbol`,
  {lit}`Geb.BitTreeScanner.cfgOf_inputSymbol_end` — the input symbol at the
  closed form, short of the input's end and at it.
* {lit}`Geb.BitTreeScanner.tr_first_pair` through
  {lit}`Geb.BitTreeScanner.tr_dead_end` — the transition resolved at each
  case of its table.
* {lit}`Geb.BitTreeScanner.cfgOf_step_of_tr_eq_advance` — one step from the
  closed form, given the resolved transition and the scan's step: the closed
  form at the prefix extended by one bit, and nothing emitted.
* {lit}`Geb.BitTreeScanner.cfgOf_step` — the step at every case.
* {lit}`Geb.BitTreeScanner.configs_cfgOf` — the configuration and the output
  at every step up to the input's length.
* {lit}`Geb.BitTreeScanner.halt_of_tr`, {lit}`Geb.BitTreeScanner.cfgOf_end` —
  the emitting step: the machine halts, and the symbol it emits is the
  decision function's value.
* {lit}`Geb.BitTreeScanner.halts_at`, {lit}`Geb.BitTreeScanner.outputString_eq`
  — the machine halts after {lit}`w.length + 1` steps having emitted that one
  symbol.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the machine's behaviour under {name}`Turing.MultiTapeTM.step`,
{name}`Turing.MultiTapeTM.configs` and {name}`Turing.MultiTapeTM.outputString`,
and its statements read the input through
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`; each of those depends on
{lit}`Classical.choice` through Cslib's {lit}`Cfg.inputSymbol` and
{name}`Turing.MultiTapeTM.inputSymbolInner`, so nothing here can be stated
choice-free.

A transition resolution is stated over an arbitrary work-symbol function
wherever the table's row does not read it, and at a constant function where
it does, which is the form {name}`Geb.BitTreeScanner.cfgOf_workTapeSymbols_eq`
reduces to at a literal count. A row that is a catch-all in the input column
is resolved at {lit}`some (boolEmb b)` by cases on the bit.

The step across every case is one lemma, {lit}`cfgOf_step_of_tr_eq_advance`,
taking the resolved transition, the scan's mode and count after the bit, and
the write: the marker is written at the first step and at no other, so the
write is a function of the prefix's length alone. {lit}`cfgOf_step` supplies
those at each case, so the configuration equality is proved once.

## Tags

Turing machine, transition, tree, prefix code
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner
open Geb.TreeScanner (boolEmb step_of_state)

section InputSymbol

/-- Short of the input's end the closed form reads the bit at its index. -/
theorem cfgOf_inputSymbol (w : List Bool) (k : ℕ) (h : k < w.length) :
    (cfgOf w k (Nat.le_of_lt h)).inputSymbol = some (boolEmb w[k]) := by
  have hi := inputSymbolInner (cfg := cfgOf w k (Nat.le_of_lt h)) k
    (by rw [cfgOf_inputPos_val]; omega) (by rw [List.length_map]; exact h)
  rw [hi, List.getElem_map]

/-- At the input's end the closed form reads blank. This takes
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`'s second guard, an equality at
{lit}`ℕ`. -/
theorem cfgOf_inputSymbol_end (w : List Bool) :
    (cfgOf w w.length (Nat.le_refl _)).inputSymbol = none := by
  have hend : ((cfgOf w w.length (Nat.le_refl _)).inputPos : ℕ) =
      (w.map boolEmb).length + 1 := by
    rw [cfgOf_inputPos_val, List.length_map]
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

end InputSymbol

section Transition

variable (work : Fin 1 → Option (Fin 2))

/-- The first step over a pair bit writes the marker, moves the work head
right and enters the main state. -/
theorem tr_first_pair :
    bitTreeScanner.tr stFirst (some (boolEmb true)) work = advance stMain (some (some 0), 1) := rfl

/-- The first step over a leaf bit writes the marker and opens the leaf. -/
theorem tr_first_leaf :
    bitTreeScanner.tr stFirst (some (boolEmb false)) work =
      advance stLeafOpen (some (some 0), 0) := rfl

/-- The first step at the input's end rejects. -/
theorem tr_first_end : bitTreeScanner.tr stFirst none work = halt 0 := rfl

/-- A pair bit in the main state moves the work head right. -/
theorem tr_main_pair :
    bitTreeScanner.tr stMain (some (boolEmb true)) work = advance stMain (none, 1) := rfl

/-- A leaf bit in the main state opens the leaf. -/
theorem tr_main_leaf :
    bitTreeScanner.tr stMain (some (boolEmb false)) work = advance stLeafOpen (none, 0) := rfl

/-- The main state at the input's end rejects. -/
theorem tr_main_end : bitTreeScanner.tr stMain none work = halt 0 := rfl

/-- Inside a leaf, {lit}`true` announces a payload bit. -/
theorem tr_leafOpen_payload :
    bitTreeScanner.tr stLeafOpen (some (boolEmb true)) work = advance stLeafBit (none, 0) := rfl

/-- Inside a leaf, {lit}`false` under the marker closes the last pending tree:
the scan completes. -/
theorem tr_leafOpen_close_last :
    bitTreeScanner.tr stLeafOpen (some (boolEmb false)) (fun _ ↦ some 0) =
      advance stDone (none, 0) := rfl

/-- Inside a leaf, {lit}`false` over a blank cell closes the leaf and moves the
work head left: the next tree is expected. -/
theorem tr_leafOpen_close :
    bitTreeScanner.tr stLeafOpen (some (boolEmb false)) (fun _ ↦ none) =
      advance stMain (none, -1) := rfl

/-- A leaf open at the input's end rejects. -/
theorem tr_leafOpen_end : bitTreeScanner.tr stLeafOpen none work = halt 0 := rfl

/-- A payload bit returns to the leaf's open state. -/
theorem tr_leafBit_bit (b : Bool) :
    bitTreeScanner.tr stLeafBit (some (boolEmb b)) work = advance stLeafOpen (none, 0) := by
  cases b <;> rfl

/-- A payload bit expected at the input's end rejects. -/
theorem tr_leafBit_end : bitTreeScanner.tr stLeafBit none work = halt 0 := rfl

/-- A bit after completion fails. -/
theorem tr_done_bit (b : Bool) :
    bitTreeScanner.tr stDone (some (boolEmb b)) work = advance stDead (none, 0) := by
  cases b <;> rfl

/-- Completion at the input's end accepts. -/
theorem tr_done_end : bitTreeScanner.tr stDone none work = halt 1 := rfl

/-- Failure absorbs a bit. -/
theorem tr_dead_bit (b : Bool) :
    bitTreeScanner.tr stDead (some (boolEmb b)) work = advance stDead (none, 0) := by
  cases b <;> rfl

/-- Failure at the input's end rejects. -/
theorem tr_dead_end : bitTreeScanner.tr stDead none work = halt 0 := rfl

end Transition

section Step

/-- One step from the closed form, given the transition resolved to a reading
step and the scan's step: the closed form at the prefix extended by one bit,
and nothing emitted. The marker is written at the first step and at no
other. -/
theorem cfgOf_step_of_tr_eq_advance (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) (q q' : Fin 6)
    (wr : Option (Option (Fin 2))) (d : SignType)
    (hq : stateOf k (scanFinal (w.take k)).mode = q)
    (htr : bitTreeScanner.tr q (cfgOf w k (by omega)).inputSymbol
      (cfgOf w k (by omega)).workTapeSymbols = advance q' (wr, d))
    (hq' : stateOf (k + 1) (scanFinal (w.take (k + 1))).mode = q')
    (hwr : wr = if k = 0 then some (some 0) else none)
    (hcount : ((scanFinal (w.take (k + 1))).count : ℤ) =
      (scanFinal (w.take k)).count + (d : ℤ)) :
    bitTreeScanner.step (cfgOf w k (by omega)) = cfgOf w (k + 1) h ∧
      bitTreeScanner.outputSymbol (cfgOf w k (by omega)) = none := by
  have hpos : moveInputPos (cfgOf w k (by omega)).inputPos SignType.pos =
      (cfgOf w (k + 1) h).inputPos := by
    rw [moveInputPos_pos_of_ne_right _ (by rw [cfgOf_inputPos_val, List.length_map]; omega)]
    exact Fin.ext rfl
  have hst : (cfgOf w k (by omega)).state = some q := by rw [cfgOf_state, hq]
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hst, htr]
    refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only [advance]
    · rw [cfgOf_state, hq']
    · exact hpos
    · funext i z
      subst hwr
      cases k with
      | zero =>
        rw [ite_eq_left rfl]
        change Function.update ((cfgOf w 0 (by omega)).workTapes i)
          ((cfgOf w 0 (by omega)).workTapePos i) (some 0) z = (cfgOf w 1 h).workTapes i z
        rw [Function.update_apply, cfgOf_workTapes, cfgOf_workTapes, cfgOf_workTapePos,
          List.take_zero, scanFinal_nil]
        simp [init]
      | succ k =>
        rw [ite_eq_right (Nat.succ_ne_zero k)]
        change (cfgOf w (k + 1) (by omega)).workTapes i z = (cfgOf w (k + 1 + 1) h).workTapes i z
        rw [cfgOf_workTapes, cfgOf_workTapes]
        simp
    · funext i
      rw [cfgOf_workTapePos, cfgOf_workTapePos, hcount]
  · unfold outputSymbol
    rw [hst]
    change (bitTreeScanner.tr q (cfgOf w k (by omega)).inputSymbol
      (cfgOf w k (by omega)).workTapeSymbols).outS = none
    rw [htr]
    rfl

/-- One step from the closed form is the closed form at the prefix extended by
one bit, and nothing is emitted: {name}`cfgOf_step_of_tr_eq_advance` at every
case of the state, the bit and, at a leaf's closing bit, the pending count. -/
theorem cfgOf_step (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    bitTreeScanner.step (cfgOf w k (by omega)) = cfgOf w (k + 1) h ∧
      bitTreeScanner.outputSymbol (cfgOf w k (by omega)) = none := by
  have hscan := scanFinal_take_succ w k (by omega)
  have hin := cfgOf_inputSymbol w k (by omega)
  have hwork := cfgOf_workTapeSymbols_eq w k (by omega)
  cases k with
  | zero =>
    rw [List.take_zero, scanFinal_nil] at hscan
    cases hb : w[0] with
    | true =>
      exact cfgOf_step_of_tr_eq_advance w 0 h stFirst stMain (some (some 0)) 1 rfl
        (by rw [hin, hb]; exact tr_first_pair _) (by rw [hscan, hb]; rfl) rfl
        (by rw [hscan, hb, List.take_zero, scanFinal_nil]; rfl)
    | false =>
      exact cfgOf_step_of_tr_eq_advance w 0 h stFirst stLeafOpen (some (some 0)) 0 rfl
        (by rw [hin, hb]; exact tr_first_leaf _) (by rw [hscan, hb]; rfl) rfl
        (by rw [hscan, hb, List.take_zero, scanFinal_nil]; rfl)
  | succ k =>
    rcases hs : scanFinal (w.take (k + 1)) with ⟨m, c⟩
    rw [hs] at hscan hwork
    cases m with
    | term =>
      cases hb : w[k + 1] with
      | true =>
        exact cfgOf_step_of_tr_eq_advance w (k + 1) h stMain stMain none 1 (by rw [hs]; rfl)
          (by rw [hin, hb]; exact tr_main_pair _) (by rw [hscan, hb]; rfl) rfl
          (by rw [hscan, hb, hs, scanStep_term_true, SignType.coe_one]; dsimp only; omega)
      | false =>
        exact cfgOf_step_of_tr_eq_advance w (k + 1) h stMain stLeafOpen none 0 (by rw [hs]; rfl)
          (by rw [hin, hb]; exact tr_main_leaf _) (by rw [hscan, hb]; rfl) rfl
          (by rw [hscan, hb, hs, scanStep_term_false, SignType.coe_zero]; dsimp only; omega)
    | leafOpen =>
      cases hb : w[k + 1] with
      | true =>
        exact cfgOf_step_of_tr_eq_advance w (k + 1) h stLeafOpen stLeafBit none 0 (by rw [hs]; rfl)
          (by rw [hin, hb]; exact tr_leafOpen_payload _) (by rw [hscan, hb]; rfl) rfl
          (by rw [hscan, hb, hs, scanStep_leafOpen_true, SignType.coe_zero]; dsimp only; omega)
      | false =>
        cases c with
        | zero =>
          exact cfgOf_step_of_tr_eq_advance w (k + 1) h stLeafOpen stDone none 0 (by rw [hs]; rfl)
            (by rw [hin, hb, hwork]; exact tr_leafOpen_close_last) (by rw [hscan, hb]; rfl) rfl
            (by rw [hscan, hb, hs, scanStep_leafOpen_false, close_zero, SignType.coe_zero]; rfl)
        | succ c =>
          exact cfgOf_step_of_tr_eq_advance w (k + 1) h stLeafOpen stMain none (-1)
            (by rw [hs]; rfl) (by rw [hin, hb, hwork]; exact tr_leafOpen_close)
            (by rw [hscan, hb]; rfl) rfl
            (by
              rw [hscan, hb, hs, scanStep_leafOpen_false, close_succ, SignType.coe_neg_one]
              dsimp only
              omega)
    | leafBit =>
      exact cfgOf_step_of_tr_eq_advance w (k + 1) h stLeafBit stLeafOpen none 0 (by rw [hs]; rfl)
        (by rw [hin]; exact tr_leafBit_bit _ _) (by rw [hscan, scanStep_leafBit]; rfl) rfl
        (by rw [hscan, hs, scanStep_leafBit, SignType.coe_zero]; dsimp only; omega)
    | done =>
      exact cfgOf_step_of_tr_eq_advance w (k + 1) h stDone stDead none 0 (by rw [hs]; rfl)
        (by rw [hin]; exact tr_done_bit _ _) (by rw [hscan, scanStep_done]; rfl) rfl
        (by rw [hscan, hs, scanStep_done, SignType.coe_zero]; dsimp only; omega)
    | dead =>
      exact cfgOf_step_of_tr_eq_advance w (k + 1) h stDead stDead none 0 (by rw [hs]; rfl)
        (by rw [hin]; exact tr_dead_bit _ _) (by rw [hscan, scanStep_dead]; rfl) rfl
        (by rw [hscan, hs, scanStep_dead, SignType.coe_zero]; dsimp only; omega)

/-- The configuration and the output at every step up to the input's length:
the closed form at the prefix read, and nothing emitted. Both conjuncts run in
one recursion, the output obligation being what the emitting step needs
alongside the configuration. -/
theorem configs_cfgOf (w : List Bool) :
    ∀ k, ∀ h : k ≤ w.length,
      bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb)) k = cfgOf w k h ∧
        bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) k = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨by rw [configs_zero, cfgOf_zero], rfl⟩
  · intro k ih h
    obtain ⟨hc, ho⟩ := ih (by omega)
    obtain ⟨hstep, hout⟩ := cfgOf_step w k h
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact hstep
    · rw [outputString_succ, ho, hc, hout]
      rfl

end Step

section Emission

/-- A step whose transition resolves to a halting step halts the machine and
emits the halting step's symbol. -/
theorem halt_of_tr {input : List (Fin 2)} (cfg : Cfg 1 (Fin 2) (Fin 6) input) (q : Fin 6)
    (hq : cfg.state = some q) (b : Fin 2)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = halt b) :
    (bitTreeScanner.step cfg).state = none ∧ bitTreeScanner.outputSymbol cfg = some b := by
  refine ⟨?_, ?_⟩
  · rw [step_of_state _ _ q hq, htr]
    rfl
  · unfold outputSymbol
    rw [hq]
    change (bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = some b
    rw [htr]
    rfl

/-- At the input's end the machine halts, and the symbol it emits is the
decision function's value: the completed state accepts, and every other
rejects. -/
theorem cfgOf_end (w : List Bool) :
    (bitTreeScanner.step (cfgOf w w.length (Nat.le_refl _))).state = none ∧
      bitTreeScanner.outputSymbol (cfgOf w w.length (Nat.le_refl _)) =
        some (boolEmb (validBool w)) := by
  have hin := cfgOf_inputSymbol_end w
  rcases hs : scanFinal w with ⟨m, c⟩
  have hst : (cfgOf w w.length (Nat.le_refl _)).state = some (stateOf w.length m) := by
    rw [cfgOf_state, List.take_length, hs]
  have hval : validBool w = decide (m = .done) := by
    unfold validBool
    rw [hs]
  rw [hval]
  cases m with
  | term =>
    by_cases hn : w.length = 0
    · exact halt_of_tr _ stFirst (by rw [hst, stateOf, ite_eq_left hn]) 0
        (by rw [hin]; exact tr_first_end _)
    · exact halt_of_tr _ stMain (by rw [hst, stateOf, ite_eq_right hn]) 0
        (by rw [hin]; exact tr_main_end _)
  | leafOpen => exact halt_of_tr _ stLeafOpen hst 0 (by rw [hin]; exact tr_leafOpen_end _)
  | leafBit => exact halt_of_tr _ stLeafBit hst 0 (by rw [hin]; exact tr_leafBit_end _)
  | done => exact halt_of_tr _ stDone hst 1 (by rw [hin]; exact tr_done_end _)
  | dead => exact halt_of_tr _ stDead hst 0 (by rw [hin]; exact tr_dead_end _)

/-- The machine halts after {lit}`w.length + 1` steps: one per bit, and the
emitting step. -/
theorem halts_at (w : List Bool) :
    (bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb)) (w.length + 1)).state =
      none := by
  rw [configs_succ_eq_step', (configs_cfgOf w w.length (Nat.le_refl _)).1]
  exact (cfgOf_end w).1

/-- Over the same {lit}`w.length + 1` steps the machine emits one symbol, the
decision function's value at the input. -/
theorem outputString_eq (w : List Bool) :
    bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) (w.length + 1) =
      [boolEmb (validBool w)] := by
  rw [outputString_succ, (configs_cfgOf w w.length (Nat.le_refl _)).2,
    (configs_cfgOf w w.length (Nat.le_refl _)).1, (cfgOf_end w).2]
  rfl

end Emission

end Geb.BitTreeScanner
