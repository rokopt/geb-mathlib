/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Transition

set_option doc.verso true

/-!
# The pending count's chains

The runs that increment and decrement the redundant counter of the pending
count on the first tape: a pair bit's increment, from the closed form at a
state expecting a tree, carrying outward through the twos and returning to
the base marker, where the bit is consumed; and a leaf's closing decrement,
from the configuration the erasure of the leaf's digits ends in, borrowing
outward through the zeros, testing a lowered one for being the top and
erasing it when it is, and returning to the base marker. Each runs in the
steps {name}`Geb.BitTreeScanner.incCost` and {name}`Geb.BitTreeScanner.decCost` assign.

## Main statements

* {lit}`Geb.BitTreeScanner.run_inc` — a pair bit's increment runs in
  {name}`Geb.BitTreeScanner.incCost` steps to the closed form at the next bit.
* {lit}`Geb.BitTreeScanner.run_dec_borrow`,
  {lit}`Geb.BitTreeScanner.run_dec_of_ne_nil` — a decrement of a counter
  that is not empty runs in {name}`Geb.BitTreeScanner.decCost` steps to the
  configuration expecting the next tree.
* {lit}`Geb.BitTreeScanner.run_close` — a leaf's closing decrement runs in
  {name}`Geb.BitTreeScanner.decCost` steps to the closed form at the state the closed
  tree leaves.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`, as
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic`'s
implementation notes explain.

The borrow's family begins at the configuration the erasure ends in, whose
state is the erasing one, and whose transition at the base marker mirrors the
borrowing state's, so the family's state is the erasing state at cell
{lit}`0` and the borrowing state above.

## Tags

Turing machine, redundant binary counter, carry, borrow, amortised analysis
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Inc

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (c : ℕ) (l : List Redundant.Digit)

/-- The step of an increment without a carry: the lowest digit is raised and
the pair bit consumed. -/
theorem cfgAt_step_pair_low (h : k < w.length) (hb : w[k] = true)
    (hc : Redundant.carryLength l = 0) :
    bitTreeScanner.step (cfgAt w k hk ⟨.term, c, 0, []⟩ l) =
        cfgAt w (k + 1) h ⟨.term, c + 1, 0, []⟩ (Redundant.inc l) ∧
      bitTreeScanner.outputSymbol (cfgAt w k hk ⟨.term, c, 0, []⟩ l) = none := by
  have hlow := tapeCount_carry l
  rw [hc] at hlow
  obtain ⟨hstep, hout⟩ := step_advance (cfgAt w k hk ⟨.term, c, 0, []⟩ l) stMain stMain
    (some (some (raise (tapeCount l 1))), 0) idle idle rfl
    (by
      rw [workTapeSymbols_cfgAt_term, inputSymbol_of_inputPos w _ k h rfl, hb]
      exact tr_main_pair_notTwo _ _ _ (by simpa using hlow))
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (cfgAt w k hk ⟨.term, c, 0, []⟩ l).inputPos SignType.pos =
      (cfgAt w (k + 1) h ⟨.term, c + 1, 0, []⟩ (Redundant.inc l)).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change k + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j z
    match j with
    | 0 =>
      have hr := raise_tapeCount_carry l
      rw [hc] at hr
      change Function.update (tapeCount l) 1 (some (raise (tapeCount l 1))) z =
        tapeCount (Redundant.inc l) z
      rw [Function.update_apply, tapeCount_inc, hc, Nat.cast_zero, zero_add]
      by_cases hz : z = 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left hz]
        simpa using hr
      · rw [ite_eq_right hz, ite_eq_right (by omega), ite_eq_right hz]
    | 1 => rfl
    | 2 => rfl
  · exact vec3_ext (add_zero _) (add_zero _) (add_zero _)

/-- The step beginning a carry: at a two at the lowest digit, the digit
becomes a one and the head moves outward. -/
theorem cfgAt_step_pair_two (h : k < w.length) (hb : w[k] = true)
    (hc : 0 < Redundant.carryLength l) :
    bitTreeScanner.step (cfgAt w k hk ⟨.term, c, 0, []⟩ l) = incCarryCfg w k hk l 1 ∧
      bitTreeScanner.outputSymbol (cfgAt w k hk ⟨.term, c, 0, []⟩ l) = none := by
  have hsym : tapeCount l 1 = some 2 := by
    rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl,
      tapeCount_of_lt l 0 (by have := Redundant.carryLength_le_length l; omega),
      Redundant.getD_of_lt_carryLength l 0 hc]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (cfgAt w k hk ⟨.term, c, 0, []⟩ l) stMain stIncCarry
    (some (some 1), 1) idle idle rfl
    (by
      rw [workTapeSymbols_cfgAt_term, inputSymbol_of_inputPos w _ k h rfl, hb, hsym]
      exact tr_main_pair_two _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update (tapeCount l) 1 (some 1) z =
        if 1 ≤ z ∧ z ≤ ((1 : ℕ) : ℤ) then some 1 else tapeCount l z
      rw [Function.update_apply]
      by_cases hz : z = 1
      · rw [ite_eq_left hz, ite_eq_left (by omega)]
      · rw [ite_eq_right hz, ite_eq_right (by omega)]
    | 1 => exact congrFun (tapeLeaf_blank ⟨.term, c, 0, []⟩ (Or.inl rfl)) z
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (1 : ℤ) + ((1 : SignType) : ℤ) = ((1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      rfl
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- One step of the carry over a two. -/
theorem incCarryCfg_step (j : ℕ) (hjk : j < Redundant.carryLength l) :
    bitTreeScanner.step (incCarryCfg w k hk l j) = incCarryCfg w k hk l (j + 1) ∧
      bitTreeScanner.outputSymbol (incCarryCfg w k hk l j) = none := by
  have hk' := Redundant.carryLength_le_length l
  have hsym : (incCarryCfg w k hk l j).workTapeSymbols = ![some 2, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![if 1 ≤ ((j : ℤ) + 1) ∧ ((j : ℤ) + 1) ≤ j then some 1 else tapeCount l ((j : ℤ) + 1),
      tapeBase 0, tapeDigits w.length.bits 0] = _
    rw [ite_eq_right (by omega), tapeCount_of_lt _ _ (by omega),
      Redundant.getD_of_lt_carryLength l j hjk]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (incCarryCfg w k hk l j) stIncCarry stIncCarry
    (some (some 1), 1) idle idle rfl (by rw [hsym]; exact tr_incCarry_two _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j' z
    match j' with
    | 0 =>
      change Function.update (fun z ↦ if 1 ≤ z ∧ z ≤ (j : ℤ) then some 1 else tapeCount l z)
        ((j : ℤ) + 1) (some 1) z =
        if 1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ) then some 1 else tapeCount l z
      rw [Function.update_apply]
      by_cases hz : z = (j : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_left (by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (j : ℤ)
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    | 1 => rfl
    | 2 => rfl
  · funext j'
    match j' with
    | 0 =>
      change (j : ℤ) + 1 + ((1 : SignType) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step absorbing the carry: at a digit that is not a two, the digit is
raised and the return begins. -/
theorem incCarryCfg_flip :
    bitTreeScanner.step (incCarryCfg w k hk l (Redundant.carryLength l)) =
        incBackCfg w k hk l (Redundant.carryLength l) ∧
      bitTreeScanner.outputSymbol (incCarryCfg w k hk l (Redundant.carryLength l)) = none := by
  have hsym : (incCarryCfg w k hk l (Redundant.carryLength l)).workTapeSymbols =
      ![tapeCount l ((Redundant.carryLength l : ℤ) + 1), some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![if 1 ≤ ((Redundant.carryLength l : ℤ) + 1) ∧
        ((Redundant.carryLength l : ℤ) + 1) ≤ Redundant.carryLength l then some 1
      else tapeCount l ((Redundant.carryLength l : ℤ) + 1), tapeBase 0,
      tapeDigits w.length.bits 0] = _
    rw [ite_eq_right (by omega)]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (incCarryCfg w k hk l (Redundant.carryLength l)) stIncCarry
    stIncBack (some (some (raise (tapeCount l ((Redundant.carryLength l : ℤ) + 1)))), -1) idle idle
    rfl (by rw [hsym]; exact tr_incCarry_notTwo _ _ _ _ (tapeCount_carry l))
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (Redundant.carryLength l : ℤ) then some 1 else tapeCount l z)
        ((Redundant.carryLength l : ℤ) + 1)
        (some (raise (tapeCount l ((Redundant.carryLength l : ℤ) + 1)))) z =
        tapeCount (Redundant.inc l) z
      rw [Function.update_apply, tapeCount_inc]
      by_cases hz : z = (Redundant.carryLength l : ℤ) + 1
      · rw [ite_eq_left hz,
          ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (Redundant.carryLength l : ℤ)) by omega),
          ite_eq_left hz, raise_tapeCount_carry]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (Redundant.carryLength l : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.carryLength l : ℤ) + 1 + ((-1 : SignType) : ℤ) =
        (Redundant.carryLength l : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- One step of the return over a digit. -/
theorem incBackCfg_step (j : ℕ) (hj : j < Redundant.carryLength l) :
    bitTreeScanner.step (incBackCfg w k hk l (j + 1)) = incBackCfg w k hk l j ∧
      bitTreeScanner.outputSymbol (incBackCfg w k hk l (j + 1)) = none := by
  have hk' := Redundant.carryLength_le_length l
  have hsym : (incBackCfg w k hk l (j + 1)).workTapeSymbols =
      ![some (digitEmb ((Redundant.inc l).getD j 0)), some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount (Redundant.inc l) ((j + 1 : ℕ) : ℤ), tapeBase 0,
      tapeDigits w.length.bits 0] = _
    rw [Nat.cast_succ, tapeCount_of_lt (Redundant.inc l) j (by rw [Redundant.length_inc]; omega)]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (incBackCfg w k hk l (j + 1)) stIncBack stIncBack (none, -1)
    idle idle rfl (by rw [hsym]; exact tr_incBack_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j'
    match j' with
    | 0 =>
      change ((j + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (j : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step ending a carry: at the base marker, the pair bit is consumed and
the head steps to the lowest digit. -/
theorem incBackCfg_exit (h : k < w.length) (hb : w[k] = true) :
    bitTreeScanner.step (incBackCfg w k hk l 0) =
        cfgAt w (k + 1) h ⟨.term, c + 1, 0, []⟩ (Redundant.inc l) ∧
      bitTreeScanner.outputSymbol (incBackCfg w k hk l 0) = none := by
  have hsym : (incBackCfg w k hk l 0).workTapeSymbols = ![some 3, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_advance (incBackCfg w k hk l 0) stIncBack stMain (none, 1) idle
    idle rfl
    (by
      rw [hsym, inputSymbol_of_inputPos w _ k h rfl, hb]
      exact tr_incBack_base _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (incBackCfg w k hk l 0).inputPos SignType.pos =
      (cfgAt w (k + 1) h ⟨.term, c + 1, 0, []⟩ (Redundant.inc l)).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change k + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j
    match j with
    | 0 => rfl
    | 1 => exact (tapeLeaf_blank ⟨.term, c + 1, 0, []⟩ (Or.inl rfl)).symm
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = 1
      rw [SignType.coe_one]
      rfl
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- A pair bit's increment: in {name}`Geb.BitTreeScanner.incCost` steps, from the
closed form at a state expecting a tree to the closed form at the next bit,
one more tree pending. -/
theorem run_inc (h : k < w.length) (hb : w[k] = true) (hl : l.length ≤ bound w) :
    Run w (cfgAt w k hk ⟨.term, c, 0, []⟩ l)
      (cfgAt w (k + 1) h ⟨.term, c + 1, 0, []⟩ (Redundant.inc l)) (incCost l) := by
  rw [incCost]
  by_cases hc : Redundant.carryLength l = 0
  · rw [ite_eq_left hc]
    exact run_step _ _ (cfgAt_step_pair_low w k hk c l h hb hc) (headsLE_cfgAt_term w k hk c l)
      (headsLE_cfgAt_term w (k + 1) h (c + 1) _)
  · rw [ite_eq_right hc]
    have hc' : 0 < Redundant.carryLength l := Nat.pos_of_ne_zero hc
    have hcarry : Run w (incCarryCfg w k hk l 1) (incCarryCfg w k hk l (Redundant.carryLength l))
        (Redundant.carryLength l - 1) := by
      have := run_family (fun j ↦ incCarryCfg w k hk l (j + 1)) (Redundant.carryLength l - 1)
        (fun j hj ↦ incCarryCfg_step w k hk l (j + 1) (by omega))
        (fun j hj ↦ headsLE_incCarryCfg w k hk l hl (j + 1) (by omega))
      rw [show Redundant.carryLength l - 1 + 1 = Redundant.carryLength l by omega] at this
      exact this
    have hback : Run w (incBackCfg w k hk l (Redundant.carryLength l)) (incBackCfg w k hk l 0)
        (Redundant.carryLength l) :=
      run_family_down (incBackCfg w k hk l) (Redundant.carryLength l)
        (fun j hj ↦ incBackCfg_step w k hk l j hj)
        (fun j hj ↦ headsLE_incBackCfg w k hk l hl j hj)
    rw [show 2 * Redundant.carryLength l + 2 =
      1 + (Redundant.carryLength l - 1) + 1 + Redundant.carryLength l + 1 by omega]
    exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
      (run_step _ _ (cfgAt_step_pair_two w k hk c l h hb hc') (headsLE_cfgAt_term w k hk c l)
        (headsLE_incCarryCfg w k hk l hl 1 hc'))
      hcarry)
      (run_step _ _ (incCarryCfg_flip w k hk l) (headsLE_incCarryCfg w k hk l hl _ le_rfl)
        (headsLE_incBackCfg w k hk l hl _ le_rfl)))
      hback)
      (run_step _ _ (incBackCfg_exit w k hk c l h hb)
        (headsLE_incBackCfg w k hk l hl 0 (Nat.zero_le _))
        (headsLE_cfgAt_term w (k + 1) h (c + 1) _))

end Inc

section Dec

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- One step of the borrow over a zero. -/
theorem decBorrowCfg_step (j : ℕ) (hj : j < Redundant.borrowLength l) :
    bitTreeScanner.step (decBorrowCfg w k hk l j) = decBorrowCfg w k hk l (j + 1) ∧
      bitTreeScanner.outputSymbol (decBorrowCfg w k hk l j) = none := by
  have hb := Redundant.borrowLength_le_length l
  have hsym : (decBorrowCfg w k hk l j).workTapeSymbols = ![some 0, some 3, some 3] := by
    rw [workTapeSymbols_decBorrowCfg, tapeCount_of_lt _ _ (by omega),
      Redundant.getD_of_lt_borrowLength l j hj]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBorrowCfg w k hk l j) _ stDecBorrow
    (some (some 1), 1) idle idle rfl (by rw [hsym]; exact tr_decBorrowCfg_zero j _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext
    (by
      change some stDecBorrow = some (if j + 1 = 0 then stClear else stDecBorrow)
      rw [ite_eq_right (Nat.succ_ne_zero j)])
    (moveInputPos_zero _) ?_ ?_
  · funext j' z
    match j' with
    | 0 =>
      change Function.update (fun z ↦ if 1 ≤ z ∧ z ≤ (j : ℤ) then some 1 else tapeCount l z)
        ((j : ℤ) + 1) (some 1) z =
        if 1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ) then some 1 else tapeCount l z
      rw [Function.update_apply]
      by_cases hz : z = (j : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_left (show 1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ) by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (j : ℤ)
        · rw [ite_eq_left h1, ite_eq_left (show 1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ) by omega)]
        · rw [ite_eq_right h1, ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ)) by omega)]
    | 1 => rfl
    | 2 => rfl
  · funext j'
    match j' with
    | 0 =>
      change (j : ℤ) + 1 + ((1 : SignType) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step absorbing the borrow at a two at the lowest digit: the digit
becomes a one and the next tree is expected at once. -/
theorem decBorrowCfg_flip_two_zero (hn : Redundant.nlz l = true) (h : l ≠ [])
    (hd : l.getD (Redundant.borrowLength l) 0 = 2) (h0 : Redundant.borrowLength l = 0) :
    bitTreeScanner.step (decBorrowCfg w k hk l (Redundant.borrowLength l)) =
        { state := some stMain, inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩,
          workTapes := ![tapeCount (Redundant.dec l), tapeBase, tapeDigits w.length.bits],
          workTapePos := ![1, 0, 0] } ∧
      bitTreeScanner.outputSymbol (decBorrowCfg w k hk l (Redundant.borrowLength l)) = none := by
  have hlt := borrowLength_lt_length_of_nlz l hn h
  have hsym : (decBorrowCfg w k hk l (Redundant.borrowLength l)).workTapeSymbols =
      ![some 2, some 3, some 3] := by
    rw [workTapeSymbols_decBorrowCfg, tapeCount_of_lt _ _ hlt, hd]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBorrowCfg w k hk l (Redundant.borrowLength l)) stClear
    stMain (some (some 1), 0) idle idle
    (by
      change some (if Redundant.borrowLength l = 0 then stClear else stDecBorrow) = _
      rw [ite_eq_left h0])
    (by rw [hsym]; exact tr_clear_base_two _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ) then some 1 else tapeCount l z)
        ((Redundant.borrowLength l : ℤ) + 1) (some 1) z = tapeCount (Redundant.dec l) z
      rw [Function.update_apply, tapeCount_dec l hn h, ite_eq_left hd]
      by_cases hz : z = (Redundant.borrowLength l : ℤ) + 1
      · rw [ite_eq_left hz,
          ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ)) by omega),
          ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 1 + ((0 : SignType) : ℤ) = 1
      rw [SignType.coe_zero, h0]
      rfl
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step absorbing the borrow at a two above the lowest digit: the digit
becomes a one and the return begins. -/
theorem decBorrowCfg_flip_two_pos (hn : Redundant.nlz l = true) (h : l ≠ [])
    (hd : l.getD (Redundant.borrowLength l) 0 = 2) (h0 : Redundant.borrowLength l ≠ 0) :
    bitTreeScanner.step (decBorrowCfg w k hk l (Redundant.borrowLength l)) =
        decBackCfg w k hk l (Redundant.borrowLength l) ∧
      bitTreeScanner.outputSymbol (decBorrowCfg w k hk l (Redundant.borrowLength l)) = none := by
  have hlt := borrowLength_lt_length_of_nlz l hn h
  have hsym : (decBorrowCfg w k hk l (Redundant.borrowLength l)).workTapeSymbols =
      ![some 2, some 3, some 3] := by
    rw [workTapeSymbols_decBorrowCfg, tapeCount_of_lt _ _ hlt, hd]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBorrowCfg w k hk l (Redundant.borrowLength l)) stDecBorrow
    stDecBack (some (some 1), -1) idle idle
    (by
      change some (if Redundant.borrowLength l = 0 then stClear else stDecBorrow) = _
      rw [ite_eq_right h0])
    (by rw [hsym]; exact tr_decBorrow_two _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ) then some 1 else tapeCount l z)
        ((Redundant.borrowLength l : ℤ) + 1) (some 1) z = tapeCount (Redundant.dec l) z
      rw [Function.update_apply, tapeCount_dec l hn h, ite_eq_left hd]
      by_cases hz : z = (Redundant.borrowLength l : ℤ) + 1
      · rw [ite_eq_left hz,
          ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ)) by omega),
          ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 1 + ((-1 : SignType) : ℤ) =
        (Redundant.borrowLength l : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step absorbing the borrow at a one: the digit becomes a zero and the
head moves above it for the top test. -/
theorem decBorrowCfg_flip_one (hn : Redundant.nlz l = true) (h : l ≠ [])
    (hd : l.getD (Redundant.borrowLength l) 0 = 1) :
    bitTreeScanner.step (decBorrowCfg w k hk l (Redundant.borrowLength l)) = decTopCfg w k hk l ∧
      bitTreeScanner.outputSymbol (decBorrowCfg w k hk l (Redundant.borrowLength l)) = none := by
  have hlt := borrowLength_lt_length_of_nlz l hn h
  have hsym : (decBorrowCfg w k hk l (Redundant.borrowLength l)).workTapeSymbols =
      ![some 1, some 3, some 3] := by
    rw [workTapeSymbols_decBorrowCfg, tapeCount_of_lt _ _ hlt, hd]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBorrowCfg w k hk l (Redundant.borrowLength l)) _ stDecTop
    (some (some 0), 1) idle idle rfl (by rw [hsym]; exact tr_decBorrowCfg_one _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ) then some 1 else tapeCount l z)
        ((Redundant.borrowLength l : ℤ) + 1) (some 0) z = decTape l z
      rw [Function.update_apply, decTape]
      by_cases hz : z = (Redundant.borrowLength l : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (Redundant.borrowLength l : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 1 + ((1 : SignType) : ℤ) =
        (Redundant.borrowLength l : ℤ) + 2
      rw [SignType.coe_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The top test finding a digit: the lowered digit was not the top, the
count is decremented, and the return begins. -/
theorem decTopCfg_step_digit (hn : Redundant.nlz l = true) (h : l ≠ [])
    (hd : l.getD (Redundant.borrowLength l) 0 = 1)
    (htop : Redundant.borrowLength l + 1 < l.length) :
    bitTreeScanner.step (decTopCfg w k hk l) = decBackCfg w k hk l (Redundant.borrowLength l + 1) ∧
      bitTreeScanner.outputSymbol (decTopCfg w k hk l) = none := by
  have hsym : (decTopCfg w k hk l).workTapeSymbols =
      ![some (digitEmb (l.getD (Redundant.borrowLength l + 1) 0)), some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![decTape l ((Redundant.borrowLength l : ℤ) + 2), tapeBase 0,
      tapeDigits w.length.bits 0] = _
    rw [decTape, ite_eq_right (by omega), ite_eq_right (by omega),
      show (Redundant.borrowLength l : ℤ) + 2 = ((Redundant.borrowLength l + 1 : ℕ) : ℤ) + 1 by
        rw [Nat.cast_succ]; omega,
      tapeCount_of_lt _ _ htop]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decTopCfg w k hk l) stDecTop stDecBack (none, -1) idle idle
    rfl (by rw [hsym]; exact tr_decTop_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change decTape l z = tapeCount (Redundant.dec l) z
      rw [decTape, tapeCount_dec l hn h,
        ite_eq_right (show ¬l.getD (Redundant.borrowLength l) 0 = 2 by rw [hd]; decide),
        ite_eq_right (show ¬Redundant.borrowLength l + 1 = l.length by omega)]
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 2 + ((-1 : SignType) : ℤ) =
        ((Redundant.borrowLength l + 1 : ℕ) : ℤ)
      rw [SignType.coe_neg_one, Nat.cast_succ]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The top test finding blank: the lowered digit was the top, and the head
moves back to erase it. -/
theorem decTopCfg_step_blank (htop : Redundant.borrowLength l + 1 = l.length) :
    bitTreeScanner.step (decTopCfg w k hk l) = decEraseCfg w k hk l ∧
      bitTreeScanner.outputSymbol (decTopCfg w k hk l) = none := by
  have hsym : (decTopCfg w k hk l).workTapeSymbols = ![none, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![decTape l ((Redundant.borrowLength l : ℤ) + 2), tapeBase 0,
      tapeDigits w.length.bits 0] = _
    rw [decTape, ite_eq_right (by omega), ite_eq_right (by omega), tapeCount_of_ge _ _ (by omega)]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decTopCfg w k hk l) stDecTop stDecErase (none, -1) idle idle
    rfl (by rw [hsym]; exact tr_decTop_blank _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 2 + ((-1 : SignType) : ℤ) =
        (Redundant.borrowLength l : ℤ) + 1
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The erasing step: the lowered top digit is blanked, the count is
decremented, and the return begins. -/
theorem decEraseCfg_step (hn : Redundant.nlz l = true) (h : l ≠ [])
    (hd : l.getD (Redundant.borrowLength l) 0 = 1)
    (htop : Redundant.borrowLength l + 1 = l.length) :
    bitTreeScanner.step (decEraseCfg w k hk l) = decBackCfg w k hk l (Redundant.borrowLength l) ∧
      bitTreeScanner.outputSymbol (decEraseCfg w k hk l) = none := by
  obtain ⟨hstep, hout⟩ := step_stay (decEraseCfg w k hk l) stDecErase stDecBack (some none, -1)
    idle idle rfl (tr_decErase _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change Function.update (decTape l) ((Redundant.borrowLength l : ℤ) + 1) none z =
        tapeCount (Redundant.dec l) z
      rw [Function.update_apply, decTape, tapeCount_dec l hn h,
        ite_eq_right (show ¬l.getD (Redundant.borrowLength l) 0 = 2 by rw [hd]; decide),
        ite_eq_left htop]
      split_ifs <;> first | rfl | omega
    | 1 => rfl
    | 2 => rfl
  · funext j
    match j with
    | 0 =>
      change (Redundant.borrowLength l : ℤ) + 1 + ((-1 : SignType) : ℤ) =
        (Redundant.borrowLength l : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- One step of the return over a digit. -/
theorem decBackCfg_step (j : ℕ) (hj : j < (Redundant.dec l).length) :
    bitTreeScanner.step (decBackCfg w k hk l (j + 1)) = decBackCfg w k hk l j ∧
      bitTreeScanner.outputSymbol (decBackCfg w k hk l (j + 1)) = none := by
  have hsym : (decBackCfg w k hk l (j + 1)).workTapeSymbols =
      ![some (digitEmb ((Redundant.dec l).getD j 0)), some 3, some 3] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount (Redundant.dec l) ((j + 1 : ℕ) : ℤ), tapeBase 0,
      tapeDigits w.length.bits 0] = _
    rw [Nat.cast_succ, tapeCount_of_lt (Redundant.dec l) j hj]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBackCfg w k hk l (j + 1)) stDecBack stDecBack (none, -1)
    idle idle rfl (by rw [hsym]; exact tr_decBack_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j'
    match j' with
    | 0 =>
      change ((j + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (j : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The step ending a borrow: at the base marker, the head steps to the
lowest digit and the next tree is expected. -/
theorem decBackCfg_exit :
    bitTreeScanner.step (decBackCfg w k hk l 0) =
        { state := some stMain, inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩,
          workTapes := ![tapeCount (Redundant.dec l), tapeBase, tapeDigits w.length.bits],
          workTapePos := ![1, 0, 0] } ∧
      bitTreeScanner.outputSymbol (decBackCfg w k hk l 0) = none := by
  have hsym : (decBackCfg w k hk l 0).workTapeSymbols = ![some 3, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (decBackCfg w k hk l 0) stDecBack stMain (none, 1) idle idle
    rfl (by rw [hsym]; exact tr_decBack_base _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j
    match j with
    | 0 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = 1
      rw [SignType.coe_one]
      rfl
    | 1 => exact add_zero _
    | 2 => exact add_zero _

/-- The return from any cell within the decremented digits to the base
marker and the step there. -/
theorem run_decBack (hl : l.length ≤ bound w) (j : ℕ) (hj : j ≤ Redundant.borrowLength l + 1)
    (hj' : j ≤ (Redundant.dec l).length) :
    Run w (decBackCfg w k hk l j)
      { state := some stMain, inputPos := ⟨k + 1, by simp only [List.length_map]; omega⟩,
        workTapes := ![tapeCount (Redundant.dec l), tapeBase, tapeDigits w.length.bits],
        workTapePos := ![1, 0, 0] } (j + 1) :=
  run_seq _ _ _ _ _
    (run_family_down (decBackCfg w k hk l) j (fun i hi ↦ decBackCfg_step w k hk l i (by omega))
      (fun i hi ↦ headsLE_decBackCfg w k hk l hl i (by omega)))
    (run_step _ _ (decBackCfg_exit w k hk l) (headsLE_decBackCfg w k hk l hl 0 (Nat.zero_le _))
      (headsLE_mk w _ _ _ 1 0 0 (by rw [headBound]; omega) (by rw [headBound]; omega)
        (by rw [headBound]; omega)))

/-- A decrement of a counter whose lowest digit is not a two: from the
configuration the leaf's erasure ends in, out through the zeros, the
absorbing step and the return, to the configuration expecting the next tree
at the decremented count. -/
theorem run_dec_borrow (hn : Redundant.nlz l = true) (h : l ≠ []) (hl : l.length ≤ bound w)
    (hd0 : l.getD 0 0 ≠ 2) :
    Run w (decBorrowCfg w k hk l 0) (mainCfg w k hk (Redundant.dec l))
      (if l.getD (Redundant.borrowLength l) 0 = 2 then 2 * Redundant.borrowLength l + 2
        else 2 * Redundant.borrowLength l + 4) := by
  have hlt := borrowLength_lt_length_of_nlz l hn h
  have hne := getD_borrowLength_ne_zero l hn h
  have hlen := Redundant.length_dec l
  have hborrow : Run w (decBorrowCfg w k hk l 0) (decBorrowCfg w k hk l (Redundant.borrowLength l))
      (Redundant.borrowLength l) :=
    run_family (decBorrowCfg w k hk l) (Redundant.borrowLength l)
      (fun j hj ↦ decBorrowCfg_step w k hk l j hj)
      (fun j hj ↦ headsLE_decBorrowCfg w k hk l hl j hj)
  by_cases hd : l.getD (Redundant.borrowLength l) 0 = 2
  · rw [ite_eq_left hd]
    have h0 : Redundant.borrowLength l ≠ 0 := fun h0 ↦ hd0 (by rw [← h0]; exact hd)
    have hflip := decBorrowCfg_flip_two_pos w k hk l hn h hd h0
    rw [show 2 * Redundant.borrowLength l + 2 =
      Redundant.borrowLength l + 1 + (Redundant.borrowLength l + 1) by omega]
    exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ hborrow
      (run_step _ _ hflip (headsLE_decBorrowCfg w k hk l hl _ le_rfl)
        (headsLE_decBackCfg w k hk l hl _ (by omega))))
      (run_decBack w k hk l hl _ (by omega)
        (by
          rw [length_dec_of_ne_top l (fun h' ↦ by rw [hd] at h'; exact absurd h'.1 (by decide))]
          exact hlt.le))
  · rw [ite_eq_right hd]
    have hd1 : l.getD (Redundant.borrowLength l) 0 = 1 := by
      match h' : l.getD (Redundant.borrowLength l) 0 with
      | 0 => exact absurd h' hne
      | 1 => rfl
      | 2 => exact absurd h' hd
    have hflip := decBorrowCfg_flip_one w k hk l hn h hd1
    by_cases htop : Redundant.borrowLength l + 1 = l.length
    · rw [show 2 * Redundant.borrowLength l + 4 =
        Redundant.borrowLength l + 1 + 1 + 1 + (Redundant.borrowLength l + 1) by omega]
      exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ hborrow
        (run_step _ _ hflip (headsLE_decBorrowCfg w k hk l hl _ le_rfl)
          (headsLE_decTopCfg w k hk l hn h hl)))
        (run_step _ _ (decTopCfg_step_blank w k hk l htop) (headsLE_decTopCfg w k hk l hn h hl)
          (headsLE_decEraseCfg w k hk l hl)))
        (run_step _ _ (decEraseCfg_step w k hk l hn h hd1 htop) (headsLE_decEraseCfg w k hk l hl)
          (headsLE_decBackCfg w k hk l hl _ (by omega))))
        (run_decBack w k hk l hl _ (by omega) (by rw [hlen, ite_eq_left ⟨hd1, htop⟩]; omega))
    · have htop' : Redundant.borrowLength l + 1 < l.length := by omega
      rw [show 2 * Redundant.borrowLength l + 4 =
        Redundant.borrowLength l + 1 + 1 + (Redundant.borrowLength l + 1 + 1) by omega]
      exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ hborrow
        (run_step _ _ hflip (headsLE_decBorrowCfg w k hk l hl _ le_rfl)
          (headsLE_decTopCfg w k hk l hn h hl)))
        (run_step _ _ (decTopCfg_step_digit w k hk l hn h hd1 htop')
          (headsLE_decTopCfg w k hk l hn h hl) (headsLE_decBackCfg w k hk l hl _ le_rfl)))
        (run_decBack w k hk l hl _ le_rfl
          (by rw [length_dec_of_ne_top l (fun h' ↦ htop h'.2)]; exact htop'.le))

/-- A decrement of a counter that is not empty: from the configuration the
leaf's erasure ends in, in {name}`Geb.BitTreeScanner.decCost` steps, to the
configuration expecting the next tree at the decremented count. -/
theorem run_dec_of_ne_nil (hn : Redundant.nlz l = true) (h : l ≠ []) (hl : l.length ≤ bound w) :
    Run w (decBorrowCfg w k hk l 0) (mainCfg w k hk (Redundant.dec l)) (decCost l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons d r =>
    match d with
    | 0 => exact run_dec_borrow w k hk (0 :: r) hn h hl (by rw [List.getD_cons_zero]; decide)
    | 1 => exact run_dec_borrow w k hk (1 :: r) hn h hl (by rw [List.getD_cons_zero]; decide)
    | 2 =>
      rw [show decCost (2 :: r) = 1 from rfl]
      exact run_step _ _ (decBorrowCfg_flip_two_zero w k hk (2 :: r) hn h rfl rfl)
        (headsLE_decBorrowCfg w k hk (2 :: r) hl 0 (Nat.zero_le _)) (headsLE_mainCfg w k hk _)

/-- The step closing the last pending tree: at an empty count, the scan
completes. -/
theorem decBorrowCfg_nil_step :
    bitTreeScanner.step (decBorrowCfg w k hk [] 0) = cfgAt w k hk (close 0) (Redundant.dec []) ∧
      bitTreeScanner.outputSymbol (decBorrowCfg w k hk [] 0) = none := by
  have hsym : (decBorrowCfg w k hk [] 0).workTapeSymbols = ![none, some 3, some 3] := by
    rw [workTapeSymbols_decBorrowCfg, tapeCount_of_ge [] _ (by rw [List.length_nil]; omega)]
  obtain ⟨hstep, hout⟩ := step_stay (decBorrowCfg w k hk [] 0) stClear stDone idle idle idle rfl
    (by rw [hsym]; exact tr_clear_base_blank _ _)
  refine ⟨?_, hout⟩
  rw [hstep, close_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 =>
      change (if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeCount [] z) =
        tapeCount (Redundant.dec []) z
      rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega)]
      rfl
    | 1 => exact congrFun (tapeLeaf_blank ⟨.done, 0, 0, []⟩ (Or.inr rfl)).symm z
    | 2 => rfl
  · exact vec3_ext (add_zero _) (add_zero _) (add_zero _)

/-- The closed form at the state a completed tree leaves, from the
configuration the leaf's erasure ends in: at an empty count the scan
completes in one step; otherwise the count is decremented and the next tree
expected. -/
theorem run_close (hn : Redundant.nlz l = true) (c : ℕ) (hl : l.length ≤ bound w)
    (hv : Redundant.value l = c) :
    Run w (decBorrowCfg w k hk l 0) (cfgAt w k hk (close c) (Redundant.dec l)) (decCost l) := by
  cases l with
  | nil =>
    rw [Redundant.value_nil] at hv
    subst hv
    exact run_step _ _ (decBorrowCfg_nil_step w k hk)
      (headsLE_decBorrowCfg w k hk [] hl 0 (Nat.zero_le _))
      (headsLE_mk w _ _ _ 1 0 0 (by rw [headBound]; omega) (by rw [headBound]; omega)
        (by rw [headBound]; omega))
  | cons d r =>
    have hne : d :: r ≠ [] := List.cons_ne_nil _ _
    have hpos : c ≠ 0 := by
      rw [← hv]
      exact fun h0 ↦ hne ((Redundant.value_eq_zero_iff _ hn).mp h0)
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [close_succ, ← mainCfg_eq_cfgAt w k hk c']
    exact run_dec_of_ne_nil w k hk (d :: r) hn hne hl

end Dec

end Geb.BitTreeScanner
