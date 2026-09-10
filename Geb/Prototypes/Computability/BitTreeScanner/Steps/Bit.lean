/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Leaf

set_option doc.verso true

/-!
# The two-pass tree scanner's steps at each bit

From the closed form {name}`Geb.BitTreeScanner.cfgAt` at a scan state and a
counter satisfying the invariants, the machine reads the next bit and does
the work the bit carries, running {name}`Geb.BitTreeScanner.cost` steps to the
closed form at the scan's next state and the counter's next value: one step
for a bit that changes no count, the pending count's increment at a pair bit,
and the leaf count's chains at a length digit or a payload bit.

## Main statements

* {lit}`Geb.BitTreeScanner.advance_cfgAt` — a step reading a bit from the
  closed form lands on the closed form at a state, given the resolved
  transition and the field equalities.
* {lit}`Geb.BitTreeScanner.run_cfgAt_step` — a bit at any state satisfying
  the invariants: the closed form at the scan's next state, after the bit's
  cost.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`, as
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic`'s
implementation notes explain.

## Tags

Turing machine, tree, prefix code, Elias gamma code, binary counter
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Advance

variable (w : List Bool) (k : ℕ)

/-- A step reading a bit from the closed form lands on the closed form at a
state, given the resolved transition and the field equalities. -/
theorem advance_cfgAt (h : k + 1 ≤ w.length) (s s' : Scan) (l l' : List Redundant.Digit)
    (q' : Fin stateCount) (a₀ a₁ a₂ : Act)
    (htr : bitTreeScanner.tr (stateOf s.mode) (some (boolEmb w[k]))
      ![tapeCount l 1, tapeLeaf s (headLeaf s), tapeDigits w.length.bits (headRuler s)] =
      advance q' a₀ a₁ a₂)
    (hq : stateOf s'.mode = q')
    (h0 : applyAct a₀ (tapeCount l) 1 = tapeCount l')
    (h1 : applyAct a₁ (tapeLeaf s) (headLeaf s) = tapeLeaf s')
    (h2 : applyAct a₂ (tapeDigits w.length.bits) (headRuler s) = tapeDigits w.length.bits)
    (hc : (1 : ℤ) + (a₀.2 : ℤ) = 1) (hh : headLeaf s + (a₁.2 : ℤ) = headLeaf s')
    (hr : headRuler s + (a₂.2 : ℤ) = headRuler s') :
    bitTreeScanner.step (cfgAt w k (by omega) s l) = cfgAt w (k + 1) h s' l' ∧
      bitTreeScanner.outputSymbol (cfgAt w k (by omega) s l) = none := by
  obtain ⟨hstep, hout⟩ := step_advance (cfgAt w k (by omega) s l) (stateOf s.mode) q' a₀ a₁ a₂
    rfl
    (by
      rw [workTapeSymbols_eq,
        inputSymbol_of_inputPos w _ k (by omega) (cfgAt_inputPos_val _ _ _ _ _)]
      exact htr)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext ?_ ?_ ?_ ?_
  · change some q' = some (stateOf s'.mode)
    rw [hq]
  · change moveInputPos (cfgAt w k (by omega) s l).inputPos SignType.pos =
      (cfgAt w (k + 1) h s' l').inputPos
    rw [moveInputPos_pos_of_ne_right _
      (by rw [cfgAt_inputPos_val, List.length_map]; omega)]
    exact Fin.ext rfl
  · funext i
    match i with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · funext i
    match i with
    | 0 => exact hc
    | 1 => exact hh
    | 2 => exact hr

end Advance

section Modes

variable (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) (c : ℕ) (l : List Redundant.Digit)

/-- A bit in the expecting mode. -/
theorem run_cfgAt_term (hl : l.length ≤ bound w) :
    Run w (cfgAt w k (by omega) ⟨.term, c, 0, []⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.term, c, 0, []⟩ w[k])
        (treeStep (bound w) ⟨.term, c, 0, []⟩ w[k] l))
      (cost ⟨.term, c, 0, []⟩ w[k] l) := by
  rw [treeStep_term]
  cases hb : w[k] with
  | true =>
    rw [scanStep_term_true, Bool.cond_true]
    exact run_inc w k (by omega) c l h hb hl
  | false =>
    rw [scanStep_term_false, Bool.cond_false]
    refine run_step _ _ (advance_cfgAt w k h ⟨.term, c, 0, []⟩ ⟨.zeros, c, 0, []⟩ l l stZeros idle
      (none, 1) idle (by rw [hb]; exact tr_main_leaf _) rfl rfl ?_ rfl (add_zero _) ?_ (add_zero _))
      (headsLE_cfgAt w k _ ⟨.term, c, 0, []⟩ ⟨rfl, rfl⟩ l)
      (headsLE_cfgAt w (k + 1) h ⟨.zeros, c, 0, []⟩ ⟨rfl, Nat.zero_le _⟩ l)
    · change tapeLeaf ⟨.term, c, 0, []⟩ = tapeLeaf ⟨.zeros, c, 0, []⟩
      rw [tapeLeaf_blank _ (Or.inl rfl), tapeLeaf_zeros_zero]
    · change headLeaf ⟨.term, c, 0, []⟩ + ((1 : SignType) : ℤ) = headLeaf ⟨.zeros, c, 0, []⟩
      rw [SignType.coe_one, headLeaf_term, headLeaf_zeros]
      rfl

/-- A bit while reading a gamma code's zeros. -/
theorem run_cfgAt_zeros (wd : ℕ) (hw : wd ≤ bound w + 1) (hn : Redundant.nlz l = true)
    (hv : Redundant.value l = c) (hl : l.length ≤ bound w) :
    Run w (cfgAt w k (by omega) ⟨.zeros, c, wd, []⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.zeros, c, wd, []⟩ w[k])
        (treeStep (bound w) ⟨.zeros, c, wd, []⟩ w[k] l))
      (cost ⟨.zeros, c, wd, []⟩ w[k] l) := by
  have hgood : Good (bound w) ⟨.zeros, c, wd, []⟩ := ⟨rfl, hw⟩
  cases hb : w[k] with
  | false =>
    rw [treeStep_of_not_term (bound w) ⟨.zeros, c, wd, []⟩ false l (fun h ↦ nomatch h)]
    by_cases hW : bound w < wd
    · rw [scanStep_zeros_false_of_lt _ _ _ _ hW,
        ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
      refine run_step _ _ (advance_cfgAt w k h ⟨.zeros, c, wd, []⟩ ⟨.dead, c, wd, []⟩ l l stDead
        idle idle idle ?_ rfl rfl rfl rfl (add_zero _) (add_zero _) (add_zero _))
        (headsLE_cfgAt w k _ _ hgood l) (headsLE_cfgAt w (k + 1) h ⟨.dead, c, wd, []⟩ ⟨rfl, hw⟩ l)
      rw [hb, headRuler_zeros, tapeDigits_of_ge _ _ (by rw [bound] at hW; omega)]
      exact tr_zeros_zero_blank _ _
    · rw [scanStep_zeros_false _ _ _ _ (by omega),
        ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
      obtain ⟨x, hx⟩ := tapeDigits_eq_some w.length.bits wd (by omega) (by rw [bound] at hW; omega)
      refine run_step _ _ (advance_cfgAt w k h ⟨.zeros, c, wd, []⟩ ⟨.zeros, c, wd + 1, []⟩ l l
        stZeros idle (some (some 2), 1) (none, 1) ?_ rfl rfl ?_ rfl (add_zero _) ?_ ?_)
        (headsLE_cfgAt w k _ _ hgood l)
        (headsLE_cfgAt w (k + 1) h ⟨.zeros, c, wd + 1, []⟩ ⟨rfl, by dsimp only; omega⟩ l)
      · rw [hb, headRuler_zeros, hx]
        exact tr_zeros_zero_some _ _ _ (Option.some_ne_none x)
      · exact funext (tapeLeaf_zeros_succ c wd)
      · change headLeaf ⟨.zeros, c, wd, []⟩ + ((1 : SignType) : ℤ) =
          headLeaf ⟨.zeros, c, wd + 1, []⟩
        rw [SignType.coe_one, headLeaf_zeros, headLeaf_zeros]
        omega
      · change headRuler ⟨.zeros, c, wd, []⟩ + ((1 : SignType) : ℤ) =
          headRuler ⟨.zeros, c, wd + 1, []⟩
        rw [SignType.coe_one, headRuler_zeros, headRuler_zeros]
        omega
  | true =>
    rw [treeStep_zeros_true, scanStep_zeros_true,
      show cost ⟨.zeros, c, wd, []⟩ true l = 1 + pendingDigits (wd + 1) [true] l from rfl]
    refine run_seq _ _ _ _ _ (run_step _ _ (advance_cfgAt w k h ⟨.zeros, c, wd, []⟩
      ⟨.bits, c, wd + 1, [true]⟩ l l stBits idle (some (some 1), -1) idle
      (by rw [hb]; exact tr_zeros_one _) rfl rfl ?_ rfl (add_zero _) ?_ ?_)
      (headsLE_cfgAt w k _ _ hgood l)
      (headsLE_cfgAt_bits w (k + 1) h c (wd + 1) [true] (by rw [List.length_singleton]; omega)
        (by omega) l))
      (run_pendingDigits w (k + 1) h l c (wd + 1) [true] rfl (by rw [List.length_singleton]; omega)
        (by omega) hn hv hl)
    · funext z
      change Function.update (tapeLeaf ⟨.zeros, c, wd, []⟩) (headLeaf ⟨.zeros, c, wd, []⟩)
        (some 1) z = tapeLeaf ⟨.bits, c, wd + 1, [true]⟩ z
      rw [Function.update_apply, tapeLeaf, tapeLeaf, headLeaf_zeros]
      change (if z = (wd : ℤ) + 1 then some 1
        else if z = 0 then some 3 else if 1 ≤ z ∧ z ≤ (wd : ℤ) then some 2 else none) =
        if z = 0 then some 3
        else if 1 ≤ z ∧ z ≤ ((wd + 1 - [true].length : ℕ) : ℤ) then some 2
        else digitsAt ((wd + 1 - [true].length : ℕ) : ℤ) [true] z
      rw [List.length_singleton, Nat.add_sub_cancel, digitsAt, List.length_singleton]
      by_cases hz : z = (wd : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (show ¬z = 0 by omega),
          ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (wd : ℤ)) by omega),
          ite_eq_left (show (wd : ℤ) < z ∧ z ≤ (wd : ℤ) + ((1 : ℕ) : ℤ) by omega), hz,
          show ((wd : ℤ) + 1 - wd - 1).toNat = 0 by omega]
        rfl
      · rw [ite_eq_right hz]
        by_cases hz0 : z = 0
        · rw [ite_eq_left hz0, ite_eq_left hz0]
        · rw [ite_eq_right hz0, ite_eq_right hz0]
          by_cases h1 : 1 ≤ z ∧ z ≤ (wd : ℤ)
          · rw [ite_eq_left h1, ite_eq_left h1]
          · rw [ite_eq_right h1, ite_eq_right h1,
              ite_eq_right (show ¬((wd : ℤ) < z ∧ z ≤ (wd : ℤ) + ((1 : ℕ) : ℤ)) by omega)]
    · change headLeaf ⟨.zeros, c, wd, []⟩ + ((-1 : SignType) : ℤ) =
        headLeaf ⟨.bits, c, wd + 1, [true]⟩
      rw [SignType.coe_neg_one, headLeaf_zeros, headLeaf_bits, List.length_singleton,
        Nat.add_sub_cancel]
      omega
    · change headRuler ⟨.zeros, c, wd, []⟩ + ((0 : SignType) : ℤ) =
        headRuler ⟨.bits, c, wd + 1, [true]⟩
      rw [SignType.coe_zero, headRuler_zeros, headRuler_bits, List.length_singleton,
        Nat.add_sub_cancel]
      omega

/-- A bit while reading a gamma code's digits. -/
theorem run_cfgAt_bits (wd : ℕ) (d : List Bool) (hs : Good (bound w) ⟨.bits, c, wd, d⟩)
    (hn : Redundant.nlz l = true) (hv : Redundant.value l = c) (hl : l.length ≤ bound w) :
    Run w (cfgAt w k (by omega) ⟨.bits, c, wd, d⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.bits, c, wd, d⟩ w[k])
        (treeStep (bound w) ⟨.bits, c, wd, d⟩ w[k] l))
      (cost ⟨.bits, c, wd, d⟩ w[k] l) := by
  have hgood := hs
  dsimp only [Good] at hs
  obtain ⟨hlt, ⟨r, hr⟩, hw⟩ := hs
  have hf : allFalse (w[k] :: d) = false := by
    rw [hr, ← List.cons_append, ← Bool.not_eq_true, allFalse_iff]
    exact Nat.ne_of_gt (ofBits_append_true_pos _)
  rw [treeStep_bits, scanStep_bits,
    show cost ⟨.bits, c, wd, d⟩ w[k] l = 1 + pendingDigits wd (w[k] :: d) l by
      cases w[k] <;> rfl]
  have hmark : tapeLeaf ⟨.bits, c, wd, d⟩ (headLeaf ⟨.bits, c, wd, d⟩) = some 2 := by
    rw [tapeLeaf, headLeaf_bits]
    change (if ((wd - d.length : ℕ) : ℤ) = 0 then some 3
      else if 1 ≤ ((wd - d.length : ℕ) : ℤ) ∧ ((wd - d.length : ℕ) : ℤ) ≤ ((wd - d.length : ℕ) : ℤ)
        then some 2
      else digitsAt ((wd - d.length : ℕ) : ℤ) d ((wd - d.length : ℕ) : ℤ)) = some 2
    rw [ite_eq_right (show ¬((wd - d.length : ℕ) : ℤ) = 0 by omega),
      ite_eq_left ⟨by omega, le_rfl⟩]
  refine run_seq _ _ _ _ _ (run_step _ _ (advance_cfgAt w k h ⟨.bits, c, wd, d⟩
    ⟨.bits, c, wd, w[k] :: d⟩ l l stBits idle (some (some (boolEmb w[k])), -1) (none, -1)
    (by rw [hmark]; exact tr_bits_mark _ _ _) rfl rfl ?_ rfl (add_zero _) ?_ ?_)
    (headsLE_cfgAt w k _ _ hgood l)
    (headsLE_cfgAt_bits w (k + 1) h c wd (w[k] :: d) (by rw [List.length_cons]; exact hlt) hw l))
    (run_pendingDigits w (k + 1) h l c wd (w[k] :: d) hf (by rw [List.length_cons]; exact hlt) hw
      hn hv hl)
  · funext z
    change Function.update (tapeLeaf ⟨.bits, c, wd, d⟩) (headLeaf ⟨.bits, c, wd, d⟩)
      (some (boolEmb w[k])) z = tapeLeaf ⟨.bits, c, wd, w[k] :: d⟩ z
    rw [Function.update_apply, tapeLeaf, tapeLeaf, headLeaf_bits]
    change (if z = ((wd - d.length : ℕ) : ℤ) then some (boolEmb w[k])
      else if z = 0 then some 3
      else if 1 ≤ z ∧ z ≤ ((wd - d.length : ℕ) : ℤ) then some 2
      else digitsAt ((wd - d.length : ℕ) : ℤ) d z) =
      if z = 0 then some 3
      else if 1 ≤ z ∧ z ≤ ((wd - (w[k] :: d).length : ℕ) : ℤ) then some 2
      else digitsAt ((wd - (w[k] :: d).length : ℕ) : ℤ) (w[k] :: d) z
    rw [List.length_cons, digitsAt_cons,
      show ((wd - (d.length + 1) : ℕ) : ℤ) + 1 = ((wd - d.length : ℕ) : ℤ) by omega]
    by_cases hz : z = ((wd - d.length : ℕ) : ℤ)
    · rw [ite_eq_left hz, ite_eq_right (show ¬z = 0 by omega),
        ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((wd - (d.length + 1) : ℕ) : ℤ)) by omega), ite_eq_left hz]
    · rw [ite_eq_right hz]
      by_cases hz0 : z = 0
      · rw [ite_eq_left hz0, ite_eq_left hz0]
      · rw [ite_eq_right hz0, ite_eq_right hz0]
        by_cases h1 : 1 ≤ z ∧ z ≤ ((wd - d.length : ℕ) : ℤ)
        · rw [ite_eq_left h1,
            ite_eq_left (show 1 ≤ z ∧ z ≤ ((wd - (d.length + 1) : ℕ) : ℤ) by omega)]
        · rw [ite_eq_right h1,
            ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((wd - (d.length + 1) : ℕ) : ℤ)) by omega),
            ite_eq_right hz]
  · change headLeaf ⟨.bits, c, wd, d⟩ + ((-1 : SignType) : ℤ) = headLeaf ⟨.bits, c, wd, w[k] :: d⟩
    rw [SignType.coe_neg_one, headLeaf_bits, headLeaf_bits, List.length_cons]
    omega
  · change headRuler ⟨.bits, c, wd, d⟩ + ((-1 : SignType) : ℤ) =
      headRuler ⟨.bits, c, wd, w[k] :: d⟩
    rw [SignType.coe_neg_one, headRuler_bits, headRuler_bits, List.length_cons]
    omega

/-- The step consuming a payload bit: the decrement's return has reached the
base marker, and the machine steps to the lowest digit of the decremented
count. -/
theorem returnCfg_consume (d : List Bool) :
    bitTreeScanner.step (returnCfg w k (by omega) l false d 0) =
        borrowCfg w (k + 1) h l false (decList d) 0 ∧
      bitTreeScanner.outputSymbol (returnCfg w k (by omega) l false d 0) = none := by
  have hsym : (returnCfg w k (by omega) l false d 0).workTapeSymbols =
      ![tapeCount l 1, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_advance (returnCfg w k (by omega) l false d 0) stReturn stBorrow
    idle (none, 1) idle rfl (by
      rw [hsym, inputSymbol_of_inputPos w _ k (by omega) rfl]
      exact tr_return_base_bit _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (returnCfg w k (by omega) l false d 0).inputPos SignType.pos =
      (borrowCfg w (k + 1) h l false (decList d) 0).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change k + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change tapeDigits (decList d) z =
        if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits (decList d) z
      rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega)]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = ((0 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
    | 2 => exact add_zero _

/-- A payload bit in the countdown. -/
theorem run_cfgAt_count (wd : ℕ) (d : List Bool) (hs : Good (bound w) ⟨.count, c, wd, d⟩)
    (hn : Redundant.nlz l = true) (hv : Redundant.value l = c) (hl : l.length ≤ bound w) :
    Run w (cfgAt w k (by omega) ⟨.count, c, wd, d⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.count, c, wd, d⟩ w[k])
        (treeStep (bound w) ⟨.count, c, wd, d⟩ w[k] l))
      (cost ⟨.count, c, wd, d⟩ w[k] l) := by
  dsimp only [Good] at hs
  obtain ⟨hd, hlen, hw⟩ := hs
  rw [treeStep_count, scanStep_count,
    show cost ⟨.count, c, wd, d⟩ w[k] l =
      2 * borrowLength d + 1 + 1 + pendingCount wd (decList d) l by cases w[k] <;> rfl,
    cfgAt_count]
  have h₄ := run_pendingCount w (k + 1) h l c wd (decList d) (by rw [length_decList, hlen]) hw hn
    hv hl
  rw [cfgAt_count] at h₄
  exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _
    (run_decrement w k (by omega) l false d hd (by omega))
    (run_step _ _ (returnCfg_consume w k h l d) (headsLE_returnCfg w k _ l false d (by omega) 0
      (Nat.zero_le _))
      (headsLE_borrowCfg w (k + 1) h l false (decList d) (by rw [length_decList]; omega) 0
        (Nat.zero_le _)))) h₄

/-- A bit after completion. -/
theorem run_cfgAt_done :
    Run w (cfgAt w k (by omega) ⟨.done, c, 0, []⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.done, c, 0, []⟩ w[k])
        (treeStep (bound w) ⟨.done, c, 0, []⟩ w[k] l))
      (cost ⟨.done, c, 0, []⟩ w[k] l) := by
  rw [treeStep_of_not_term (bound w) ⟨.done, c, 0, []⟩ w[k] l (fun h ↦ nomatch h), scanStep_done,
    ite_eq_right (by rintro (h | h) <;> exact nomatch h),
    show cost ⟨.done, c, 0, []⟩ w[k] l = 1 by cases w[k] <;> rfl]
  refine run_step _ _ (advance_cfgAt w k h ⟨.done, c, 0, []⟩ ⟨.dead, c, 0, []⟩ l l stDead idle
    (none, 1) idle (tr_done_bit _ _) rfl rfl ?_ rfl (add_zero _) ?_ (add_zero _))
    (headsLE_cfgAt w k _ ⟨.done, c, 0, []⟩ ⟨rfl, rfl⟩ l)
    (headsLE_cfgAt w (k + 1) h ⟨.dead, c, 0, []⟩ ⟨rfl, Nat.zero_le _⟩ l)
  · change tapeLeaf ⟨.done, c, 0, []⟩ = tapeLeaf ⟨.dead, c, 0, []⟩
    rw [tapeLeaf_blank _ (Or.inr rfl), tapeLeaf_dead, tapeLeaf_zeros_zero]
  · change headLeaf ⟨.done, c, 0, []⟩ + ((1 : SignType) : ℤ) = headLeaf ⟨.dead, c, 0, []⟩
    rw [SignType.coe_one, headLeaf_done, headLeaf_dead]
    rfl

/-- A bit after failure. -/
theorem run_cfgAt_dead (wd : ℕ) (hw : wd ≤ bound w + 1) :
    Run w (cfgAt w k (by omega) ⟨.dead, c, wd, []⟩ l)
      (cfgAt w (k + 1) h (scanStep (bound w) ⟨.dead, c, wd, []⟩ w[k])
        (treeStep (bound w) ⟨.dead, c, wd, []⟩ w[k] l))
      (cost ⟨.dead, c, wd, []⟩ w[k] l) := by
  rw [treeStep_of_not_term (bound w) ⟨.dead, c, wd, []⟩ w[k] l (fun h ↦ nomatch h), scanStep_dead,
    ite_eq_right (by rintro (h | h) <;> exact nomatch h),
    show cost ⟨.dead, c, wd, []⟩ w[k] l = 1 by cases w[k] <;> rfl]
  exact run_step _ _ (advance_cfgAt w k h ⟨.dead, c, wd, []⟩ ⟨.dead, c, wd, []⟩ l l stDead idle
    idle idle (tr_dead_bit _ _) rfl rfl rfl rfl (add_zero _) (add_zero _) (add_zero _))
    (headsLE_cfgAt w k _ ⟨.dead, c, wd, []⟩ ⟨rfl, hw⟩ l)
    (headsLE_cfgAt w (k + 1) h ⟨.dead, c, wd, []⟩ ⟨rfl, hw⟩ l)

/-- A bit at any state satisfying the invariants: the closed form at the
scan's next state and the counter's next value, after the bit's cost. -/
theorem run_cfgAt_step (s : Scan) (hs : Good (bound w) s) (ht : GoodTree s l)
    (hl : l.length ≤ bound w) :
    Run w (cfgAt w k (by omega) s l)
      (cfgAt w (k + 1) h (scanStep (bound w) s w[k]) (treeStep (bound w) s w[k] l))
      (cost s w[k] l) := by
  obtain ⟨m, c, wd, d⟩ := s
  obtain ⟨hn, hv⟩ := ht
  cases m with
  | term =>
    obtain ⟨rfl, rfl⟩ := hs
    exact run_cfgAt_term w k h c l hl
  | zeros =>
    obtain ⟨rfl, hw⟩ := hs
    exact run_cfgAt_zeros w k h c l wd hw hn hv hl
  | bits => exact run_cfgAt_bits w k h c l wd d hs hn hv hl
  | count => exact run_cfgAt_count w k h c l wd d hs hn hv hl
  | done =>
    obtain ⟨rfl, rfl⟩ := hs
    exact run_cfgAt_done w k h c l
  | dead =>
    obtain ⟨rfl, hw⟩ := hs
    exact run_cfgAt_dead w k h c l wd hw

end Modes

end Geb.BitTreeScanner
