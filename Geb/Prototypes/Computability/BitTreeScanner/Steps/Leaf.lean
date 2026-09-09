/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Count

set_option doc.verso true

/-!
# The leaf count's chains

The runs through a leaf's count on the second tape: a decrement borrows
outward through the zeros below the lowest one, flips it, and returns to the
base marker; a decrement that runs off the digits' end into blank finds the
count at zero, erases the digits on its way back, and at the base marker
begins the pending count's decrement that closes the leaf. Composed into the
work a bit carries before the next: {name}`Geb.BitTreeScanner.pendingCount` after a
payload bit, {name}`Geb.BitTreeScanner.pendingDigits` after a length digit.

## Main statements

* {lit}`Geb.BitTreeScanner.run_decrement` — a decrement's borrow and return.
* {lit}`Geb.BitTreeScanner.run_fail` — a decrement finding the count at zero,
  the erasure, and the pending count's decrement closing the leaf.
* {lit}`Geb.BitTreeScanner.run_pendingCount`,
  {lit}`Geb.BitTreeScanner.run_pendingDigits` — the work after a payload bit
  and after a length digit, to the closed form at the state the bit settles
  in.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`, as
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic`'s
implementation notes explain.

## Tags

Turing machine, binary counter, borrow, Elias gamma code
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Borrow

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- One step of the borrow over a zero. -/
theorem borrowCfg_step (first : Bool) (d : List Bool) (i : ℕ) (hi : i < borrowLength d) :
    bitTreeScanner.step (borrowCfg w k hk l first d i) = borrowCfg w k hk l first d (i + 1) ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk l first d i) = none := by
  have htz := borrowLength_le_length d
  have hsym : (borrowCfg w k hk l first d i).workTapeSymbols =
      ![tapeCount l 1, some 0, some 3] := by
    rw [workTapeSymbols_borrowCfg, tapeDigits_of_lt _ _ (by omega), getD_of_lt_borrowLength d i hi]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk l first d i) (borrowState first)
    (borrowState first) idle (some (some 1), 1) idle rfl
    (by rw [hsym]; exact tr_borrowState_zero _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update (fun z ↦ if 1 ≤ z ∧ z ≤ (i : ℤ) then some 1 else tapeDigits d z)
        ((i : ℤ) + 1) (some 1) z =
        if 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) then some 1 else tapeDigits d z
      rw [Function.update_apply]
      by_cases hz : z = (i : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_left (show 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (i : ℤ)
        · rw [ite_eq_left h1, ite_eq_left (show 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) by omega)]
        · rw [ite_eq_right h1, ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ)) by omega)]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change (i : ℤ) + 1 + ((1 : SignType) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega
    | 2 => exact add_zero _

/-- The step absorbing the borrow: at the lowest one, the digit becomes a zero
and the return begins. -/
theorem borrowCfg_flip (first : Bool) (d : List Bool) (hd : allFalse d = false) :
    bitTreeScanner.step (borrowCfg w k hk l first d (borrowLength d)) =
        returnCfg w k hk l first d (borrowLength d) ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk l first d (borrowLength d)) = none := by
  have htz := borrowLength_lt_length d hd
  have hsym : (borrowCfg w k hk l first d (borrowLength d)).workTapeSymbols =
      ![tapeCount l 1, some 1, some 3] := by
    rw [workTapeSymbols_borrowCfg, tapeDigits_of_lt _ _ htz, getD_borrowLength d hd]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk l first d (borrowLength d))
    (borrowState first) (returnState first) idle (some (some 0), -1) idle rfl
    (by rw [hsym]; exact tr_borrowState_one _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (borrowLength d : ℤ) then some 1 else tapeDigits d z)
        ((borrowLength d : ℤ) + 1) (some 0) z = tapeDigits (decList d) z
      rw [Function.update_apply, tapeDigits_decList d hd]
      by_cases hz : z = (borrowLength d : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (borrowLength d : ℤ)) by omega),
          ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (borrowLength d : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change (borrowLength d : ℤ) + 1 + ((-1 : SignType) : ℤ) = (borrowLength d : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 2 => exact add_zero _

/-- One step of the return over a digit. -/
theorem returnCfg_step (first : Bool) (d : List Bool) (i : ℕ) (hi : i < d.length) :
    bitTreeScanner.step (returnCfg w k hk l first d (i + 1)) = returnCfg w k hk l first d i ∧
      bitTreeScanner.outputSymbol (returnCfg w k hk l first d (i + 1)) = none := by
  have hsym : (returnCfg w k hk l first d (i + 1)).workTapeSymbols =
      ![tapeCount l 1, some (boolEmb ((decList d).getD i false)), some 3] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount l 1, tapeDigits (decList d) ((i + 1 : ℕ) : ℤ), tapeDigits w.length.bits 0] =
      _
    rw [Nat.cast_succ, tapeDigits_of_lt (decList d) i (by rw [length_decList]; exact hi)]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (returnCfg w k hk l first d (i + 1)) (returnState first)
    (returnState first) idle (none, -1) idle rfl
    (by rw [hsym]; exact tr_returnState_digit _ _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change ((i + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (i : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 2 => exact add_zero _

/-- A decrement's borrow and return: from the lowest digit, out through the
zeros, the absorbing step, and back to the base cell, in
{lit}`2 * borrowLength d + 1` steps. -/
theorem run_decrement (first : Bool) (d : List Bool) (hd : allFalse d = false)
    (hlen : d.length ≤ bound w + 2) :
    Run w (borrowCfg w k hk l first d 0) (returnCfg w k hk l first d 0)
      (2 * borrowLength d + 1) := by
  have htz := borrowLength_lt_length d hd
  rw [show 2 * borrowLength d + 1 = borrowLength d + 1 + borrowLength d by omega]
  exact run_seq _ _ _ _ _
    (run_seq _ _ _ _ _
      (run_family (borrowCfg w k hk l first d) (borrowLength d)
        (fun i hi ↦ borrowCfg_step w k hk l first d i hi)
        (fun i hi ↦ headsLE_borrowCfg w k hk l first d hlen i (by omega)))
      (run_step _ _ (borrowCfg_flip w k hk l first d hd)
        (headsLE_borrowCfg w k hk l first d hlen _ htz.le)
        (headsLE_returnCfg w k hk l first d hlen _ htz.le)))
    (run_family_down (returnCfg w k hk l first d) (borrowLength d)
      (fun i hi ↦ returnCfg_step w k hk l first d i (by omega))
      (fun i hi ↦ headsLE_returnCfg w k hk l first d hlen i (by omega)))

end Borrow

section Fail

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- The step past the digits' end: the borrow ran into blank, so the count was
zero, and the erasure begins. -/
theorem borrowCfg_blank (d : List Bool) :
    bitTreeScanner.step (borrowCfg w k hk l false d d.length) = clearCfg w k hk l d.length ∧
      bitTreeScanner.outputSymbol (borrowCfg w k hk l false d d.length) = none := by
  have hsym : (borrowCfg w k hk l false d d.length).workTapeSymbols =
      ![tapeCount l 1, none, some 3] := by
    rw [workTapeSymbols_borrowCfg, tapeDigits_of_ge d _ (by omega)]
  obtain ⟨hstep, hout⟩ := step_stay (borrowCfg w k hk l false d d.length) stBorrow stClear idle
    (none, -1) idle rfl (by rw [hsym]; exact tr_borrow_blank _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change (if 1 ≤ z ∧ z ≤ (d.length : ℤ) then some 1 else tapeDigits d z) =
        if 1 ≤ z ∧ z ≤ (d.length : ℤ) then some 1 else tapeBase z
      by_cases h1 : 1 ≤ z ∧ z ≤ (d.length : ℤ)
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1, tapeDigits, tapeBase]
        by_cases hz : z = 0
        · rw [ite_eq_left hz, ite_eq_left hz]
        · rw [ite_eq_right hz, ite_eq_right hz, digitsAt, ite_eq_right (by omega)]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change (d.length : ℤ) + 1 + ((-1 : SignType) : ℤ) = (d.length : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 2 => exact add_zero _

/-- One step of the erasure. -/
theorem clearCfg_step (i : ℕ) :
    bitTreeScanner.step (clearCfg w k hk l (i + 1)) = clearCfg w k hk l i ∧
      bitTreeScanner.outputSymbol (clearCfg w k hk l (i + 1)) = none := by
  have hsym : (clearCfg w k hk l (i + 1)).workTapeSymbols =
      ![tapeCount l 1, some (boolEmb true), some 3] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount l 1, if 1 ≤ ((i + 1 : ℕ) : ℤ) ∧ ((i + 1 : ℕ) : ℤ) ≤ ((i + 1 : ℕ) : ℤ)
      then some 1 else tapeBase ((i + 1 : ℕ) : ℤ), tapeDigits w.length.bits 0] = _
    rw [ite_eq_left ⟨by omega, le_rfl⟩]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (clearCfg w k hk l (i + 1)) stClear stClear idle
    (some none, -1) idle rfl (by rw [hsym]; exact tr_clear_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) then some 1 else tapeBase z)
        ((i + 1 : ℕ) : ℤ) none z =
        if 1 ≤ z ∧ z ≤ (i : ℤ) then some 1 else tapeBase z
      rw [Function.update_apply]
      by_cases hz : z = ((i + 1 : ℕ) : ℤ)
      · rw [ite_eq_left hz, ite_eq_right (show ¬(1 ≤ z ∧ z ≤ (i : ℤ)) by omega), tapeBase,
          ite_eq_right (show ¬z = 0 by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (i : ℤ)
        · rw [ite_eq_left (show 1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ) by omega), ite_eq_left h1]
        · rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((i + 1 : ℕ) : ℤ)) by omega), ite_eq_right h1]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change ((i + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (i : ℤ)
      rw [SignType.coe_neg_one]
      omega
    | 2 => exact add_zero _

/-- A decrement finding the count at zero: out across the digits, back
erasing them, and the pending count's decrement closing the leaf, in
{name}`Geb.BitTreeScanner.failCost` steps, to the closed form at the state the
closed tree leaves. -/
theorem run_fail (c : ℕ) (d : List Bool) (hd : allFalse d = true) (hlen : d.length ≤ bound w + 2)
    (hn : Redundant.nlz l = true) (hv : Redundant.value l = c) (hl : l.length ≤ bound w) :
    Run w (borrowCfg w k hk l false d 0) (cfgAt w k hk (close c) (Redundant.dec l))
      (failCost d.length l) := by
  have htz := borrowLength_of_allFalse d hd
  rw [failCost, show 2 * d.length + 1 + decCost l = d.length + 1 + d.length + decCost l by omega]
  refine run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ ?_
    (run_step _ _ (borrowCfg_blank w k hk l d) (headsLE_borrowCfg w k hk l false d hlen _ le_rfl)
      (headsLE_clearCfg w k hk l _ hlen)))
    (run_family_down (clearCfg w k hk l) d.length (fun i _ ↦ clearCfg_step w k hk l i)
      (fun i hi ↦ headsLE_clearCfg w k hk l i (by omega)))) ?_
  · have := run_family (borrowCfg w k hk l false d) d.length
      (fun i hi ↦ borrowCfg_step w k hk l false d i (by omega))
      (fun i hi ↦ headsLE_borrowCfg w k hk l false d hlen i hi)
    exact this
  · rw [clearCfg_zero]
    exact run_close w k hk l hn c hl hv

end Fail

section Settle

variable (w : List Bool) (k : ℕ) (hk : k ≤ w.length) (l : List Redundant.Digit)

/-- The step from complete digits to the first decrement. -/
theorem cfgAt_bits_full_step (c : ℕ) (d : List Bool) :
    bitTreeScanner.step (cfgAt w k hk ⟨.bits, c, d.length, d⟩ l) =
        borrowCfg w k hk l true d 0 ∧
      bitTreeScanner.outputSymbol (cfgAt w k hk ⟨.bits, c, d.length, d⟩ l) = none := by
  have hsym : (cfgAt w k hk ⟨.bits, c, d.length, d⟩ l).workTapeSymbols =
      ![tapeCount l 1, some 3, tapeDigits w.length.bits (headRuler ⟨.bits, c, d.length, d⟩)] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount l 1, tapeLeaf ⟨.bits, c, d.length, d⟩ (headLeaf ⟨.bits, c, d.length, d⟩),
      tapeDigits w.length.bits (headRuler ⟨.bits, c, d.length, d⟩)] = _
    rw [tapeLeaf_bits_full, headLeaf]
    change ![tapeCount l 1, tapeDigits d ((d.length - d.length : ℕ) : ℤ), _] = _
    rw [Nat.sub_self]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (cfgAt w k hk ⟨.bits, c, d.length, d⟩ l) stBits stBorrowInit
    idle (none, 1) idle rfl (by rw [hsym]; exact tr_bits_base _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change tapeLeaf ⟨.bits, c, d.length, d⟩ z =
        if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 1 else tapeDigits d z
      rw [ite_eq_right (show ¬(1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ)) by omega), tapeLeaf_bits_full]
    | 2 => rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 =>
      change headLeaf ⟨.bits, c, d.length, d⟩ + ((1 : SignType) : ℤ) = ((0 : ℕ) : ℤ) + 1
      rw [SignType.coe_one, headLeaf]
      change ((d.length - d.length : ℕ) : ℤ) + 1 = ((0 : ℕ) : ℤ) + 1
      rw [Nat.sub_self]
    | 2 =>
      change headRuler ⟨.bits, c, d.length, d⟩ + ((0 : SignType) : ℤ) = 0
      rw [SignType.coe_zero, headRuler]
      change ((d.length - d.length : ℕ) : ℤ) + 0 = 0
      rw [Nat.sub_self]
      rfl

/-- The first decrement's return reaching the base marker steps to the lowest
digit, where the countdown begins. -/
theorem returnCfg_init_exit (d : List Bool) :
    bitTreeScanner.step (returnCfg w k hk l true d 0) = borrowCfg w k hk l false (decList d) 0 ∧
      bitTreeScanner.outputSymbol (returnCfg w k hk l true d 0) = none := by
  have hsym : (returnCfg w k hk l true d 0).workTapeSymbols = ![tapeCount l 1, some 3, some 3] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (returnCfg w k hk l true d 0) stReturnInit stBorrow idle
    (none, 1) idle rfl (by rw [hsym]; exact tr_returnInit_base _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
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

/-- The work after a payload bit: the failed decrement that detects the
payload's end and closes the leaf, when no payload remains, in
{name}`Geb.BitTreeScanner.pendingCount` steps, to the closed form at the state the
bit settles in. -/
theorem run_pendingCount (c wd : ℕ) (d : List Bool) (hlen : d.length = wd)
    (hw : wd ≤ bound w + 2) (hn : Redundant.nlz l = true) (hv : Redundant.value l = c)
    (hl : l.length ≤ bound w) :
    Run w (cfgAt w k hk ⟨.count, c, wd, d⟩ l) (cfgAt w k hk (settleCount c wd d) (settleTree d l))
      (pendingCount wd d l) := by
  subst hlen
  cases hd : allFalse d with
  | true =>
    rw [settleCount_of_allFalse _ _ _ hd, pendingCount, hd, Bool.cond_true, settleTree, hd,
      Bool.cond_true, cfgAt_count]
    exact run_fail w k hk l c d hd hw hn hv hl
  | false =>
    rw [settleCount_of_not_allFalse _ _ _ hd, pendingCount, hd, Bool.cond_false, settleTree, hd,
      Bool.cond_false]
    exact run_zero _ (headsLE_mk w _ _ _ 1 1 0 (by rw [headBound]; omega)
      (by rw [headBound]; omega) (by rw [headBound]; omega))

/-- The work after a length digit: when the digits are complete, the step to
the lowest digit, the first decrement, and what follows a payload bit, in
{name}`Geb.BitTreeScanner.pendingDigits` steps, to the closed form at the state the
digit settles in. -/
theorem run_pendingDigits (c wd : ℕ) (d : List Bool) (hd : allFalse d = false)
    (hle : d.length ≤ wd) (hw : wd ≤ bound w + 2) (hn : Redundant.nlz l = true)
    (hv : Redundant.value l = c) (hl : l.length ≤ bound w) :
    Run w (cfgAt w k hk ⟨.bits, c, wd, d⟩ l)
      (cfgAt w k hk (settleDigits c wd d) (settleTreeDigits wd d l)) (pendingDigits wd d l) := by
  by_cases hfull : d.length = wd
  · subst hfull
    rw [settleDigits_of_length_eq _ _ _ rfl, pendingDigits, ite_eq_left rfl, chainCost,
      settleTreeDigits, ite_eq_left rfl]
    have h₄ := run_pendingCount w k hk l c d.length (decList d) (length_decList d) hw hn hv hl
    rw [cfgAt_count w k hk l c d.length (decList d)] at h₄
    rw [show 1 + (2 * borrowLength d + 2) + pendingCount d.length (decList d) l =
      1 + (2 * borrowLength d + 1) + 1 + pendingCount d.length (decList d) l by omega]
    exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
      (run_step _ _ (cfgAt_bits_full_step w k hk l c d)
        (headsLE_mk w _ _ _ 1 (headLeaf ⟨.bits, c, d.length, d⟩) (headRuler ⟨.bits, c, d.length, d⟩)
          (by rw [headBound]; omega)
          (by rw [headBound, headLeaf_bits]; omega)
          (by rw [headBound, headRuler_bits]; omega))
        (headsLE_borrowCfg w k hk l true d hw 0 (Nat.zero_le _)))
      (run_decrement w k hk l true d hd hw))
      (run_step _ _ (returnCfg_init_exit w k hk l d)
        (headsLE_returnCfg w k hk l true d hw 0 (Nat.zero_le _))
        (headsLE_borrowCfg w k hk l false (decList d) (by rw [length_decList]; exact hw) 0
          (Nat.zero_le _)))) h₄
  · rw [settleDigits_of_length_ne _ _ _ hfull, pendingDigits, ite_eq_right hfull, settleTreeDigits,
      ite_eq_right hfull]
    exact run_zero _ (headsLE_mk w _ _ _ 1 (headLeaf ⟨.bits, c, wd, d⟩)
      (headRuler ⟨.bits, c, wd, d⟩) (by rw [headBound]; omega)
      (by rw [headBound, headLeaf_bits]; omega)
      (by rw [headBound, headRuler_bits]; omega))

end Settle

end Geb.BitTreeScanner
