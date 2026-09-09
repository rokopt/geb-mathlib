/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Counter

set_option doc.verso true

/-!
# The scan's invariant and the machine's cost per bit

The states the scan reaches from its initial state satisfy an invariant,
{lit}`Geb.BitTreeScanner.Good`, which the machine's closed-form configuration
needs: the digit cells a leaf claims hold its digits and number at most the
bound and two, the countdown holds a positive count, and outside a leaf
nothing is held. Against that invariant the module states the number of
machine steps each input bit costs, {lit}`Geb.BitTreeScanner.cost`, and bounds the
total by a potential over the three counters the machine keeps: the leaf's
digits, the pending count in the redundant counter, and, during the pass
that counts the input, that count. Each pays for its own chains, so a bit
costs a constant amortised.

A bit costs one step unless it is a pair bit, whose increment carries through
the twos at the bottom of the pending count, or a payload bit, whose countdown
borrows through the zeros below the lowest one of the remaining count; a
leaf's length digits and its last payload bit carry the work the machine does
before the next bit: the one decrement that turns the length read into the
payload remaining, the failed decrement that detects the payload's end and
clears the digit cells, and the decrement of the pending count that closes
the leaf. The input's length is counted first, in ordinary binary, an
increment per input bit, with the same accounting.

## Main definitions

* {lit}`Geb.BitTreeScanner.borrowLength` — the number of zeros below the lowest one
  of a digit list, the length of a borrow.
* {lit}`Geb.BitTreeScanner.Good` — the invariant, at a bound.
* {lit}`Geb.BitTreeScanner.incCost`, {lit}`Geb.BitTreeScanner.decCost` — the steps an
  increment and a decrement of the pending count cost.
* {lit}`Geb.BitTreeScanner.chainCost`, {lit}`Geb.BitTreeScanner.failCost`,
  {lit}`Geb.BitTreeScanner.pendingCount`, {lit}`Geb.BitTreeScanner.pendingDigits`,
  {lit}`Geb.BitTreeScanner.cost` — the steps a bit costs.
* {lit}`Geb.BitTreeScanner.endCost` — the steps from the state at the input's end to
  the halt.
* {lit}`Geb.BitTreeScanner.runAux`, {lit}`Geb.BitTreeScanner.time` — the steps a word
  costs.
* {lit}`Geb.BitTreeScanner.incB`, {lit}`Geb.BitTreeScanner.carryLengthB`,
  {lit}`Geb.BitTreeScanner.seekIncCost`, {lit}`Geb.BitTreeScanner.seekTime` — the
  increment in ordinary binary, its carry, and the steps the pass counting
  the input costs.
* {lit}`Geb.BitTreeScanner.potential` — the potential over the leaf's digits and
  the pending count.

## Main statements

* {lit}`Geb.BitTreeScanner.good_init`, {lit}`Geb.BitTreeScanner.good_scanStep`,
  {lit}`Geb.BitTreeScanner.good_scanAt` — the invariant holds initially and is
  preserved.
* {lit}`Geb.BitTreeScanner.count_le_length` — the pending count is at most the
  bits read.
* {lit}`Geb.BitTreeScanner.length_treeAt_le` — the pending count's digits are at
  most the bound.
* {lit}`Geb.BitTreeScanner.count_false_decList`, {lit}`Geb.BitTreeScanner.borrowLength_lt_length`,
  {lit}`Geb.BitTreeScanner.eq_of_allFalse_decList` — the borrow's effect on the
  zero digits, its length, and the shape of a count of one.
* {lit}`Geb.BitTreeScanner.getD_of_lt_borrowLength`, {lit}`Geb.BitTreeScanner.getD_borrowLength`,
  {lit}`Geb.BitTreeScanner.getD_decList_of_lt`, {lit}`Geb.BitTreeScanner.getD_decList_borrowLength`,
  {lit}`Geb.BitTreeScanner.getD_decList_of_gt`, {lit}`Geb.BitTreeScanner.borrowLength_of_allFalse` —
  the digits below, at and above the borrow's length, before and after the
  decrement.
* {lit}`Geb.BitTreeScanner.incCost_add_nonOnes_le`, {lit}`Geb.BitTreeScanner.decCost_add_nonOnes_le`
  — the pending count's chains against its potential.
* {lit}`Geb.BitTreeScanner.cost_add_potential_le` — a bit costs at most a constant
  amortised against the potential.
* {lit}`Geb.BitTreeScanner.time_take_succ` — the time of a prefix extended by one
  bit.
* {lit}`Geb.BitTreeScanner.time_add_endCost_le` — the scan's time bound with the
  steps to the halt.
* {lit}`Geb.BitTreeScanner.bits_succ`, {lit}`Geb.BitTreeScanner.seekTime_le` — the ordinary
  increment is the successor's digits, and the counting pass's time bound.

## Implementation notes

{lit}`Good` is a {lit}`Prop`-valued match on the mode, so that at a literal
mode it unfolds to the conjunction that mode carries. {lit}`cost` matches on
the mode and the bit as {name}`Geb.BitTreeScanner.scanStep` does, so the two case
analyses align in {lit}`cost_add_potential_le`. The pending count's costs are
stated on the counter the replay {name}`Geb.BitTreeScanner.treeAt` keeps, so the
cost of a bit is a function of the scan's state and the counter together.

## Tags

amortised analysis, potential, binary counter, Turing machine, cost model
-/

@[expose] public section

namespace Geb.BitTreeScanner

section Digits

/-- The number of zeros below the lowest one of a digit list: the length of the
borrow a decrement propagates. At an all-zero list, its length. -/
def borrowLength (d : List Bool) : ℕ := d.foldr (fun b n ↦ cond b 0 (n + 1)) 0

/-- A zero at the bottom lengthens the borrow. -/
@[simp] theorem borrowLength_cons_false (d : List Bool) :
    borrowLength (false :: d) = borrowLength d + 1 := rfl

/-- A one at the bottom absorbs the borrow at once. -/
@[simp] theorem borrowLength_cons_true (d : List Bool) : borrowLength (true :: d) = 0 := rfl

/-- The borrow is at most the whole list. -/
theorem borrowLength_le_length (d : List Bool) : borrowLength d ≤ d.length :=
  List.rec (motive := fun d ↦ borrowLength d ≤ d.length) le_rfl
    (fun b d ih ↦ by
      cases b with
      | false => rw [borrowLength_cons_false, List.length_cons]; exact Nat.succ_le_succ ih
      | true => rw [borrowLength_cons_true]; exact Nat.zero_le _) d

/-- A digit list with a one has a borrow shorter than itself. -/
theorem borrowLength_lt_length (d : List Bool) (h : allFalse d = false) :
    borrowLength d < d.length :=
  List.rec (motive := fun d ↦ allFalse d = false → borrowLength d < d.length) (fun h ↦ nomatch h)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [borrowLength_cons_false, List.length_cons]
        exact Nat.succ_lt_succ (ih h)
      | true =>
        rw [borrowLength_cons_true, List.length_cons]
        exact Nat.succ_pos _) d h

/-- A zero at the bottom is counted. -/
theorem count_false_cons_false (d : List Bool) : (false :: d).count false = d.count false + 1 := by
  simp

/-- A one at the bottom is not counted. -/
theorem count_false_cons_true (d : List Bool) : (true :: d).count false = d.count false := by
  simp

/-- A one at the bottom is counted among the ones. -/
theorem count_true_cons_true (d : List Bool) : (true :: d).count true = d.count true + 1 := by
  simp

/-- A zero at the bottom is not counted among the ones. -/
theorem count_true_cons_false (d : List Bool) : (false :: d).count true = d.count true := by
  simp

/-- An all-zero list has as many zeros as digits. -/
theorem count_false_of_allFalse (d : List Bool) (h : allFalse d = true) :
    d.count false = d.length :=
  List.rec (motive := fun d ↦ allFalse d = true → d.count false = d.length) (fun _ ↦ rfl)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [count_false_cons_false, ih h, List.length_cons]
      | true => rw [allFalse_cons] at h; exact nomatch h) d h

/-- A decrement of a positive count turns the zeros of the borrow into ones and
one one into a zero. -/
theorem count_false_decList (d : List Bool) (h : allFalse d = false) :
    (decList d).count false + borrowLength d = d.count false + 1 :=
  List.rec
    (motive := fun d ↦ allFalse d = false →
      (decList d).count false + borrowLength d = d.count false + 1)
    (fun h ↦ nomatch h)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [decList_cons_false, borrowLength_cons_false, count_false_cons_true,
          count_false_cons_false]
        have := ih h
        omega
      | true =>
        rw [decList_cons_true, borrowLength_cons_true, count_false_cons_false,
          count_false_cons_true]) d h

/-- A positive count whose decrement is zero is one: a one at the bottom and
zeros above it. -/
theorem eq_of_allFalse_decList (d : List Bool) (h : allFalse d = false)
    (h' : allFalse (decList d) = true) : borrowLength d = 0 ∧ d.count false + 1 = d.length := by
  cases d with
  | nil => exact nomatch h
  | cons b d =>
    cases b with
    | false => rw [decList_cons_false, allFalse_cons] at h'; exact nomatch h'
    | true =>
      rw [decList_cons_true, allFalse_cons, Bool.not_false, Bool.true_and] at h'
      rw [borrowLength_cons_true, count_false_cons_true, List.length_cons,
        count_false_of_allFalse d h']
      exact ⟨rfl, rfl⟩

/-- Below the borrow's length a digit is a zero. -/
theorem getD_of_lt_borrowLength (d : List Bool) :
    ∀ i, i < borrowLength d → d.getD i false = false :=
  List.rec (motive := fun d ↦ ∀ i, i < borrowLength d → d.getD i false = false)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun b d ih i hi ↦ by
      cases b with
      | false =>
        cases i with
        | zero => rfl
        | succ i => rw [borrowLength_cons_false] at hi; exact ih i (by omega)
      | true => rw [borrowLength_cons_true] at hi; exact absurd hi (Nat.not_lt_zero _)) d

/-- At the borrow's length the digit is a one. -/
theorem getD_borrowLength (d : List Bool) (h : allFalse d = false) :
    d.getD (borrowLength d) false = true :=
  List.rec (motive := fun d ↦ allFalse d = false → d.getD (borrowLength d) false = true)
    (fun h ↦ nomatch h)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [borrowLength_cons_false]
        exact ih h
      | true => rfl) d h

/-- The decrement turns the digits below the borrow's length into ones. -/
theorem getD_decList_of_lt (d : List Bool) :
    ∀ i, i < borrowLength d → (decList d).getD i false = true :=
  List.rec (motive := fun d ↦ ∀ i, i < borrowLength d → (decList d).getD i false = true)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun b d ih i hi ↦ by
      cases b with
      | false =>
        rw [decList_cons_false]
        cases i with
        | zero => rfl
        | succ i => rw [borrowLength_cons_false] at hi; exact ih i (by omega)
      | true => rw [borrowLength_cons_true] at hi; exact absurd hi (Nat.not_lt_zero _)) d

/-- The decrement turns the digit at the borrow's length into a zero. -/
theorem getD_decList_borrowLength (d : List Bool) (h : allFalse d = false) :
    (decList d).getD (borrowLength d) false = false :=
  List.rec (motive := fun d ↦ allFalse d = false → (decList d).getD (borrowLength d) false = false)
    (fun h ↦ nomatch h)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [decList_cons_false, borrowLength_cons_false]
        exact ih h
      | true => rfl) d h

/-- The decrement leaves the digits above the borrow's length. -/
theorem getD_decList_of_gt (d : List Bool) :
    ∀ i, borrowLength d < i → (decList d).getD i false = d.getD i false :=
  List.rec (motive := fun d ↦ ∀ i, borrowLength d < i → (decList d).getD i false = d.getD i false)
    (fun _ _ ↦ rfl)
    (fun b d ih i hi ↦ by
      cases b with
      | false =>
        rw [decList_cons_false]
        cases i with
        | zero => rw [borrowLength_cons_false] at hi; exact absurd hi (Nat.not_lt_zero _)
        | succ i => rw [borrowLength_cons_false] at hi; exact ih i (by omega)
      | true =>
        rw [decList_cons_true]
        cases i with
        | zero => rw [borrowLength_cons_true] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i => rfl) d

/-- An all-zero list's borrow is its whole length. -/
theorem borrowLength_of_allFalse (d : List Bool) (h : allFalse d = true) :
    borrowLength d = d.length :=
  List.rec (motive := fun d ↦ allFalse d = true → borrowLength d = d.length) (fun _ ↦ rfl)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [allFalse_cons, Bool.not_false, Bool.true_and] at h
        rw [borrowLength_cons_false, ih h, List.length_cons]
      | true => rw [allFalse_cons] at h; exact nomatch h) d h

end Digits

section Invariant

variable (W : ℕ)

/-- The invariant of the states the scan reaches at a bound: outside a leaf
nothing is held; reading the zeros nothing is held yet and the width is at
most the bound and one, as after failure, which keeps the width the zeros
reached; reading the digits, at least one and fewer than the width are held,
the most significant a one, the width at most the bound and two; in the
countdown the digits fill the width, at most the bound and two, and denote a
positive count. -/
def Good (s : Scan) : Prop :=
  match s.mode with
  | .term | .done => s.width = 0 ∧ s.digits = []
  | .zeros | .dead => s.digits = [] ∧ s.width ≤ W + 1
  | .bits => s.digits.length < s.width ∧ (∃ r, s.digits = r ++ [true]) ∧ s.width ≤ W + 2
  | .count => allFalse s.digits = false ∧ s.digits.length = s.width ∧ s.width ≤ W + 2

/-- The initial state satisfies the invariant. -/
theorem good_init : Good W init := ⟨rfl, rfl⟩

/-- The state a completed tree leaves satisfies the invariant. -/
theorem good_close (c : ℕ) : Good W (close c) := by
  cases c <;> exact ⟨rfl, rfl⟩

/-- The state after a payload bit satisfies the invariant, the digits filling
the width. -/
theorem good_settleCount (c w : ℕ) (d : List Bool) (hlen : d.length = w) (hw : w ≤ W + 2) :
    Good W (settleCount c w d) := by
  cases hf : allFalse d with
  | true => rw [settleCount_of_allFalse _ _ _ hf]; exact good_close W c
  | false => rw [settleCount_of_not_allFalse _ _ _ hf]; exact ⟨hf, hlen, hw⟩

/-- The state after a length digit satisfies the invariant, the digits ending
in a one and not exceeding the width. -/
theorem good_settleDigits (c w : ℕ) (d : List Bool) (hr : ∃ r, d = r ++ [true])
    (hle : d.length ≤ w) (hw : w ≤ W + 2) : Good W (settleDigits c w d) := by
  by_cases hfull : d.length = w
  · rw [settleDigits_of_length_eq _ _ _ hfull]
    exact good_settleCount W c w _ (by rw [length_decList, hfull]) hw
  · rw [settleDigits_of_length_ne _ _ _ hfull]
    obtain ⟨r, hr⟩ := hr
    change d.length < w ∧ (∃ r, d = r ++ [true]) ∧ w ≤ W + 2
    exact ⟨by omega, ⟨r, hr⟩, hw⟩

/-- The scan preserves the invariant. -/
theorem good_scanStep (s : Scan) (h : Good W s) (b : Bool) : Good W (scanStep W s b) := by
  obtain ⟨m, c, w, d⟩ := s
  cases m <;> dsimp only [Good] at h
  · cases b with
    | true => rw [scanStep_term_true]; exact ⟨rfl, rfl⟩
    | false => rw [scanStep_term_false]; exact ⟨rfl, Nat.zero_le _⟩
  · obtain ⟨hd, hw⟩ := h
    cases b with
    | false =>
      by_cases hW : W < w
      · rw [scanStep_zeros_false_of_lt W _ _ _ hW]; exact ⟨rfl, hw⟩
      · rw [scanStep_zeros_false W _ _ _ (by omega)]
        exact ⟨rfl, by change w + 1 ≤ W + 1; omega⟩
    | true =>
      rw [scanStep_zeros_true]
      exact good_settleDigits W c (w + 1) [true] ⟨[], rfl⟩ (by rw [List.length_singleton]; omega)
        (by omega)
  · obtain ⟨hlt, ⟨r, hr⟩, hw⟩ := h
    rw [scanStep_bits]
    exact good_settleDigits W c w (b :: d) ⟨b :: r, by rw [hr, List.cons_append]⟩
      (by rw [List.length_cons]; exact hlt) hw
  · obtain ⟨_, hlen, hw⟩ := h
    rw [scanStep_count]
    exact good_settleCount W c w _ (by rw [length_decList, hlen]) hw
  · rw [scanStep_done]; exact ⟨rfl, Nat.zero_le _⟩
  · rw [scanStep_dead]; exact h

/-- The scan of any word from a state satisfying the invariant satisfies it. -/
theorem good_scanFrom (w : List Bool) : ∀ s, Good W s → Good W (scanFrom W w s) :=
  List.rec (motive := fun w ↦ ∀ s, Good W s → Good W (scanFrom W w s)) (fun _ h ↦ h)
    (fun b _ ih s h ↦ by rw [scanFrom_cons]; exact ih _ (good_scanStep W s h b)) w

/-- The scan of any word satisfies the invariant. -/
theorem good_scanAt (w : List Bool) : Good W (scanAt W w) := good_scanFrom W w init (good_init W)

/-- A step raises the pending count by at most one. -/
theorem count_scanStep_le (s : Scan) (b : Bool) : (scanStep W s b).count ≤ s.count + 1 := by
  by_cases hm : s.mode = .term ∧ b = true
  · obtain ⟨m, c, wd, d⟩ := s
    obtain ⟨hm, hb⟩ := hm
    change m = .term at hm
    subst hm hb
    rw [scanStep_term_true]
  · cases hc : closes W s b with
    | true =>
      rw [scanStep_eq_close_of_closes W s b hc]
      generalize s.count = c
      cases c with
      | zero => exact Nat.zero_le _
      | succ c => rw [close_succ]; change c ≤ c + 1 + 1; omega
    | false => rw [count_scanStep_of_not_closes W s b hm hc]; exact Nat.le_succ _

/-- The pending count after a word from a state is at most the state's and the
word's length. -/
theorem count_scanFrom_le (w : List Bool) :
    ∀ s, (scanFrom W w s).count ≤ s.count + w.length :=
  List.rec (motive := fun w ↦ ∀ s, (scanFrom W w s).count ≤ s.count + w.length)
    (fun _ ↦ le_rfl)
    (fun b w ih s ↦ by
      rw [scanFrom_cons, List.length_cons]
      have h1 := ih (scanStep W s b)
      have h2 := count_scanStep_le W s b
      omega) w

/-- The pending count is at most the bits read. -/
theorem count_le_length (w : List Bool) : (scanAt W w).count ≤ w.length := by
  have := count_scanFrom_le W w init
  rw [scanAt]
  exact le_trans this (le_of_eq (Nat.zero_add _))

/-- The pending count's digits, at a prefix of a word scanned at its bound, are
at most the bound. -/
theorem length_treeAt_le (w : List Bool) (k : ℕ) (hk : k ≤ w.length) :
    (treeAt (bound w) (w.take k)).length ≤ bound w := by
  obtain ⟨hn, hv⟩ := goodTree_treeAt (bound w) (w.take k)
  refine le_trans (Redundant.length_le_bits_length _ hn) ?_
  rw [hv]
  exact bits_length_mono (le_trans (count_le_length _ _) (by rw [List.length_take]; omega))

end Invariant

section Cost

/-- The steps an increment of the pending count costs: one when the lowest
digit is below two, else out through the twos, the raising step, back to the
base marker and the step consuming the bit. -/
def incCost (l : List Redundant.Digit) : ℕ :=
  if Redundant.carryLength l = 0 then 1 else 2 * Redundant.carryLength l + 2

/-- The steps a decrement of the pending count costs: one at an empty counter
or a two at the bottom; otherwise out through the zeros, the absorbing step,
back to the base marker and the step there, the absorbing digit being tested
for being the top, and erased when it is, when it is a one. -/
def decCost (l : List Redundant.Digit) : ℕ :=
  match l with
  | [] => 1
  | 2 :: _ => 1
  | 0 :: _ | 1 :: _ =>
    if l.getD (Redundant.borrowLength l) 0 = 2 then 2 * Redundant.borrowLength l + 2
    else 2 * Redundant.borrowLength l + 4

/-- An increment's steps against the pending count's potential. -/
theorem incCost_add_nonOnes_le (l : List Redundant.Digit) :
    incCost l + 2 * Redundant.nonOnes (Redundant.inc l) ≤ 2 * Redundant.nonOnes l + 4 := by
  have := Redundant.nonOnes_inc_add_carryLength_le l
  rw [incCost]
  split_ifs with h <;> omega

/-- The absorbing digit of a borrow is not a zero. -/
theorem getD_borrowLength_ne_zero (l : List Redundant.Digit) (hn : Redundant.nlz l = true)
    (h : l ≠ []) : l.getD (Redundant.borrowLength l) 0 ≠ 0 :=
  List.rec
    (motive := fun l ↦ Redundant.nlz l = true → l ≠ [] → l.getD (Redundant.borrowLength l) 0 ≠ 0)
    (fun _ h ↦ absurd rfl h)
    (fun d l ih hn _ ↦ by
      match d with
      | 0 =>
        have hl := Redundant.ne_nil_of_nlz_cons_zero l hn
        rw [Redundant.borrowLength_cons_zero, List.getD_cons_succ]
        exact ih (Redundant.nlz_of_nlz_cons 0 l hn hl) hl
      | 1 => rw [Redundant.borrowLength_cons_one, List.getD_cons_zero]; decide
      | 2 => rw [Redundant.borrowLength_cons_two, List.getD_cons_zero]; decide) l hn h

/-- A decrement's steps against the pending count's potential. -/
theorem decCost_add_nonOnes_le (l : List Redundant.Digit) :
    decCost l + 2 * Redundant.nonOnes (Redundant.dec l) ≤ 2 * Redundant.nonOnes l + 6 := by
  have := Redundant.nonOnes_dec_add_borrowLength_le l
  cases l with
  | nil => decide
  | cons d l =>
    match d with
    | 0 =>
      rw [decCost]
      split_ifs <;> omega
    | 1 =>
      rw [decCost, Redundant.borrowLength_cons_one, List.getD_cons_zero,
        ite_eq_right (by decide)]
      cases l with
      | nil => decide
      | cons e l => rw [Redundant.dec_cons_one_cons] at this ⊢; omega
    | 2 => rw [decCost, Redundant.dec_cons_two] at *; omega

/-- The steps a decrement of the leaf's count costs: out along the borrow,
back, and the step at the base marker. -/
def chainCost (d : List Bool) : ℕ := 2 * borrowLength d + 2

/-- The steps a failed decrement of the leaf's count costs at a width, with
the pending count's decrement that closes the leaf: out across the cells,
back erasing them, and the decrement from the base marker. -/
def failCost (w : ℕ) (l : List Redundant.Digit) : ℕ := 2 * w + 1 + decCost l

/-- The steps after a payload bit before the next bit: the failed decrement
that detects the payload's end and closes the leaf, when no payload
remains. -/
def pendingCount (w : ℕ) (d : List Bool) (l : List Redundant.Digit) : ℕ :=
  cond (allFalse d) (failCost w l) 0

/-- The steps after a length digit before the next bit: when the digits fill
the width, the step to the lowest digit, the decrement that turns the length
read into the payload remaining, and what follows a payload bit. -/
def pendingDigits (w : ℕ) (d : List Bool) (l : List Redundant.Digit) : ℕ :=
  if d.length = w then 1 + chainCost d + pendingCount w (decList d) l else 0

/-- The steps a bit costs at a state satisfying the invariant and the pending
count's counter, including the steps before the next bit. -/
def cost (s : Scan) (b : Bool) (l : List Redundant.Digit) : ℕ :=
  match s.mode, b with
  | .term, true => incCost l
  | .term, false => 1
  | .zeros, false => 1
  | .zeros, true => 1 + pendingDigits (s.width + 1) [true] l
  | .bits, _ => 1 + pendingDigits s.width (b :: s.digits) l
  | .count, _ => chainCost s.digits + pendingCount s.width (decList s.digits) l
  | .done, _ => 1
  | .dead, _ => 1

/-- The steps from the state at the input's end to the halt: one, the emitting
step, except in the countdown, where the decrement runs to the base marker
before the step there finds the input ended. -/
def endCost (s : Scan) : ℕ :=
  match s.mode with
  | .count => chainCost s.digits
  | _ => 1

variable (W : ℕ)

/-- The scan with the counter and the time: the state, the counter and the
steps so far. -/
def runAux (w : List Bool) (p : Scan × List Redundant.Digit × ℕ) :
    Scan × List Redundant.Digit × ℕ :=
  w.foldl (fun p b ↦ (scanStep W p.1 b, treeStep W p.1 b p.2.1, p.2.2 + cost p.1 b p.2.1)) p

/-- The steps a word costs from the initial state, at a bound. -/
def time (w : List Bool) : ℕ := (runAux W w (init, [], 0)).2.2

/-- The potential over the leaf's digits and the pending count: weighted zero
digits and weighted width of the leaf's digits, and twice the pending count's
digits that are not one. -/
def potential (s : Scan) (l : List Redundant.Digit) : ℕ :=
  (match s.mode with
    | .zeros => 2 * s.width + 4
    | .bits => 2 * s.digits.count false + 2 * s.width + 6
    | .count => 2 * s.digits.count false + 2 * s.width + 2
    | _ => 0) + 2 * Redundant.nonOnes l

/-- The potential of the state a completed tree leaves is the counter's. -/
theorem potential_close (c : ℕ) (l : List Redundant.Digit) :
    potential (close c) l = 2 * Redundant.nonOnes l := by
  cases c <;> exact Nat.zero_add _

/-- The potential of the initial state is zero. -/
theorem potential_init : potential init [] = 0 := rfl

/-- The scan with the time reads the empty word as nothing. -/
@[simp] theorem runAux_nil (p : Scan × List Redundant.Digit × ℕ) : runAux W [] p = p := rfl

/-- The scan with the time reads the head bit first. -/
@[simp] theorem runAux_cons (b : Bool) (w : List Bool) (p : Scan × List Redundant.Digit × ℕ) :
    runAux W (b :: w) p =
      runAux W w (scanStep W p.1 b, treeStep W p.1 b p.2.1, p.2.2 + cost p.1 b p.2.1) := rfl

/-- The scan with the time reads a concatenation's earlier part first. -/
theorem runAux_append (u v : List Bool) (p : Scan × List Redundant.Digit × ℕ) :
    runAux W (u ++ v) p = runAux W v (runAux W u p) := List.foldl_append

/-- The scan with the time carries the scan with the counter. -/
theorem runAux_fst (w : List Bool) :
    ∀ p : Scan × List Redundant.Digit × ℕ,
      ((runAux W w p).1, (runAux W w p).2.1) = runTree W w (p.1, p.2.1) :=
  List.rec
    (motive := fun w ↦ ∀ p : Scan × List Redundant.Digit × ℕ,
      ((runAux W w p).1, (runAux W w p).2.1) = runTree W w (p.1, p.2.1))
    (fun _ ↦ rfl) (fun b _ ih p ↦ by rw [runAux_cons, ih, runTree_cons]) w

/-- The time of a prefix extended by one bit is the prefix's and the bit's cost
at the prefix's state and counter. -/
theorem time_take_succ (w : List Bool) (k : ℕ) (h : k < w.length) :
    time W (w.take (k + 1)) =
      time W (w.take k) + cost (scanAt W (w.take k)) w[k] (treeAt W (w.take k)) := by
  rw [List.take_succ_eq_append_getElem h, time, runAux_append, runAux_cons, runAux_nil]
  have := runAux_fst W (w.take k) (init, [], 0)
  rw [Prod.ext_iff] at this
  obtain ⟨h1, h2⟩ := this
  dsimp only at h1 h2
  rw [runTree_fst] at h1
  rw [h1, h2]
  rfl

/-- The state a completed tree leaves expects a tree or is complete. -/
theorem close_mode (c : ℕ) : (close c).mode = .term ∨ (close c).mode = .done := by
  cases c with
  | zero => exact Or.inr rfl
  | succ c => exact Or.inl rfl

/-- The counter's step at a pair bit or a bit inside a pair's code. -/
theorem treeStep_term (c w : ℕ) (d : List Bool) (b : Bool) (l : List Redundant.Digit) :
    treeStep W ⟨.term, c, w, d⟩ b l = cond b (Redundant.inc l) l := by
  cases b with
  | true => exact ite_eq_left ⟨rfl, rfl⟩
  | false =>
    rw [treeStep, ite_eq_right (by exact fun h ↦ nomatch h.2), closes,
      decide_eq_false (by exact fun h ↦ h.1 rfl)]
    rfl

/-- The counter's step at a bit inside a leaf decrements when the bit closes
the leaf. -/
theorem treeStep_of_not_term (s : Scan) (b : Bool) (l : List Redundant.Digit)
    (hm : s.mode ≠ .term) :
    treeStep W s b l =
      if (scanStep W s b).mode = .term ∨ (scanStep W s b).mode = .done then Redundant.dec l
      else l := by
  rw [treeStep, ite_eq_right (by exact fun h ↦ hm h.1), closes]
  by_cases h : (scanStep W s b).mode = .term ∨ (scanStep W s b).mode = .done
  · rw [decide_eq_true ⟨hm, h⟩, ite_eq_left rfl, ite_eq_left h]
  · rw [decide_eq_false (by exact fun h' ↦ h h'.2), ite_eq_right h]
    rfl

/-- The counter after the work a bit in the countdown carries: decremented
when the leaf closes. -/
def settleTree (d : List Bool) (l : List Redundant.Digit) : List Redundant.Digit :=
  cond (allFalse d) (Redundant.dec l) l

/-- The counter after the work a length digit carries: decremented when the
digits are complete and the leaf closes at once. -/
def settleTreeDigits (wd : ℕ) (d : List Bool) (l : List Redundant.Digit) : List Redundant.Digit :=
  if d.length = wd then settleTree (decList d) l else l

/-- The counter's step at the one of a gamma code is the counter after the
digit's work. -/
theorem treeStep_zeros_true (c : ℕ) (l : List Redundant.Digit) (wd : ℕ) :
    treeStep W ⟨.zeros, c, wd, []⟩ true l = settleTreeDigits (wd + 1) [true] l := by
  rw [treeStep_of_not_term W ⟨.zeros, c, wd, []⟩ true l (fun h ↦ nomatch h),
    scanStep_zeros_true, settleTreeDigits]
  by_cases hfull : [true].length = wd + 1
  · rw [settleDigits_of_length_eq _ _ _ hfull, ite_eq_left hfull, decList_cons_true, settleTree,
      allFalse_cons, allFalse_nil, Bool.not_false, Bool.and_true, Bool.cond_true,
      settleCount_of_allFalse _ _ _ rfl, ite_eq_left (close_mode c)]
  · rw [settleDigits_of_length_ne _ _ _ hfull, ite_eq_right hfull,
      ite_eq_right (by rintro (h | h) <;> exact nomatch h)]

/-- The counter's step at a digit of a gamma code is the counter after the
digit's work. -/
theorem treeStep_bits (c : ℕ) (l : List Redundant.Digit) (wd : ℕ) (d : List Bool) (b : Bool) :
    treeStep W ⟨.bits, c, wd, d⟩ b l = settleTreeDigits wd (b :: d) l := by
  rw [treeStep_of_not_term W ⟨.bits, c, wd, d⟩ b l (fun h ↦ nomatch h), scanStep_bits,
    settleTreeDigits]
  by_cases hfull : (b :: d).length = wd
  · rw [settleDigits_of_length_eq _ _ _ hfull, ite_eq_left hfull, settleTree]
    cases hf : allFalse (decList (b :: d)) with
    | true => rw [settleCount_of_allFalse _ _ _ hf, ite_eq_left (close_mode c), Bool.cond_true]
    | false =>
      rw [settleCount_of_not_allFalse _ _ _ hf, Bool.cond_false,
        ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
  · rw [settleDigits_of_length_ne _ _ _ hfull, ite_eq_right hfull,
      ite_eq_right (by rintro (h | h) <;> exact nomatch h)]

/-- The counter's step at a payload bit is the counter after the bit's
work. -/
theorem treeStep_count (c : ℕ) (l : List Redundant.Digit) (wd : ℕ) (d : List Bool) (b : Bool) :
    treeStep W ⟨.count, c, wd, d⟩ b l = settleTree (decList d) l := by
  rw [treeStep_of_not_term W ⟨.count, c, wd, d⟩ b l (fun h ↦ nomatch h), scanStep_count,
    settleTree]
  cases hf : allFalse (decList d) with
  | true => rw [settleCount_of_allFalse _ _ _ hf, ite_eq_left (close_mode c), Bool.cond_true]
  | false =>
    rw [settleCount_of_not_allFalse _ _ _ hf, Bool.cond_false,
      ite_eq_right (by rintro (h | h) <;> exact nomatch h)]

/-- The steps after a complete count and their potential against the state's:
the leaf closes when no payload remains, the pending count then
decremented. -/
theorem chainCost_add_pendingCount_add_potential_le (c w : ℕ) (d : List Bool)
    (l : List Redundant.Digit) (hf : allFalse d = false) :
    chainCost d + pendingCount w (decList d) l +
        potential (settleCount c w (decList d))
          (if (settleCount c w (decList d)).mode = .term ∨
              (settleCount c w (decList d)).mode = .done then Redundant.dec l else l) ≤
      potential ⟨.count, c, w, d⟩ l + 8 := by
  have hcount := count_false_decList d hf
  have htz := borrowLength_lt_length d hf
  have hdec := decCost_add_nonOnes_le l
  cases hf' : allFalse (decList d) with
  | true =>
    obtain ⟨htz0, hc⟩ := eq_of_allFalse_decList d hf hf'
    rw [settleCount_of_allFalse _ _ _ hf', ite_eq_left (close_mode c), potential_close,
      pendingCount, hf', Bool.cond_true]
    simp only [chainCost, failCost, potential]
    omega
  | false =>
    rw [settleCount_of_not_allFalse _ _ _ hf', ite_eq_right (by rintro (h | h) <;> exact nomatch h),
      pendingCount, hf', Bool.cond_false]
    simp only [chainCost, potential]
    omega

/-- A bit costs at most nine steps amortised against the potential. -/
theorem cost_add_potential_le (s : Scan) (h : Good W s) (b : Bool) (l : List Redundant.Digit) :
    cost s b l + potential (scanStep W s b) (treeStep W s b l) ≤ potential s l + 9 := by
  obtain ⟨m, c, w, d⟩ := s
  cases m <;> dsimp only [Good] at h
  · rw [treeStep_term]
    cases b with
    | true =>
      rw [scanStep_term_true, Bool.cond_true]
      have := incCost_add_nonOnes_le l
      simp only [cost, potential]
      omega
    | false =>
      rw [scanStep_term_false, Bool.cond_false]
      simp only [cost, potential]
      omega
  · obtain ⟨hd, hw⟩ := h
    subst hd
    rw [treeStep_of_not_term W ⟨.zeros, c, w, []⟩ b l (fun h ↦ nomatch h)]
    cases b with
    | false =>
      by_cases hW : W < w
      · rw [scanStep_zeros_false_of_lt W _ _ _ hW,
          ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
        simp only [cost, potential]
        omega
      · rw [scanStep_zeros_false W _ _ _ (by omega),
          ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
        simp only [cost, potential]
        omega
    | true =>
      rw [scanStep_zeros_true]
      simp only [cost]
      by_cases hw0 : w = 0
      · subst hw0
        rw [settleDigits_of_length_eq c (0 + 1) [true] rfl, pendingDigits,
          ite_eq_left (show [true].length = 0 + 1 from rfl), decList_cons_true, pendingCount,
          allFalse_cons, allFalse_nil, Bool.not_false, Bool.and_true, Bool.cond_true,
          settleCount_of_allFalse c (0 + 1) [false] rfl, ite_eq_left (close_mode c),
          potential_close]
        have := decCost_add_nonOnes_le l
        simp only [chainCost, failCost, borrowLength_cons_true, potential]
        omega
      · have hne : [true].length ≠ w + 1 := by rw [List.length_singleton]; omega
        rw [settleDigits_of_length_ne _ _ _ hne, pendingDigits, ite_eq_right hne,
          ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
        simp only [potential]
        rw [count_false_cons_true, List.count_nil]
        omega
  · obtain ⟨hlt, ⟨r, hr⟩, hw⟩ := h
    rw [treeStep_of_not_term W ⟨.bits, c, w, d⟩ b l (fun h ↦ nomatch h), scanStep_bits]
    simp only [cost]
    have hf : allFalse (b :: d) = false := by
      rw [hr, ← List.cons_append, ← Bool.not_eq_true, allFalse_iff]
      exact Nat.ne_of_gt (ofBits_append_true_pos _)
    by_cases hfull : (b :: d).length = w
    · rw [settleDigits_of_length_eq _ _ _ hfull, pendingDigits, ite_eq_left hfull]
      have := chainCost_add_pendingCount_add_potential_le c w (b :: d) l hf
      rw [List.length_cons] at hfull
      simp only [potential] at this ⊢
      cases b
      · rw [count_false_cons_false] at this
        omega
      · rw [count_false_cons_true] at this
        omega
    · rw [settleDigits_of_length_ne _ _ _ hfull, pendingDigits, ite_eq_right hfull,
        ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
      simp only [potential]
      cases b
      · rw [count_false_cons_false]
        omega
      · rw [count_false_cons_true]
        omega
  · obtain ⟨hf, hlen, hw⟩ := h
    rw [treeStep_of_not_term W ⟨.count, c, w, d⟩ b l (fun h ↦ nomatch h), scanStep_count]
    simp only [cost]
    have := chainCost_add_pendingCount_add_potential_le c w d l hf
    omega
  · obtain ⟨rfl, rfl⟩ := h
    rw [treeStep_of_not_term W ⟨.done, c, 0, []⟩ b l (fun h ↦ nomatch h), scanStep_done,
      ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
    simp only [cost, potential]
    omega
  · obtain ⟨rfl, hw⟩ := h
    rw [treeStep_of_not_term W ⟨.dead, c, w, []⟩ b l (fun h ↦ nomatch h), scanStep_dead,
      ite_eq_right (by rintro (h | h) <;> exact nomatch h)]
    simp only [cost, potential]
    omega

/-- The time of a word from a state satisfying the invariant and a counter,
with the final potential, is at most nine per bit above the initial
potential. -/
theorem time_add_potential_le (w : List Bool) :
    ∀ (s : Scan) (l : List Redundant.Digit) (n : ℕ), Good W s →
      (runAux W w (s, l, n)).2.2 +
          potential (runTree W w (s, l)).1 (runTree W w (s, l)).2 ≤
        n + 9 * w.length + potential s l :=
  List.rec
    (motive := fun w ↦ ∀ (s : Scan) (l : List Redundant.Digit) (n : ℕ), Good W s →
      (runAux W w (s, l, n)).2.2 +
          potential (runTree W w (s, l)).1 (runTree W w (s, l)).2 ≤
        n + 9 * w.length + potential s l)
    (fun _ _ _ _ ↦ by simp)
    (fun b w ih s l n hs ↦ by
      rw [runAux_cons, runTree_cons, List.length_cons]
      dsimp only
      have h1 := ih (scanStep W s b) (treeStep W s b l) (n + cost s b l) (good_scanStep W s hs b)
      have h2 := cost_add_potential_le W s hs b l
      omega) w

/-- The steps from a state satisfying the invariant to the halt are at most one
above its potential. -/
theorem endCost_le_potential (s : Scan) (l : List Redundant.Digit) (h : Good W s) :
    endCost s ≤ potential s l + 1 := by
  obtain ⟨m, c, w, d⟩ := s
  cases m
  case count =>
    dsimp only [Good] at h
    obtain ⟨hf, hlen, _⟩ := h
    have := borrowLength_lt_length d hf
    simp only [endCost, potential, chainCost]
    omega
  all_goals simp only [endCost, potential]; omega

/-- A word of {lit}`n` bits scanned at its bound is consumed and the machine
halted in at most {lit}`9 * n + 1` steps of the scan. -/
theorem time_add_endCost_le (w : List Bool) :
    time (bound w) w + endCost (scanFinal w) ≤ 9 * w.length + 1 := by
  have h1 := time_add_potential_le (bound w) w init [] 0 (good_init _)
  have h2 := endCost_le_potential (bound w) (scanFinal w) (treeAt (bound w) w) (good_scanAt _ w)
  rw [potential_init] at h1
  rw [scanFinal, scanAt] at h2 ⊢
  change (runAux (bound w) w (init, [], 0)).2.2 + endCost (scanFrom (bound w) w init) ≤
    9 * w.length + 1
  have h3 : (runTree (bound w) w (init, [])).1 = scanFrom (bound w) w init := runTree_fst _ _ _
  rw [h3] at h1
  rw [treeAt] at h2
  omega

end Cost

section Seek

/-- One digit of the ordinary binary increment, given the rest as a function
of whether a carry is pending. -/
def incStepB (b : Bool) (k : Bool → List Bool) (carry : Bool) : List Bool :=
  cond carry (cond b (false :: k true) (true :: k false)) (b :: k false)

/-- The ordinary binary increment as a function of whether a carry is
pending; a carry past the top digit becomes a new top one. -/
def incAuxB (l : List Bool) : Bool → List Bool := l.foldr incStepB fun carry ↦ cond carry [true] []

/-- The ordinary binary increment, least significant digit first. -/
def incB (l : List Bool) : List Bool := incAuxB l true

/-- Without a carry the digits pass. -/
theorem incAuxB_false (l : List Bool) : incAuxB l false = l :=
  List.rec (motive := fun l ↦ incAuxB l false = l) rfl
    (fun b _ ih ↦ by
      change b :: incAuxB _ false = b :: _
      rw [ih]) l

/-- The increment of zero. -/
@[simp] theorem incB_nil : incB [] = [true] := rfl

/-- A zero at the bottom becomes a one. -/
@[simp] theorem incB_cons_false (l : List Bool) : incB (false :: l) = true :: l := by
  change true :: incAuxB l false = _
  rw [incAuxB_false]

/-- A one at the bottom becomes a zero and the carry propagates. -/
@[simp] theorem incB_cons_true (l : List Bool) : incB (true :: l) = false :: incB l := rfl

/-- The ordinary increment is the successor's digits. -/
theorem bits_succ (n : ℕ) : (n + 1).bits = incB n.bits :=
  Nat.binaryRec' (motive := fun n ↦ (n + 1).bits = incB n.bits)
    (by rw [Nat.zero_bits, incB_nil]; exact Nat.one_bits)
    (fun b n h ih ↦ by
      cases b with
      | false =>
        rw [Nat.bits_append_bit n false h, incB_cons_false,
          show Nat.bit false n + 1 = Nat.bit true n by rw [Nat.bit_val, Nat.bit_val]; rfl]
        exact Nat.bits_append_bit n true fun _ ↦ rfl
      | true =>
        rw [Nat.bits_append_bit n true h, incB_cons_true, ← ih,
          show Nat.bit true n + 1 = Nat.bit false (n + 1) by
            rw [Nat.bit_val, Nat.bit_val, Bool.toNat_true, Bool.toNat_false]; omega]
        exact Nat.bits_append_bit (n + 1) false fun h ↦ absurd h (Nat.succ_ne_zero n)) n

/-- The length of an ordinary carry: the run of ones at the bottom. -/
def carryLengthB (l : List Bool) : ℕ := l.foldr (fun b n ↦ cond b (n + 1) 0) 0

/-- The carry stops at a zero. -/
@[simp] theorem carryLengthB_cons_false (l : List Bool) : carryLengthB (false :: l) = 0 := rfl

/-- The carry passes a one. -/
@[simp] theorem carryLengthB_cons_true (l : List Bool) :
    carryLengthB (true :: l) = carryLengthB l + 1 := rfl

/-- The ordinary carry is at most the whole list. -/
theorem carryLengthB_le_length (l : List Bool) : carryLengthB l ≤ l.length :=
  List.rec (motive := fun l ↦ carryLengthB l ≤ l.length) le_rfl
    (fun b l ih ↦ by
      rw [List.length_cons]
      cases b with
      | false => rw [carryLengthB_cons_false]; exact Nat.zero_le _
      | true => rw [carryLengthB_cons_true]; exact Nat.succ_le_succ ih) l

/-- Below the ordinary carry's length a digit is a one. -/
theorem getD_of_lt_carryLengthB (l : List Bool) :
    ∀ i, i < carryLengthB l → l.getD i false = true :=
  List.rec (motive := fun l ↦ ∀ i, i < carryLengthB l → l.getD i false = true)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun b l ih i hi ↦ by
      cases b with
      | false => rw [carryLengthB_cons_false] at hi; exact absurd hi (Nat.not_lt_zero _)
      | true =>
        cases i with
        | zero => rfl
        | succ i => rw [carryLengthB_cons_true] at hi; exact ih i (by omega)) l

/-- At the ordinary carry's length, short of the top, the digit is a zero. -/
theorem getD_carryLengthB (l : List Bool) (h : carryLengthB l < l.length) :
    l.getD (carryLengthB l) false = false :=
  List.rec (motive := fun l ↦ carryLengthB l < l.length → l.getD (carryLengthB l) false = false)
    (fun h ↦ absurd h (Nat.lt_irrefl 0))
    (fun b l ih h ↦ by
      cases b with
      | false => rfl
      | true =>
        rw [carryLengthB_cons_true, List.length_cons] at h
        rw [carryLengthB_cons_true, List.getD_cons_succ]
        exact ih (by omega)) l h

/-- The ordinary increment lengthens the digits exactly when the carry runs
through every digit. -/
theorem length_incB (l : List Bool) : (incB l).length = max l.length (carryLengthB l + 1) :=
  List.rec (motive := fun l ↦ (incB l).length = max l.length (carryLengthB l + 1)) rfl
    (fun b l ih ↦ by
      rw [List.length_cons]
      cases b with
      | false => rw [incB_cons_false, carryLengthB_cons_false, List.length_cons]; omega
      | true => rw [incB_cons_true, carryLengthB_cons_true, List.length_cons, ih]; omega) l

/-- The ordinary increment turns the digits below the carry's length into
zeros. -/
theorem getD_incB_of_lt (l : List Bool) :
    ∀ i, i < carryLengthB l → (incB l).getD i false = false :=
  List.rec (motive := fun l ↦ ∀ i, i < carryLengthB l → (incB l).getD i false = false)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun b l ih i hi ↦ by
      cases b with
      | false => rw [carryLengthB_cons_false] at hi; exact absurd hi (Nat.not_lt_zero _)
      | true =>
        rw [incB_cons_true]
        cases i with
        | zero => rfl
        | succ i => rw [carryLengthB_cons_true] at hi; exact ih i (by omega)) l

/-- The ordinary increment raises the digit at the carry's length. -/
theorem getD_incB_carryLengthB (l : List Bool) : (incB l).getD (carryLengthB l) false = true :=
  List.rec (motive := fun l ↦ (incB l).getD (carryLengthB l) false = true) rfl
    (fun b l ih ↦ by
      cases b with
      | false => rfl
      | true => rw [incB_cons_true, carryLengthB_cons_true, List.getD_cons_succ, ih]) l

/-- The ordinary increment leaves the digits above the carry's length. -/
theorem getD_incB_of_gt (l : List Bool) :
    ∀ i, carryLengthB l < i → (incB l).getD i false = l.getD i false :=
  List.rec (motive := fun l ↦ ∀ i, carryLengthB l < i → (incB l).getD i false = l.getD i false)
    (fun i hi ↦ by
      rw [incB_nil]
      cases i with
      | zero => exact absurd hi (Nat.lt_irrefl 0)
      | succ i => rfl)
    (fun b l ih i hi ↦ by
      cases b with
      | false =>
        rw [incB_cons_false]
        cases i with
        | zero => rw [carryLengthB_cons_false] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i => rfl
      | true =>
        rw [incB_cons_true]
        cases i with
        | zero => rw [carryLengthB_cons_true] at hi; exact absurd hi (Nat.not_lt_zero _)
        | succ i => rw [carryLengthB_cons_true] at hi; exact ih i (by omega)) l

/-- A carry turns as many ones into zeros as it passes, one digit becoming a
one. -/
theorem count_true_incB_add_carryLengthB_le (l : List Bool) :
    (incB l).count true + carryLengthB l ≤ l.count true + 1 :=
  List.rec (motive := fun l ↦ (incB l).count true + carryLengthB l ≤ l.count true + 1) (by decide)
    (fun b l ih ↦ by
      cases b with
      | false =>
        rw [incB_cons_false, carryLengthB_cons_false, count_true_cons_true, count_true_cons_false]
      | true =>
        rw [incB_cons_true, carryLengthB_cons_true, count_true_cons_true, count_true_cons_false]
        omega) l

/-- The steps the counting pass costs at one input bit: one when the count's
lowest digit is a zero, else out through the ones, the raising step, back to
the base marker and the step consuming the bit. -/
def seekIncCost (i : ℕ) : ℕ :=
  if carryLengthB i.bits = 0 then 1 else 2 * carryLengthB i.bits + 2

/-- The steps the counting pass costs over the first {lit}`n` input bits. -/
def seekTime : ℕ → ℕ := Nat.rec 0 fun i acc ↦ acc + seekIncCost i

/-- The counting pass's steps, with twice the ones of the count, are at most
four per bit. -/
theorem seekTime_add_le (n : ℕ) : seekTime n + 2 * n.bits.count true ≤ 4 * n :=
  Nat.rec (motive := fun n ↦ seekTime n + 2 * n.bits.count true ≤ 4 * n) (by decide)
    (fun i ih ↦ by
      have := count_true_incB_add_carryLengthB_le i.bits
      change seekTime i + seekIncCost i + 2 * (i + 1).bits.count true ≤ 4 * (i + 1)
      rw [bits_succ, seekIncCost]
      split_ifs with h <;> omega) n

/-- The counting pass costs at most four steps per input bit. -/
theorem seekTime_le (n : ℕ) : seekTime n ≤ 4 * n :=
  le_trans (Nat.le_add_right _ _) (seekTime_add_le n)

/-- The steps from the initial configuration to the halt: the first pass, the
scan, and the steps from the input's end. -/
def totalTime (w : List Bool) : ℕ :=
  seekTime w.length + w.length + 3 + time (bound w) w + endCost (scanFinal w)

/-- The halting time is at most fourteen per bit and four. -/
theorem totalTime_le (w : List Bool) : totalTime w ≤ 14 * w.length + 4 := by
  have h1 := seekTime_le w.length
  have h2 := time_add_endCost_le w
  rw [totalTime]
  omega

end Seek

end Geb.BitTreeScanner
