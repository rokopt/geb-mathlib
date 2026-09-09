/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Scan

set_option doc.verso true

/-!
# The scan's invariant and the machine's cost per bit

The states the scan reaches from its initial state satisfy an invariant,
{lit}`Geb.BitTreeScanner.Good`, which the machine's closed-form configuration
needs: the digit cells a leaf claims hold its digits, the countdown holds a
positive count, and outside a leaf nothing is held. Against that invariant the
module states the number of machine steps each input bit costs, {lit}`Geb.BitTreeScanner.cost`,
and bounds the total by a potential: a bit costs at most five steps amortised,
so the machine consumes a word of {lit}`n` bits in at most {lit}`5 * n` steps.

A bit costs one step unless it is a payload bit, whose countdown borrows
through the zeros below the lowest one of the remaining count, and each
leaf's length digits and last payload bit carry the work the machine does
before the next bit: the one decrement that turns the length read into the
payload remaining, and the failed decrement that detects the payload's end
and clears the digit cells. The potential is the number of zero digits,
weighted, plus the width of the digit cells, weighted: a borrow turns zeros
into ones and a clearance empties the cells, so each pays for itself.

## Main definitions

* {lit}`Geb.BitTreeScanner.borrowLength` — the number of zeros below the lowest one of a digit
  list, the length of a borrow.
* {lit}`Geb.BitTreeScanner.Good` — the invariant.
* {lit}`Geb.BitTreeScanner.chainCost`, {lit}`Geb.BitTreeScanner.failCost`,
  {lit}`Geb.BitTreeScanner.pendingCount`, {lit}`Geb.BitTreeScanner.pendingDigits`,
  {lit}`Geb.BitTreeScanner.cost` — the steps a bit costs.
* {lit}`Geb.BitTreeScanner.endCost` — the steps from the state at the input's end to
  the halt.
* {lit}`Geb.BitTreeScanner.runAux`, {lit}`Geb.BitTreeScanner.time` — the steps a word
  costs.
* {lit}`Geb.BitTreeScanner.potential` — the potential.

## Main statements

* {lit}`Geb.BitTreeScanner.good_init`, {lit}`Geb.BitTreeScanner.good_scanStep`,
  {lit}`Geb.BitTreeScanner.good_scanFinal` — the invariant holds initially and is
  preserved.
* {lit}`Geb.BitTreeScanner.count_false_decList`, {lit}`Geb.BitTreeScanner.borrowLength_le_length`,
  {lit}`Geb.BitTreeScanner.borrowLength_lt_length`,
  {lit}`Geb.BitTreeScanner.eq_of_allFalse_decList` — the borrow's effect on the
  zero digits, its length, and the shape of a count of one.
* {lit}`Geb.BitTreeScanner.getD_of_lt_borrowLength`,
  {lit}`Geb.BitTreeScanner.getD_borrowLength`, {lit}`Geb.BitTreeScanner.getD_decList_of_lt`,
  {lit}`Geb.BitTreeScanner.getD_decList_borrowLength`,
  {lit}`Geb.BitTreeScanner.getD_decList_of_gt`,
  {lit}`Geb.BitTreeScanner.borrowLength_of_allFalse` — the digits below, at and above
  the borrow's length, before and after the decrement.
* {lit}`Geb.BitTreeScanner.cost_add_potential_le` — a bit costs at most five steps
  amortised against the potential.
* {lit}`Geb.BitTreeScanner.time_take_succ` — the time of a prefix extended by one
  bit.
* {lit}`Geb.BitTreeScanner.time_add_potential_le`,
  {lit}`Geb.BitTreeScanner.time_add_endCost_le` — the time bound against the
  potential, and with the steps to the halt.

## Implementation notes

{lit}`Good` is a {lit}`Prop`-valued match on the mode, so that at a literal
mode it unfolds to the conjunction that mode carries. {lit}`cost` matches on
the mode and the bit as {name}`Geb.BitTreeScanner.scanStep` does, so the two case
analyses align in {lit}`cost_add_potential_le`.

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

/-- The invariant of the states the scan reaches: outside a leaf nothing is
held; reading the zeros nothing is held yet; reading the digits, at least one
and fewer than the width are held, the most significant a one; in the
countdown the digits fill the width and denote a positive count. -/
def Good (s : Scan) : Prop :=
  match s.mode with
  | .term | .done | .dead => s.width = 0 ∧ s.digits = []
  | .zeros => s.digits = []
  | .bits => s.digits.length < s.width ∧ ∃ r, s.digits = r ++ [true]
  | .count => allFalse s.digits = false ∧ s.digits.length = s.width

/-- The initial state satisfies the invariant. -/
theorem good_init : Good init := ⟨rfl, rfl⟩

/-- The state a completed tree leaves satisfies the invariant. -/
theorem good_close (c : ℕ) : Good (close c) := by
  cases c <;> exact ⟨rfl, rfl⟩

/-- The state after a payload bit satisfies the invariant, the digits filling
the width. -/
theorem good_settleCount (c w : ℕ) (d : List Bool) (hlen : d.length = w) :
    Good (settleCount c w d) := by
  cases hf : allFalse d with
  | true => rw [settleCount_of_allFalse _ _ _ hf]; exact good_close c
  | false => rw [settleCount_of_not_allFalse _ _ _ hf]; exact ⟨hf, hlen⟩

/-- The state after a length digit satisfies the invariant, the digits ending
in a one and not exceeding the width. -/
theorem good_settleDigits (c w : ℕ) (d : List Bool) (hr : ∃ r, d = r ++ [true])
    (hle : d.length ≤ w) : Good (settleDigits c w d) := by
  by_cases hfull : d.length = w
  · rw [settleDigits_of_length_eq _ _ _ hfull]
    exact good_settleCount c w _ (by rw [length_decList, hfull])
  · rw [settleDigits_of_length_ne _ _ _ hfull]
    obtain ⟨r, hr⟩ := hr
    change d.length < w ∧ ∃ r, d = r ++ [true]
    exact ⟨by omega, r, hr⟩

/-- The scan preserves the invariant. -/
theorem good_scanStep (s : Scan) (h : Good s) (b : Bool) : Good (scanStep s b) := by
  obtain ⟨m, c, w, d⟩ := s
  cases m <;> dsimp only [Good] at h
  · cases b with
    | true => rw [scanStep_term_true]; exact ⟨rfl, rfl⟩
    | false => rw [scanStep_term_false]; exact rfl
  · cases b with
    | false => rw [scanStep_zeros_false]; exact rfl
    | true =>
      rw [scanStep_zeros_true]
      exact good_settleDigits c (w + 1) [true] ⟨[], rfl⟩ (by rw [List.length_singleton]; omega)
  · obtain ⟨hlt, r, hr⟩ := h
    rw [scanStep_bits]
    exact good_settleDigits c w (b :: d) ⟨b :: r, by rw [hr, List.cons_append]⟩
      (by rw [List.length_cons]; exact hlt)
  · obtain ⟨_, hlen⟩ := h
    rw [scanStep_count]
    exact good_settleCount c w _ (by rw [length_decList, hlen])
  · rw [scanStep_done]; exact ⟨rfl, rfl⟩
  · rw [scanStep_dead]; exact h

/-- The scan of any word from a state satisfying the invariant satisfies it. -/
theorem good_scanFrom (w : List Bool) : ∀ s, Good s → Good (scanFrom w s) :=
  List.rec (motive := fun w ↦ ∀ s, Good s → Good (scanFrom w s)) (fun _ h ↦ h)
    (fun b _ ih s h ↦ by rw [scanFrom_cons]; exact ih _ (good_scanStep s h b)) w

/-- The scan of any word satisfies the invariant. -/
theorem good_scanFinal (w : List Bool) : Good (scanFinal w) := good_scanFrom w init good_init

end Invariant

section Cost

/-- The steps a decrement costs: out along the borrow, back, and the step at
the base marker. -/
def chainCost (d : List Bool) : ℕ := 2 * borrowLength d + 2

/-- The steps a failed decrement costs at a width: out across the cells, back
erasing them, and the step at the base marker leaving the leaf. -/
def failCost (w : ℕ) : ℕ := 2 * w + 2

/-- The steps after a payload bit before the next bit: the failed decrement
that detects the payload's end, when no payload remains. -/
def pendingCount (w : ℕ) (d : List Bool) : ℕ := cond (allFalse d) (failCost w) 0

/-- The steps after a length digit before the next bit: when the digits fill
the width, the step to the lowest digit, the decrement that turns the length
read into the payload remaining, and what follows a payload bit. -/
def pendingDigits (w : ℕ) (d : List Bool) : ℕ :=
  if d.length = w then 1 + chainCost d + pendingCount w (decList d) else 0

/-- The steps a bit costs at a state satisfying the invariant, including the
steps before the next bit. -/
def cost (s : Scan) (b : Bool) : ℕ :=
  match s.mode, b with
  | .term, _ => 1
  | .zeros, false => 1
  | .zeros, true => 1 + pendingDigits (s.width + 1) [true]
  | .bits, _ => 1 + pendingDigits s.width (b :: s.digits)
  | .count, _ => chainCost s.digits + pendingCount s.width (decList s.digits)
  | .done, _ => 1
  | .dead, _ => 1

/-- The steps from the state at the input's end to the halt: one, the emitting
step, except in the countdown, where the decrement runs to the base marker
before the step there finds the input ended. -/
def endCost (s : Scan) : ℕ :=
  match s.mode with
  | .count => chainCost s.digits
  | _ => 1

/-- The scan with its time: the state and the steps so far. -/
def runAux (w : List Bool) (p : Scan × ℕ) : Scan × ℕ :=
  w.foldl (fun p b ↦ (scanStep p.1 b, p.2 + cost p.1 b)) p

/-- The steps a word costs from the initial state. -/
def time (w : List Bool) : ℕ := (runAux w (init, 0)).2

/-- The potential: weighted zero digits and weighted width, which a borrow and
a clearance draw down. -/
def potential (s : Scan) : ℕ :=
  match s.mode with
  | .zeros => 2 * s.width + 4
  | .bits => 2 * s.digits.count false + 2 * s.width + 6
  | .count => 2 * s.digits.count false + 2 * s.width + 2
  | _ => 0

/-- The potential of the state a completed tree leaves is zero. -/
theorem potential_close (c : ℕ) : potential (close c) = 0 := by cases c <;> rfl

/-- The potential of the initial state is zero. -/
theorem potential_init : potential init = 0 := rfl

/-- The scan with its time reads the empty word as nothing. -/
@[simp] theorem runAux_nil (p : Scan × ℕ) : runAux [] p = p := rfl

/-- The scan with its time reads the head bit first. -/
@[simp] theorem runAux_cons (b : Bool) (w : List Bool) (p : Scan × ℕ) :
    runAux (b :: w) p = runAux w (scanStep p.1 b, p.2 + cost p.1 b) := rfl

/-- The scan with its time reads a concatenation's earlier part first. -/
theorem runAux_append (u v : List Bool) (p : Scan × ℕ) :
    runAux (u ++ v) p = runAux v (runAux u p) := List.foldl_append

/-- The scan with its time carries the scan. -/
theorem runAux_fst (w : List Bool) : ∀ p : Scan × ℕ, (runAux w p).1 = scanFrom w p.1 :=
  List.rec (motive := fun w ↦ ∀ p : Scan × ℕ, (runAux w p).1 = scanFrom w p.1) (fun _ ↦ rfl)
    (fun b _ ih p ↦ by rw [runAux_cons, ih, scanFrom_cons]) w

/-- The time of a prefix extended by one bit is the prefix's and the bit's cost
at the prefix's state. -/
theorem time_take_succ (w : List Bool) (k : ℕ) (h : k < w.length) :
    time (w.take (k + 1)) = time (w.take k) + cost (scanFinal (w.take k)) w[k] := by
  rw [List.take_succ_eq_append_getElem h, time, runAux_append, runAux_cons, runAux_nil, runAux_fst]
  rfl

/-- The bit after a payload bit or a complete length: the cost of the step and
what follows, against the potential, at a count. -/
theorem chainCost_add_pendingCount_add_potential_le (c w : ℕ) (d : List Bool)
    (hf : allFalse d = false) :
    chainCost d + pendingCount w (decList d) + potential (settleCount c w (decList d)) ≤
      4 + potential ⟨.count, c, w, d⟩ := by
  have hcount := count_false_decList d hf
  have htz := borrowLength_lt_length d hf
  cases hf' : allFalse (decList d) with
  | true =>
    obtain ⟨htz0, hc⟩ := eq_of_allFalse_decList d hf hf'
    rw [settleCount_of_allFalse _ _ _ hf', potential_close, pendingCount, hf']
    simp only [chainCost, failCost, potential, Bool.cond_true]
    omega
  | false =>
    rw [settleCount_of_not_allFalse _ _ _ hf', pendingCount, hf']
    simp only [chainCost, potential, Bool.cond_false]
    omega

/-- A bit costs at most five steps amortised against the potential. -/
theorem cost_add_potential_le (s : Scan) (h : Good s) (b : Bool) :
    cost s b + potential (scanStep s b) ≤ 5 + potential s := by
  obtain ⟨m, c, w, d⟩ := s
  cases m <;> dsimp only [Good] at h
  · cases b with
    | true => rw [scanStep_term_true]; simp [cost, potential]
    | false => rw [scanStep_term_false]; simp [cost, potential]
  · subst h
    cases b with
    | false => rw [scanStep_zeros_false]; simp only [cost, potential]; omega
    | true =>
      rw [scanStep_zeros_true]
      simp only [cost]
      by_cases hw : w = 0
      · subst hw
        rw [settleDigits_of_length_eq c (0 + 1) [true] rfl, decList_cons_true,
          settleCount_of_allFalse c (0 + 1) [false] rfl, potential_close]
        change 1 + pendingDigits (0 + 1) [true] + 0 ≤ 5 + 4
        decide
      · rw [settleDigits_of_length_ne _ _ _ (by rw [List.length_singleton]; omega), pendingDigits,
          ite_eq_right (by rw [List.length_singleton]; omega)]
        simp only [potential]
        rw [count_false_cons_true, List.count_nil]
        omega
  · obtain ⟨hlt, r, hr⟩ := h
    rw [scanStep_bits]
    simp only [cost]
    have hf : allFalse (b :: d) = false := by
      rw [hr, ← List.cons_append, ← Bool.not_eq_true, allFalse_iff]
      exact Nat.ne_of_gt (ofBits_append_true_pos _)
    by_cases hfull : (b :: d).length = w
    · rw [settleDigits_of_length_eq _ _ _ hfull, pendingDigits, ite_eq_left hfull]
      have := chainCost_add_pendingCount_add_potential_le c w (b :: d) hf
      rw [List.length_cons] at hfull
      simp only [potential] at this ⊢
      cases b
      · rw [count_false_cons_false] at this
        omega
      · rw [count_false_cons_true] at this
        omega
    · rw [settleDigits_of_length_ne _ _ _ hfull, pendingDigits, ite_eq_right hfull]
      simp only [potential]
      cases b
      · rw [count_false_cons_false]
        omega
      · rw [count_false_cons_true]
        omega
  · obtain ⟨hf, hlen⟩ := h
    rw [scanStep_count]
    simp only [cost]
    have := chainCost_add_pendingCount_add_potential_le c w d hf
    omega
  · rw [scanStep_done]; simp [cost, potential]
  · rw [scanStep_dead]; simp [cost, potential]

/-- The time of a word from a state satisfying the invariant, with the final
potential, is at most five per bit above the initial potential. -/
theorem time_add_potential_le (w : List Bool) :
    ∀ (s : Scan) (n : ℕ), Good s →
      (runAux w (s, n)).2 + potential (scanFrom w s) ≤ n + 5 * w.length + potential s :=
  List.rec
    (motive := fun w ↦ ∀ (s : Scan) (n : ℕ), Good s →
      (runAux w (s, n)).2 + potential (scanFrom w s) ≤ n + 5 * w.length + potential s)
    (fun _ _ _ ↦ by simp)
    (fun b w ih s n hs ↦ by
      rw [runAux_cons, scanFrom_cons, List.length_cons]
      dsimp only
      have h1 := ih (scanStep s b) (n + cost s b) (good_scanStep s hs b)
      have h2 := cost_add_potential_le s hs b
      omega) w

/-- The steps from a state satisfying the invariant to the halt are at most one
above its potential. -/
theorem endCost_le_potential (s : Scan) (h : Good s) : endCost s ≤ potential s + 1 := by
  obtain ⟨m, c, w, d⟩ := s
  cases m
  case count =>
    dsimp only [Good] at h
    obtain ⟨hf, hlen⟩ := h
    have := borrowLength_lt_length d hf
    simp only [endCost, potential, chainCost]
    omega
  all_goals simp only [endCost, potential]; omega

/-- A word of {lit}`n` bits is consumed and the machine halted in at most
{lit}`5 * n + 1` steps. -/
theorem time_add_endCost_le (w : List Bool) :
    time w + endCost (scanFinal w) ≤ 5 * w.length + 1 := by
  have h1 := time_add_potential_le w init 0 good_init
  have h2 := endCost_le_potential (scanFinal w) (good_scanFinal w)
  rw [potential_init] at h1
  rw [scanFinal] at h2 ⊢
  change (runAux w (init, 0)).2 + endCost (scanFrom w init) ≤ 5 * w.length + 1
  omega

end Cost

end Geb.BitTreeScanner
