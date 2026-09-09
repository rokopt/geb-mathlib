/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineModel

set_option doc.verso true

/-!
# Space and transition accounting for the Elias scanner

The scalar phase and its two binary words advance together. Their lengths grow by at most
one per input bit, bounding both work space and the cost of each complete bit transition.

## Main definitions

* {lit}`account` records scalar state and binary words at each input boundary.
* {lit}`runCost` sums the machine's transition costs.

## Tags

Elias delta code, complexity, binary counter
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

/-- Binary-word updates implement the scalar phase update. -/
theorem words_step (s : Scanner.State) (bs cs : List Bool) (b : Bool)
    (ha : Scanner.Active s) (hw : Words s.1 bs cs) :
    Words (Scanner.step s b).1 (nextWords s.1 bs cs b).1 (nextWords s.1 bs cs b).2 := by
  rcases s with ⟨m, n⟩
  cases m with
  | tree => cases b with
    | false => exact ⟨rfl, rfl⟩
    | true => exact hw
  | zeros z =>
    cases b with
    | false => exact hw
    | true =>
      by_cases hz : z = 0
      · simp only [Scanner.step, nextWords, hz, ↓reduceIte]
        unfold Scanner.finish
        split <;> exact ⟨rfl, rfl⟩
      · simp only [Scanner.step, nextWords, hz, ↓reduceIte, Words]
        exact ⟨rfl, hw.2⟩
  | size r v =>
    obtain ⟨hn, hr, hv⟩ := ha
    obtain ⟨hb, hc⟩ := hw
    have hp : 0 < Counter.value (b :: bs) := by
      rw [Counter.value_cons, hb]
      omega
    by_cases he : r = 1
    · simp only [Scanner.step, nextWords, he, ↓reduceIte, Words,
        Counter.value_decrement _ hp, Counter.value_cons, hb, hc, Nat.bit_val]
      exact ⟨trivial, rfl⟩
    · simp only [Scanner.step, nextWords, he, ↓reduceIte, Words, Counter.value_cons,
        hb, Nat.bit_val]
      exact ⟨trivial, hc⟩
  | length r v =>
    obtain ⟨hn, hr, hv⟩ := ha
    obtain ⟨hb, hc⟩ := hw
    have hp : 0 < Counter.value (b :: cs) := by
      rw [Counter.value_cons, hc]
      omega
    have hbs : 0 < Counter.value bs := by rw [hb]; exact hr
    by_cases he : r = 1
    · simp only [Scanner.step, nextWords, he, ↓reduceIte, Words,
        Counter.value_decrement _ hbs, Counter.value_decrement _ hp,
        Counter.value_cons, hb, hc, Nat.bit_val]
      exact ⟨trivial, trivial⟩
    · simp only [Scanner.step, nextWords, he, ↓reduceIte, Words,
        Counter.value_decrement _ hbs, Counter.value_cons, hb, hc, Nat.bit_val]
      exact ⟨trivial, trivial⟩
  | payload r =>
    obtain ⟨hn, hr⟩ := ha
    obtain ⟨hb, hc⟩ := hw
    by_cases he : r = 1
    · simp only [Scanner.step, nextWords, he, ↓reduceIte]
      unfold Scanner.finish
      split <;> exact ⟨rfl, rfl⟩
    · have hp : 0 < Counter.value cs := by rw [hc]; exact hr
      simp only [Scanner.step, nextWords, he, ↓reduceIte, Words,
        Counter.value_decrement _ hp, hc]
      exact ⟨hb, trivial⟩
  | done => exact hw
  | dead => exact hw

/-- A scalar state paired with its two finite binary words. -/
abbrev Account := Scanner.State × (List Bool × List Bool)

/-- One pending root and initially empty binary fields. -/
def initialAccount : Account := ((.tree, 1), [], [])

/-- Advance the scalar state and both binary fields by one input bit. -/
def accountStep (s : Account) (b : Bool) : Account :=
  (Scanner.step s.1 b, nextWords s.1.1 s.2.1 s.2.2 b)

/-- State and fields after a finite input prefix. -/
def account (w : List Bool) : Account := w.foldl accountStep initialAccount

/-- The two descriptions agree at every boundary. -/
def AccountValid (s : Account) : Prop := Scanner.Active s.1 ∧ Words s.1.1 s.2.1 s.2.2

/-- A complete bit transition preserves scalar and binary-word invariants. -/
theorem accountStep_valid (s : Account) (b : Bool) (h : AccountValid s) :
    AccountValid (accountStep s b) :=
  ⟨Scanner.active_step s.1 b h.1, words_step s.1 s.2.1 s.2.2 b h.1 h.2⟩

/-- The invariant is preserved across any input suffix. -/
theorem account_foldl_valid (w : List Bool) : ∀ s, AccountValid s →
    AccountValid (w.foldl accountStep s) :=
  List.rec (fun _ h ↦ h) (fun b _ ih s h ↦ ih _ (accountStep_valid s b h)) w

/-- Projection commutes with scanning any suffix. -/
theorem account_foldl_project (w : List Bool) : ∀ s,
    (w.foldl accountStep s).1 = w.foldl Scanner.step s.1 :=
  List.rec (fun _ ↦ rfl) (fun b _ ih s ↦ ih (accountStep s b)) w

/-- The scalar account component is the streaming scanner state. -/
theorem account_project (w : List Bool) : (account w).1 = Scanner.scan w :=
  account_foldl_project w initialAccount

/-- The account invariant holds after every input prefix. -/
theorem account_valid (w : List Bool) : AccountValid (account w) :=
  account_foldl_valid w initialAccount ⟨show 0 < 1 by decide, rfl, rfl⟩

/-- The scalar component remains active or terminal. -/
theorem account_active (w : List Bool) : Scanner.Active (account w).1 :=
  (account_valid w).1

/-- Both finite words represent their scalar phase values. -/
theorem account_words (w : List Bool) :
    Words (account w).1.1 (account w).2.1 (account w).2.2 := (account_valid w).2

/-- Each binary word grows by at most one per input bit. -/
theorem nextWords_lengths_le (m : Scanner.Mode) (bs cs : List Bool) (b : Bool) :
    (nextWords m bs cs b).1.length ≤ bs.length + 1 ∧
      (nextWords m bs cs b).2.length ≤ cs.length + 1 := by
  cases m <;> cases b <;> simp only [nextWords] <;>
    first | (constructor <;> omega) |
      (split <;> constructor <;> simp only [List.length_nil, List.length_cons,
        Counter.length_decrement] <;> omega) |
      (constructor <;> simp only [List.length_nil, List.length_cons] <;> omega)

/-- The unary header counter grows by at most one per input bit. -/
theorem step_zeros_le (s : Scanner.State) (b : Bool) :
    zeroCount (Scanner.step s b).1 ≤ zeroCount s.1 + 1 := by
  rcases s with ⟨m, n⟩
  cases m <;> cases b <;> simp only [Scanner.step] <;>
    first | (simp only [zeroCount]; omega) |
      (split <;> first | (simp only [zeroCount]; omega) |
        (unfold Scanner.finish; split <;> simp only [zeroCount] <;> omega))

/-- Any suffix adds at most its length to both word widths and the unary header counter. -/
theorem account_foldl_bounds (w : List Bool) : ∀ s,
    (w.foldl accountStep s).2.1.length ≤ s.2.1.length + w.length ∧
    (w.foldl accountStep s).2.2.length ≤ s.2.2.length + w.length ∧
    zeroCount (w.foldl accountStep s).1.1 ≤ zeroCount s.1.1 + w.length :=
  List.rec (fun s ↦ ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun b bs ih s ↦ by
      obtain ⟨hb, hc, hz⟩ := ih (accountStep s b)
      obtain ⟨hbs, hcs⟩ := nextWords_lengths_le s.1.1 s.2.1 s.2.2 b
      have hzs := step_zeros_le s.1 b
      simp only [List.foldl_cons, List.length_cons]
      change _ ≤ _ at hb hc hz
      dsimp only [accountStep] at hb hc hz ⊢
      exact ⟨by omega, by omega, by omega⟩) w

/-- Each binary field uses at most the input length. -/
theorem account_lengths_le (w : List Bool) :
    (account w).2.1.length ≤ w.length ∧ (account w).2.2.length ≤ w.length := by
  obtain ⟨hb, hc, _⟩ := account_foldl_bounds w initialAccount
  simpa only [account, initialAccount, List.length_nil, Nat.zero_add] using And.intro hb hc

/-- The unary header counter is bounded by the input length. -/
theorem account_zeros_le (w : List Bool) : zeroCount (account w).1.1 ≤ w.length := by
  simpa only [account, initialAccount, zeroCount, Nat.zero_add] using
    (account_foldl_bounds w initialAccount).2.2

/-- Pending subtrees use at most one plus the input length. -/
theorem account_pending_le (w : List Bool) : (account w).1.2 ≤ w.length + 1 := by
  rw [account_project]
  exact Scanner.scan_pending_le w

/-- Appending one bit advances the account once. -/
theorem account_append (w : List Bool) (b : Bool) :
    account (w ++ [b]) = accountStep (account w) b := by
  simp only [account, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Machine time for one complete input transition. -/
def macroCost (s : Account) (b : Bool) : ℕ := bitCost s.1.1 s.2.1 s.2.2 b

/-- Advance the account while accumulating machine time. -/
def costStep (s : Account × ℕ) (b : Bool) : Account × ℕ :=
  (accountStep s.1 b, s.2 + macroCost s.1 b)

/-- Time accounting leaves the account projection unchanged. -/
theorem cost_foldl_fst (w : List Bool) : ∀ s c,
    (w.foldl costStep (s, c)).1 = w.foldl accountStep s :=
  List.rec (fun _ _ ↦ rfl) (fun b _ ih s c ↦ ih (accountStep s b) (c + macroCost s b)) w

/-- Total transition time before the final end-marker decision. -/
def runCost (w : List Bool) : ℕ := (w.foldl costStep (initialAccount, 0)).2

/-- Appending one input bit adds its exact macro cost. -/
theorem runCost_append (w : List Bool) (b : Bool) :
    runCost (w ++ [b]) = runCost w + macroCost (account w) b := by
  simp only [runCost, List.foldl_append, List.foldl_cons, List.foldl_nil, costStep,
    cost_foldl_fst, account]

/-- A width bound gives a uniform linear bound for one macro transition. -/
theorem bitCost_le (m : Scanner.Mode) (bs cs : List Bool) (b : Bool) (width : ℕ)
    (hb : bs.length ≤ width) (hc : cs.length ≤ width) :
    bitCost m bs cs b ≤ 5 * width + 16 := by
  cases m <;> cases b <;> simp only [bitCost] <;>
    first | omega | (split <;> omega)

/-- Every transition cost is positive. -/
theorem macroCost_pos (s : Account) (b : Bool) : 0 < macroCost s b := by
  rcases s with ⟨⟨m, n⟩, bs, cs⟩
  cases m <;> cases b <;> simp only [macroCost, bitCost] <;>
    first | omega | (split <;> omega)

/-- The total macro time is bounded by a quadratic polynomial in input length. -/
theorem runCost_le (w : List Bool) : runCost w ≤ 5 * w.length ^ 2 + 16 * w.length := by
  refine List.reverseRecOn w ?_ ?_
  · exact Nat.le_refl 0
  · intro bs b ih
    obtain ⟨hb, hc⟩ := account_lengths_le bs
    have hcost := bitCost_le (account bs).1.1 (account bs).2.1 (account bs).2.2
      b bs.length hb hc
    change macroCost (account bs) b ≤ _ at hcost
    rw [runCost_append]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    rw [Nat.pow_two] at ih
    omega

/-- The account at the next prefix is a single update of the current account. -/
theorem account_take_succ (w : List Bool) (t : ℕ) (h : t < w.length) :
    account (w.take (t + 1)) = accountStep (account (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, account_append]

/-- The next prefix adds exactly one complete transition cost. -/
theorem runCost_take_succ (w : List Bool) (t : ℕ) (h : t < w.length) :
    runCost (w.take (t + 1)) =
      runCost (w.take t) + macroCost (account (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, runCost_append]

/-- Binary fields at any prefix fit within the length of the whole input. -/
theorem prefix_lengths_le (w : List Bool) (t : ℕ) :
    (account (w.take t)).2.1.length ≤ w.length ∧
      (account (w.take t)).2.2.length ≤ w.length := by
  obtain ⟨hb, hc⟩ := account_lengths_le (w.take t)
  have ht : (w.take t).length ≤ w.length := by simp only [List.length_take]; omega
  exact ⟨Nat.le_trans hb ht, Nat.le_trans hc ht⟩

end Geb.BitTree.Elias.Machine
