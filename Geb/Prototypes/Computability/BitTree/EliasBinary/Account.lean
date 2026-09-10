/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Need
public import Geb.Prototypes.Computability.BitTree.Counter
public import Mathlib.Data.List.Induction

set_option doc.verso true

/-!
# The account of the binary-counter recognizer

The machine's registers are determined by the scalar scanner state, the two monotone pending
counters, and the value of the length register. The account advances as the scanner does,
except that it abandons a header whose zero run or length field outgrows the binary size of
the forks counter. Since the forks counter exceeds the input length after the first pass,
such a header could never be completed, so the decision is unchanged.

## Main definitions

* {lit}`Account` holds the scanner state, both pending counters, and the length register.
* {lit}`capped` tests the two width caps.
* {lit}`accountStep` advances the account by one input bit.
* {lit}`account` is the account after a prefix, for an input of the given length.

## Main statements

* {lit}`account_valid` maintains the register invariants.
* {lit}`account_done_iff` identifies acceptance with the streaming scanner's decision.

## Tags

Elias delta code, binary counter, recognizer, invariant
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Geb.BitTree.Elias.Scanner

/-- The scanner state, one plus the forks, the completed leaves, and the length register. -/
@[ext] structure Account where
  /-- The possibly abandoned scalar scanner state. -/
  state : State
  /-- One plus the number of forks, including the first-pass count. -/
  forks : ℕ
  /-- The number of completed leaves, including the first-pass count. -/
  leaves : ℕ
  /-- One plus the payload length, during a payload. -/
  total : ℕ
  deriving DecidableEq, Repr

/-- The zero run or the length field would exceed the forks counter's width. -/
def capped (a : Account) (b : Bool) : Bool :=
  match a.state with
  | (.zeros z, _) => !b && decide (a.forks.size ≤ z)
  | (.length _ v, _) => decide (a.forks.size ≤ v.size - 1)
  | _ => false

/-- The bit completes a leaf. -/
def leafEnds (s : State) (b : Bool) : Bool :=
  match s.1 with
  | .zeros z => b && decide (z = 0)
  | .payload r => decide (r = 1)
  | _ => false

/-- The length register after one bit. -/
def nextTotal (a : Account) (b : Bool) : ℕ :=
  match a.state.1 with
  | .length r v => if r = 1 then Nat.bit b v else 0
  | .payload r => if r = 1 then 0 else a.total
  | _ => 0

/-- Advance the account by one input bit. -/
def accountStep (a : Account) (b : Bool) : Account :=
  if capped a b then ⟨(.dead, 0), a.forks, a.leaves, 0⟩
  else
    { state := step a.state b
      forks := if a.state.1 = .tree ∧ b then a.forks + 1 else a.forks
      leaves := if leafEnds a.state b then a.leaves + 1 else a.leaves
      total := nextTotal a b }

/-- After the first pass over an input of the given length. -/
def initialAccount (n : ℕ) : Account := ⟨(.tree, 1), n + 1, n, 0⟩

/-- The account after a prefix of an input of the given length. -/
def account (n : ℕ) (w : List Bool) : Account := w.foldl accountStep (initialAccount n)

/-- The size counter of the size pair: one during the size field, then the bits read. -/
def sizeCount : State → ℕ
  | (.size _ _, _) => 1
  | (.length _ v, _) => v.size
  | _ => 0

/-- The number of cells written on the size register. -/
def sizeWidth : State → ℕ
  | (.size r v, _) => r + v.size
  | (.length r v, _) => (r + v.size).size
  | _ => 0

/-- The position of the forks head, used as a ruler. -/
def rulerPos : State → ℕ
  | (.zeros z, _) => z
  | (.length _ v, _) => v.size - 1
  | _ => 0

/-- The number of cells written on the length register. -/
def lengthWidth (a : Account) : ℕ :=
  match a.state with
  | (.length _ v, _) => v.size
  | (.payload _, _) => a.total.size
  | _ => 0

/-- The payload counter of the length pair. -/
def payloadCount (a : Account) : ℕ :=
  match a.state with
  | (.payload r, _) => a.total - r
  | _ => 0

/-- Register invariants relative to an input of the given length. -/
structure AccountValid (n : ℕ) (a : Account) : Prop where
  /-- The scalar state is active or terminal. -/
  active : Active a.state
  /-- The forks counter retains the first-pass count. -/
  forks_ge : n + 1 ≤ a.forks
  /-- The completed leaves never exceed the forks. -/
  leaves_le : a.leaves ≤ a.forks
  /-- Outside the abandoned state, the pending count is the difference of the counters. -/
  pending : a.state.1 ≠ .dead → a.state.2 + a.leaves = a.forks
  /-- The size register fits the ruler. -/
  sizeWidth_le : sizeWidth a.state ≤ a.forks.size + 1
  /-- The ruler head stays within the forks counter's width. -/
  rulerPos_le : rulerPos a.state ≤ a.forks.size
  /-- During a payload, the register is at least two. -/
  total_ge : ∀ r, a.state.1 = .payload r → 2 ≤ a.total
  /-- During a payload, the remaining count is below the register. -/
  payload_lt : ∀ r, a.state.1 = .payload r → r < a.total
  /-- The length register fits the ruler. -/
  total_size_le : ∀ r, a.state.1 = .payload r → a.total.size ≤ a.forks.size + 1
  /-- Outside a payload, the register is zero. -/
  total_zero : (∀ r, a.state.1 ≠ .payload r) → a.total = 0

/-- Build the invariant from its fields over the components of an account. -/
theorem AccountValid.of_fields (n : ℕ) (s : State) (f l t : ℕ) (h1 : Active s)
    (h2 : n + 1 ≤ f) (h3 : l ≤ f) (h4 : s.1 ≠ .dead → s.2 + l = f)
    (h5 : sizeWidth s ≤ f.size + 1) (h6 : rulerPos s ≤ f.size)
    (h7 : ∀ r, s.1 = .payload r → 2 ≤ t) (h8 : ∀ r, s.1 = .payload r → r < t)
    (h9 : ∀ r, s.1 = .payload r → t.size ≤ f.size + 1)
    (h10 : (∀ r, s.1 ≠ .payload r) → t = 0) : AccountValid n ⟨s, f, l, t⟩ :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- Outside the abandoned state, the pending count is the excess of forks over leaves. -/
theorem AccountValid.pending_eq {n : ℕ} {a : Account} (h : AccountValid n a)
    (hd : a.state.1 ≠ .dead) : a.state.2 = a.forks - a.leaves := by
  have := h.pending hd
  omega

/-- The initial account is valid. -/
theorem initialAccount_valid (n : ℕ) : AccountValid n (initialAccount n) where
  active := show 0 < 1 by decide
  forks_ge := Nat.le_refl _
  leaves_le := Nat.le_succ _
  pending := fun _ ↦ by simp only [initialAccount]; omega
  sizeWidth_le := Nat.zero_le _
  rulerPos_le := Nat.zero_le _
  total_ge := fun _ h ↦ by cases h
  payload_lt := fun _ h ↦ by cases h
  total_size_le := fun _ h ↦ by cases h
  total_zero := fun _ ↦ rfl

/-- The abandoned account is valid. -/
theorem dead_valid (n : ℕ) (a : Account) (h : AccountValid n a) :
    AccountValid n ⟨(.dead, 0), a.forks, a.leaves, 0⟩ :=
  ⟨rfl, h.forks_ge, h.leaves_le, fun hd ↦ (hd rfl).elim, Nat.zero_le _, Nat.zero_le _,
    (fun _ h ↦ by cases h), (fun _ h ↦ by cases h), (fun _ h ↦ by cases h), fun _ ↦ rfl⟩

/-- Binary size grows by at most one per appended digit. -/
theorem size_bit (b : Bool) (v : ℕ) (hv : 0 < v) : (Nat.bit b v).size = v.size + 1 := by
  have hn : Nat.bit b v ≠ 0 := by
    rw [Nat.bit_val]
    cases b
    · simp only [Bool.toNat_false, Nat.add_zero]
      omega
    · simp only [Bool.toNat_true]
      omega
  rw [Nat.size_bit hn]

/-- Binary size is positive on positive numbers. -/
theorem size_pos_of_pos (v : ℕ) (hv : 0 < v) : 0 < v.size := by
  have h := Geb.BitTree.Counter.lt_pow_size v
  by_cases hz : v.size = 0
  · rw [hz] at h
    simp at h
    omega
  · omega

/-- One bit preserves the account invariants. -/
theorem accountStep_valid (n : ℕ) (a : Account) (b : Bool) (h : AccountValid n a) :
    AccountValid n (accountStep a b) := by
  unfold accountStep
  split
  · exact dead_valid n a h
  · rename_i hc
    have ha := h.active
    have hp := h.pending
    have hl := h.leaves_le
    have hsw := h.sizeWidth_le
    have hrp := h.rulerPos_le
    have hf := h.forks_ge
    rcases hs : a.state with ⟨m, k⟩
    rw [hs] at ha hp hsw hrp
    cases m with
    | tree =>
      change 0 < k at ha
      have hk : k + a.leaves = a.forks := hp (by simp)
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      cases b
      · change AccountValid n ⟨(.zeros 0, k), a.forks, a.leaves, 0⟩
        exact AccountValid.of_fields n _ _ _ _ ha hf hl (fun _ ↦ hk) (Nat.zero_le _)
          (Nat.zero_le _) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h)
          (fun _ ↦ rfl)
      · change AccountValid n ⟨(.tree, k + 1), a.forks + 1, a.leaves, 0⟩
        exact AccountValid.of_fields n _ _ _ _ (show 0 < k + 1 by omega) (by omega) (by omega)
          (fun _ ↦ by omega) (Nat.zero_le _) (Nat.zero_le _) (fun _ h ↦ by cases h)
          (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
    | zeros z =>
      change 0 < k at ha
      simp only [sizeWidth, rulerPos] at hsw hrp
      have hk : k + a.leaves = a.forks := hp (by simp)
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      simp only [capped, hs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      cases b with
      | false =>
        have hz : z < a.forks.size := by
          by_contra hlt
          exact hc ⟨rfl, by omega⟩
        change AccountValid n ⟨(.zeros (z + 1), k), a.forks, a.leaves, 0⟩
        exact AccountValid.of_fields n _ _ _ _ ha hf hl (fun _ ↦ hk) (Nat.zero_le _) hz
          (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
      | true =>
        by_cases hz : z = 0
        · subst hz
          change AccountValid n ⟨finish k, a.forks, a.leaves + 1, 0⟩
          unfold finish
          split
          · rename_i hk1
            subst hk1
            exact AccountValid.of_fields n _ _ _ _ rfl hf (by omega) (fun _ ↦ by omega)
              (Nat.zero_le _) (Nat.zero_le _) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h)
              (fun _ h ↦ by cases h) (fun _ ↦ rfl)
          · exact AccountValid.of_fields n _ _ _ _ (show 0 < k - 1 by omega) hf (by omega)
              (fun _ ↦ by omega) (Nat.zero_le _) (Nat.zero_le _) (fun _ h ↦ by cases h)
              (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
        · have hstep : step (.zeros z, k) true = (.size z 1, k) := by simp [step, hz]
          have hle : leafEnds (.zeros z, k) true = false := by simp [leafEnds, hz]
          rw [hstep, hle]
          change AccountValid n ⟨(.size z 1, k), a.forks, a.leaves, 0⟩
          exact AccountValid.of_fields n _ _ _ _ ⟨ha, by omega, by decide⟩ hf hl (fun _ ↦ hk)
            (by simp only [sizeWidth, Nat.size_one]; omega) (Nat.zero_le _)
            (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
    | size r v =>
      obtain ⟨hk0, hr, hv⟩ := ha
      simp only [sizeWidth, rulerPos] at hsw hrp
      have hk : k + a.leaves = a.forks := hp (by simp)
      have hsb := size_bit b v hv
      have hb : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      by_cases he : r = 1
      · subst he
        change AccountValid n ⟨(.length (Nat.bit b v - 1) 1, k), a.forks, a.leaves, 0⟩
        have hw : (Nat.bit b v - 1 + Nat.size 1).size = v.size + 1 := by
          rw [Nat.size_one, Nat.sub_add_cancel (by omega), hsb]
        exact AccountValid.of_fields n _ _ _ _ ⟨hk0, by omega, by decide⟩ hf hl (fun _ ↦ hk)
          (by simp only [sizeWidth]; omega)
          (by simp only [rulerPos, Nat.size_one]; omega)
          (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
      · have hstep : step (.size r v, k) b = (.size (r - 1) (Nat.bit b v), k) := by
          simp [step, he]
        rw [hstep]
        change AccountValid n ⟨(.size (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩
        exact AccountValid.of_fields n _ _ _ _ ⟨hk0, by omega, by omega⟩ hf hl (fun _ ↦ hk)
          (by simp only [sizeWidth]; omega) (by simp only [rulerPos]; omega)
          (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
    | length r v =>
      obtain ⟨hk0, hr, hv⟩ := ha
      simp only [sizeWidth, rulerPos] at hsw hrp
      have hk : k + a.leaves = a.forks := hp (by simp)
      simp only [capped, hs, decide_eq_true_eq] at hc
      have hcap : v.size - 1 < a.forks.size := by omega
      have hsb := size_bit b v hv
      have hb : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
      by_cases he : r = 1
      · subst he
        have hnt : nextTotal a b = Nat.bit b v := by simp [nextTotal, hs]
        rw [hnt]
        change AccountValid n ⟨(.payload (Nat.bit b v - 1), k), a.forks, a.leaves, Nat.bit b v⟩
        exact AccountValid.of_fields n _ _ _ _ ⟨hk0, by omega⟩ hf hl (fun _ ↦ hk)
          (Nat.zero_le _) (Nat.zero_le _) (fun _ _ ↦ hb) (fun _ hr ↦ by cases hr; omega)
          (fun _ _ ↦ by omega) (fun hne ↦ (hne _ rfl).elim)
      · have hstep : step (.length r v, k) b = (.length (r - 1) (Nat.bit b v), k) := by
          simp [step, he]
        have hnt : nextTotal a b = 0 := by simp [nextTotal, hs, he]
        rw [hstep, hnt]
        change AccountValid n ⟨(.length (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩
        have hw : r - 1 + (Nat.bit b v).size = r + v.size := by rw [hsb]; omega
        exact AccountValid.of_fields n _ _ _ _ ⟨hk0, by omega, by omega⟩ hf hl (fun _ ↦ hk)
          (by simp only [sizeWidth]; rw [hw]; exact hsw) (by simp only [rulerPos]; omega)
          (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
    | payload r =>
      obtain ⟨hk0, hr⟩ := ha
      have hk : k + a.leaves = a.forks := hp (by simp)
      have ht2 := h.total_ge r (by rw [hs])
      have hlt := h.payload_lt r (by rw [hs])
      have hts := h.total_size_le r (by rw [hs])
      by_cases he : r = 1
      · subst he
        have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
        rw [hnt]
        change AccountValid n ⟨finish k, a.forks, a.leaves + 1, 0⟩
        unfold finish
        split
        · rename_i hk1
          subst hk1
          exact AccountValid.of_fields n _ _ _ _ rfl hf (by omega) (fun _ ↦ by omega)
            (Nat.zero_le _) (Nat.zero_le _) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h)
            (fun _ h ↦ by cases h) (fun _ ↦ rfl)
        · exact AccountValid.of_fields n _ _ _ _ (show 0 < k - 1 by omega) hf (by omega)
            (fun _ ↦ by omega) (Nat.zero_le _) (Nat.zero_le _) (fun _ h ↦ by cases h)
            (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ ↦ rfl)
      · have hstep : step (.payload r, k) b = (.payload (r - 1), k) := by simp [step, he]
        have hle : leafEnds (.payload r, k) b = false := by simp [leafEnds, he]
        have hnt : nextTotal a b = a.total := by simp [nextTotal, hs, he]
        rw [hstep, hle, hnt]
        change AccountValid n ⟨(.payload (r - 1), k), a.forks, a.leaves, a.total⟩
        exact AccountValid.of_fields n _ _ _ _ ⟨hk0, by omega⟩ hf hl (fun _ ↦ hk)
          (Nat.zero_le _) (Nat.zero_le _) (fun _ _ ↦ ht2) (fun _ hr ↦ by cases hr; omega)
          (fun _ _ ↦ hts) (fun hne ↦ (hne _ rfl).elim)
    | done =>
      change k = 0 at ha
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      change AccountValid n ⟨(.dead, k), a.forks, a.leaves, 0⟩
      exact AccountValid.of_fields n _ _ _ _ ha hf hl (fun hd ↦ (hd rfl).elim) (Nat.zero_le _)
        (Nat.zero_le _) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h)
        (fun _ ↦ rfl)
    | dead =>
      change k = 0 at ha
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      change AccountValid n ⟨(.dead, k), a.forks, a.leaves, 0⟩
      exact AccountValid.of_fields n _ _ _ _ ha hf hl (fun hd ↦ (hd rfl).elim) (Nat.zero_le _)
        (Nat.zero_le _) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h) (fun _ h ↦ by cases h)
        (fun _ ↦ rfl)

/-- Every prefix of an input has a valid account. -/
theorem account_foldl_valid (n : ℕ) (w : List Bool) : ∀ a, AccountValid n a →
    AccountValid n (w.foldl accountStep a) :=
  List.rec (fun _ h ↦ h) (fun b _ ih a h ↦ ih _ (accountStep_valid n a b h)) w

/-- The account of every prefix is valid. -/
theorem account_valid (n : ℕ) (w : List Bool) : AccountValid n (account n w) :=
  account_foldl_valid n w _ (initialAccount_valid n)

/-- Appending one bit advances the account once. -/
theorem account_append (n : ℕ) (w : List Bool) (b : Bool) :
    account n (w ++ [b]) = accountStep (account n w) b := by
  simp only [account, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The account at the next prefix is one update of the current account. -/
theorem account_take_succ (n : ℕ) (w : List Bool) (t : ℕ) (h : t < w.length) :
    account n (w.take (t + 1)) = accountStep (account n (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, account_append]

/-- An uncapped update follows the scanner. -/
theorem accountStep_state (a : Account) (b : Bool) (h : capped a b = false) :
    (accountStep a b).state = step a.state b := by
  simp [accountStep, h]

/-- A capped update abandons the scan. -/
theorem accountStep_state_capped (a : Account) (b : Bool) (h : capped a b = true) :
    (accountStep a b).state.1 = .dead := by
  simp [accountStep, h]

/-- One bit raises the sum of both counters by at most one. -/
theorem accountStep_sum_le (a : Account) (b : Bool) :
    (accountStep a b).forks + (accountStep a b).leaves ≤ a.forks + a.leaves + 1 := by
  unfold accountStep
  split
  · dsimp only
    omega
  · dsimp only
    rcases hs : a.state with ⟨m, k⟩
    cases m <;> cases b
    all_goals simp only [leafEnds, reduceCtorEq, Bool.false_eq_true, and_self, and_true,
      and_false, ↓reduceIte, Bool.true_and, Bool.false_and, decide_eq_true_eq]
    all_goals first | omega | (split_ifs <;> omega)

/-- One bit raises the forks counter by at most one. -/
theorem accountStep_forks_le (a : Account) (b : Bool) :
    (accountStep a b).forks ≤ a.forks + 1 := by
  unfold accountStep
  split
  · dsimp only
    omega
  · dsimp only
    split_ifs <;> omega

/-- One bit raises the leaves counter by at most one. -/
theorem accountStep_leaves_le (a : Account) (b : Bool) :
    (accountStep a b).leaves ≤ a.leaves + 1 := by
  unfold accountStep
  split
  · dsimp only
    omega
  · dsimp only
    split_ifs <;> omega

/-- A prefix bounds the forks counter. -/
theorem account_foldl_forks_le (w : List Bool) : ∀ a,
    (w.foldl accountStep a).forks ≤ a.forks + w.length :=
  List.rec (fun _ ↦ by simp) (fun b w ih a ↦ by
    have hi := ih (accountStep a b)
    have hs := accountStep_forks_le a b
    simp only [List.foldl_cons, List.length_cons]
    omega) w

/-- A prefix bounds the leaves counter. -/
theorem account_foldl_leaves_le (w : List Bool) : ∀ a,
    (w.foldl accountStep a).leaves ≤ a.leaves + w.length :=
  List.rec (fun _ ↦ by simp) (fun b w ih a ↦ by
    have hi := ih (accountStep a b)
    have hs := accountStep_leaves_le a b
    simp only [List.foldl_cons, List.length_cons]
    omega) w

/-- The forks counter is bounded by the input length plus one plus the prefix length. -/
theorem account_forks_le (n : ℕ) (w : List Bool) : (account n w).forks ≤ n + 1 + w.length :=
  account_foldl_forks_le w (initialAccount n)

/-- The leaves counter is bounded by the input length plus the prefix length. -/
theorem account_leaves_le (n : ℕ) (w : List Bool) : (account n w).leaves ≤ n + w.length :=
  account_foldl_leaves_le w (initialAccount n)

/-- A prefix bounds the sum of its counters. -/
theorem account_foldl_sum_le (w : List Bool) : ∀ a,
    (w.foldl accountStep a).forks + (w.foldl accountStep a).leaves ≤
      a.forks + a.leaves + w.length :=
  List.rec (fun _ ↦ by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact Nat.le_refl _) (fun b w ih a ↦ by
    have hi := ih (accountStep a b)
    have hs := accountStep_sum_le a b
    simp only [List.foldl_cons, List.length_cons]
    omega) w

/-- Both counters are bounded by twice the input length plus one. -/
theorem account_sum_le (n : ℕ) (w : List Bool) :
    (account n w).forks + (account n w).leaves ≤ 2 * n + 1 + w.length := by
  have h := account_foldl_sum_le w (initialAccount n)
  change (account n w).forks + (account n w).leaves ≤ n + 1 + n + w.length at h
  omega

/-- A capped state requires more input than any prefix leaves. -/
theorem need_of_capped (n : ℕ) (a : Account) (b : Bool) (h : AccountValid n a)
    (hc : capped a b = true) : 2 * n + 1 < need (step a.state b) := by
  have ha := h.active
  have hf := h.forks_ge
  have hpow := Geb.BitTree.Counter.lt_pow_size a.forks
  have hmono := Geb.BitTree.Counter.size_mono hf
  rcases hs : a.state with ⟨m, k⟩
  rw [hs] at ha
  cases m with
  | zeros z =>
    change 0 < k at ha
    simp only [capped, hs, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨rfl, hz⟩ := hc
    simp only [step, need]
    have h1 : 2 ^ a.forks.size ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hz
    have h2 : 2 ^ (z + 1) = 2 * 2 ^ z := Nat.pow_succ'
    omega
  | length r v =>
    obtain ⟨hk, hr, hv⟩ := ha
    simp only [capped, hs, decide_eq_true_eq] at hc
    have hvs : 2 ^ (v.size - 1) ≤ v := by
      have := size_pos_of_pos v hv
      obtain ⟨k, hk'⟩ : ∃ k, v.size = k + 1 := ⟨v.size - 1, by omega⟩
      rw [hk', Nat.add_sub_cancel]
      by_contra hlt
      have := Geb.BitTree.Counter.size_le_of_lt_pow v k (by omega)
      omega
    have h1 : 2 ^ a.forks.size ≤ 2 ^ (v.size - 1) := Nat.pow_le_pow_right (by decide) hc
    have hb : 2 * v ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
    simp only [step]
    split
    · simp only [need]
      omega
    · simp only [need]
      have hp : 1 ≤ 2 ^ (r - 1) := Nat.one_le_two_pow
      have := Nat.mul_le_mul_left (Nat.bit b v) hp
      omega
  | tree => simp [capped, hs] at hc
  | size _ _ => simp [capped, hs] at hc
  | payload _ => simp [capped, hs] at hc
  | done => simp [capped, hs] at hc
  | dead => simp [capped, hs] at hc

/-- Along every prefix, the account follows the scanner, or it has abandoned a scan that
cannot accept within the remaining input. -/
theorem account_state_or_dead (n : ℕ) (w : List Bool) (hw : w.length ≤ n) :
    (account n w).state = scan w ∨
      ((account n w).state.1 = .dead ∧ n < w.length + need (scan w)) := by
  revert hw
  refine List.reverseRecOn w ?_ ?_
  · intro _
    exact Or.inl rfl
  · intro w b ih hw'
    have hw : w.length ≤ n := by simp only [List.length_append, List.length_cons] at hw'; omega
    have hlt : w.length < n := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hw'
      omega
    have hscan : scan (w ++ [b]) = step (scan w) b := by
      simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [account_append, hscan]
    rcases ih hw with heq | ⟨hd, hn⟩
    · cases hc : capped (account n w) b
      · left
        rw [accountStep_state _ _ hc, heq]
      · right
        refine ⟨accountStep_state_capped _ _ hc, ?_⟩
        have := need_of_capped n (account n w) b (account_valid n w) hc
        rw [heq] at this
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    · right
      have hc : capped (account n w) b = false := by
        rcases hs : (account n w).state with ⟨m, k⟩
        rw [hs] at hd
        simp only at hd
        subst hd
        simp [capped, hs]
      have hstep := need_step (scan w) b (scan_active w)
      refine ⟨?_, ?_⟩
      · rw [accountStep_state _ _ hc]
        rcases hs : (account n w).state with ⟨m, k⟩
        rw [hs] at hd
        simp only at hd
        subst hd
        rfl
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega

/-- The account accepts exactly the words the streaming scanner accepts. -/
theorem account_done_iff (w : List Bool) :
    (account w.length w).state.1 = .done ↔ validBool w = true := by
  rw [validBool, decide_eq_true_eq]
  rcases account_state_or_dead w.length w (Nat.le_refl _) with heq | ⟨hd, hn⟩
  · rw [heq]
  · constructor
    · intro h
      rw [hd] at h
      cases h
    · intro h
      have hz : need (scan w) = 0 := by
        rcases hs : scan w with ⟨m, k⟩
        rw [hs] at h
        simp only at h
        subst h
        rfl
      omega

end Geb.BitTree.EliasBinary
