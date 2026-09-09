/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Scanner
public import Geb.Prototypes.Computability.BitTree.Counter
public import Mathlib.Tactic.SplitIfs

set_option doc.verso true

/-!
# Two monotone counters for the tree scanner

The pending count is the difference between one plus the forks and the completed leaves.
Each counter only increases, so binary-counter amortization bounds the combined update cost.

## Main definitions

* {lit}`Account` retains the scanner mode and both monotone counters.
* {lit}`account` processes an input prefix.
* {lit}`runCost` sums the costs of the binary-counter macros.

## Main statements

* {lit}`account_project` identifies the accounting state with the pure scanner.
* {lit}`runCost_identity` expresses the exact amortized cost.
* {lit}`runCost_le` gives a linear bound.

## Tags

binary counter, recognizer, amortized complexity
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

/-- The finite control and the two monotone counts whose difference is pending work. -/
@[ext] structure Account where
  /-- The scanner mode. -/
  mode : Mode
  /-- One plus the number of forks. -/
  forks : ℕ
  /-- The number of completed leaves. -/
  leaves : ℕ
  deriving DecidableEq, Repr

/-- Recover the scanner's pending count by subtraction. -/
def accountProject (s : Account) : State := (s.mode, s.forks - s.leaves)

/-- The initial account reserves one root and has completed no leaves. -/
def initialAccount : Account := ⟨.tree, 1, 0⟩

/-- Consume a bit, increasing exactly the counter specified by its mode. -/
def accountStep (s : Account) (b : Bool) : Account :=
  ⟨(Geb.BitTree.step (accountProject s) b).1,
    if s.mode = .tree ∧ b = true then s.forks + 1 else s.forks,
    if s.mode = .string ∧ b = false then s.leaves + 1 else s.leaves⟩

/-- Accounting after an input prefix. -/
def account (w : List Bool) : Account := w.foldl accountStep initialAccount

/-- A valid account has ordered counts, with equality exactly in terminal modes. -/
def AccountValid (s : Account) : Prop :=
  s.leaves ≤ s.forks ∧ 0 < s.forks ∧
    match s.mode with
    | .tree | .string | .bit => s.leaves < s.forks
    | .done | .dead => s.leaves = s.forks

/-- Counter updates preserve the accounting invariant. -/
theorem accountStep_valid (s : Account) (b : Bool) (h : AccountValid s) :
    AccountValid (accountStep s b) := by
  rcases s with ⟨m, a, c⟩
  cases m <;> cases b <;> dsimp [AccountValid, accountStep, accountProject,
    Geb.BitTree.step, finish] at h ⊢
  all_goals by_cases he : a - c = 1
  all_goals (try simp only [he, ↓reduceIte])
  all_goals exact ⟨by omega, by omega, by omega⟩

/-- Projecting one update agrees with the original scanner step. -/
theorem accountStep_project (s : Account) (b : Bool) (h : AccountValid s) :
    accountProject (accountStep s b) = Geb.BitTree.step (accountProject s) b := by
  rcases s with ⟨m, a, c⟩
  cases m <;> cases b <;> simp_all only [AccountValid, accountStep, accountProject,
    Geb.BitTree.step, finish, Bool.false_eq_true, Bool.true_eq_false, and_false, and_true,
    ↓reduceIte, reduceCtorEq]
  all_goals first | (congr 1; omega) | (split_ifs <;> simp_all <;> omega)

/-- Folding counter updates preserves the invariant. -/
theorem account_foldl_valid (w : List Bool) : ∀ s, AccountValid s →
    AccountValid (w.foldl accountStep s) :=
  List.rec (fun _ h ↦ h)
    (fun b _ ih s h ↦ ih (accountStep s b) (accountStep_valid s b h)) w

/-- Folding commutes with projection to the pure scanner. -/
theorem account_foldl_project (w : List Bool) : ∀ s, AccountValid s →
    accountProject (w.foldl accountStep s) = w.foldl Geb.BitTree.step (accountProject s) :=
  List.rec (fun _ _ ↦ rfl) (fun b _ ih s h ↦ by
    rw [List.foldl_cons, List.foldl_cons, ih _ (accountStep_valid s b h),
      accountStep_project s b h]) w

/-- Every reachable account satisfies the invariant. -/
theorem account_valid (w : List Bool) : AccountValid (account w) :=
  account_foldl_valid w initialAccount (by simp [AccountValid, initialAccount])

/-- Completed leaves never exceed available tree positions. -/
theorem account_leaves_le (w : List Bool) : (account w).leaves ≤ (account w).forks :=
  (account_valid w).1

/-- The initial root contributes at least one to the fork counter. -/
theorem account_forks_pos (w : List Bool) : 0 < (account w).forks :=
  (account_valid w).2.1

/-- Active modes retain a strict excess of tree positions over completed leaves. -/
theorem account_active_lt (w : List Bool)
    (h : (account w).mode = .tree ∨ (account w).mode = .string ∨
      (account w).mode = .bit) : (account w).leaves < (account w).forks := by
  have hv := (account_valid w).2.2
  rcases h with h | h | h <;> simpa only [h] using hv

/-- Terminal modes have completed all available tree positions. -/
theorem account_terminal_eq (w : List Bool)
    (h : (account w).mode = .done ∨ (account w).mode = .dead) :
    (account w).leaves = (account w).forks := by
  have hv := (account_valid w).2.2
  rcases h with h | h <;> simpa only [h] using hv

/-- The two-counter account projects to the original scanner. -/
theorem account_project (w : List Bool) : accountProject (account w) = scan w :=
  account_foldl_project w initialAccount (by simp [AccountValid, initialAccount])

/-- A prefix extended by one bit performs one accounting update. -/
theorem account_append (w : List Bool) (b : Bool) :
    account (w ++ [b]) = accountStep (account w) b := by
  simp only [account, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One bit increases the sum of counts by at most one. -/
theorem accountStep_sum_le (s : Account) (b : Bool) :
    (accountStep s b).forks + (accountStep s b).leaves ≤ s.forks + s.leaves + 1 := by
  rcases s with ⟨m, a, c⟩
  cases m <;> cases b <;> simp [accountStep] <;> omega

/-- A prefix bounds the sum of its counters. -/
theorem account_foldl_sum_le (w : List Bool) : ∀ s,
    (w.foldl accountStep s).forks + (w.foldl accountStep s).leaves ≤
      s.forks + s.leaves + w.length :=
  List.rec (fun _ ↦ by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact Nat.le_refl _) (fun b w ih s ↦ by
    have hi := ih (accountStep s b)
    have hs := accountStep_sum_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega) w

/-- The sum of both counters is bounded by the consumed length plus one. -/
theorem account_sum_le (w : List Bool) :
    (account w).forks + (account w).leaves ≤ w.length + 1 := by
  have h := account_foldl_sum_le w initialAccount
  change (account w).forks + (account w).leaves ≤ 1 + 0 + w.length at h
  omega

/-- Both binary counters fit within the size of the prefix length plus two. -/
theorem account_size_le (w : List Bool) :
    (account w).forks.size ≤ (w.length + 2).size ∧
      (account w).leaves.size ≤ (w.length + 2).size := by
  have h := account_sum_le w
  exact ⟨Counter.size_mono (by omega), Counter.size_mono (by omega)⟩

/-- The cost of consuming a bit, including an increment and its return scan when needed. -/
def macroCost (s : Account) (b : Bool) : ℕ :=
  1 + if s.mode = .tree ∧ b = true then 2 * Counter.flips s.forks.bits + 1
    else if s.mode = .string ∧ b = false then 2 * Counter.flips s.leaves.bits + 1 else 0

/-- The accumulated digit changes and update count used in the cost identity. -/
def accountPotential (s : Account) : ℕ :=
  2 * (Counter.totalFlips s.forks + Counter.totalFlips s.leaves) + s.forks + s.leaves

/-- The increase in accounting potential is exactly the cost beyond reading the input bit. -/
theorem macroCost_identity (s : Account) (b : Bool) :
    macroCost s b + accountPotential s = 1 + accountPotential (accountStep s b) := by
  rcases s with ⟨m, a, c⟩
  cases m <;> cases b <;> simp only [macroCost, accountPotential, accountStep,
    Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, ↓reduceIte, reduceCtorEq]
  all_goals (simp only [Counter.totalFlips]; omega)

/-- One combined update of the account and accumulated cost. -/
def costStep (s : Account × ℕ) (b : Bool) : Account × ℕ :=
  (accountStep s.1 b, s.2 + macroCost s.1 b)

/-- The account component of the cost fold is the ordinary accounting fold. -/
theorem cost_foldl_fst (w : List Bool) : ∀ s c,
    (w.foldl costStep (s, c)).1 = w.foldl accountStep s :=
  List.rec (fun _ _ ↦ rfl) (fun b _ ih s c ↦ ih (accountStep s b) (c + macroCost s b)) w

/-- The exact accumulated potential identity for a fold from any initial account and cost. -/
theorem cost_foldl_identity (w : List Bool) : ∀ s c,
    (w.foldl costStep (s, c)).2 + accountPotential s =
      c + w.length + accountPotential (w.foldl accountStep s) :=
  List.rec (fun _ _ ↦ by simp only [List.foldl_nil, List.length_nil, Nat.add_zero])
    (fun b w ih s c ↦ by
    have hi := ih (accountStep s b) (c + macroCost s b)
    have hs := macroCost_identity s b
    simp only [List.foldl_cons, List.length_cons, costStep]
    change _ + accountPotential s = _
    omega) w

/-- Sum of the binary-counter macro costs over the input. -/
def runCost (w : List Bool) : ℕ := (w.foldl costStep (initialAccount, 0)).2

/-- Extending a prefix adds the macro cost at that prefix's account. -/
theorem runCost_append (w : List Bool) (b : Bool) :
    runCost (w ++ [b]) = runCost w + macroCost (account w) b := by
  simp only [runCost, List.foldl_append, List.foldl_cons, List.foldl_nil, costStep,
    cost_foldl_fst, account]

/-- The exact total cost in terms of both monotone counter histories. -/
theorem runCost_identity (w : List Bool) :
    runCost w + 3 = w.length + 2 * (Counter.totalFlips (account w).forks +
      Counter.totalFlips (account w).leaves) + (account w).forks + (account w).leaves := by
  have h := cost_foldl_identity w initialAccount 0
  change runCost w + 3 = 0 + w.length + accountPotential (account w) at h
  simpa only [Nat.zero_add, accountPotential, Nat.add_assoc] using h

/-- The two-counter implementation has linear total macro cost. -/
theorem runCost_le (w : List Bool) : runCost w ≤ 6 * w.length + 2 := by
  have hi := runCost_identity w
  have ha := Counter.totalFlips_le (account w).forks
  have hb := Counter.totalFlips_le (account w).leaves
  have hs := account_sum_le w
  omega

/-- The accounting state at the next prefix is one update from the current prefix. -/
theorem account_take_succ (w : List Bool) (t : ℕ) (h : t < w.length) :
    account (w.take (t + 1)) = accountStep (account (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, account_append]

/-- Extending a prefix adds one input-and-counter macro cost. -/
theorem runCost_take_succ (w : List Bool) (t : ℕ) (h : t < w.length) :
    runCost (w.take (t + 1)) =
      runCost (w.take t) + macroCost (account (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, runCost_append]

/-- Both counters of every prefix fit in the binary width of the whole input length plus two. -/
theorem prefix_size_le (w : List Bool) (t : ℕ) :
    (account (w.take t)).forks.size ≤ (w.length + 2).size ∧
      (account (w.take t)).leaves.size ≤ (w.length + 2).size := by
  have h := account_size_le (w.take t)
  have hw : ((w.take t).length + 2).size ≤ (w.length + 2).size :=
    Counter.size_mono (by simp only [List.length_take]; omega)
  exact ⟨Nat.le_trans h.1 hw, Nat.le_trans h.2 hw⟩

/-- The chosen width always accommodates the initialization markers. -/
theorem width_pos (n : ℕ) : 0 < (n + 2).size := by
  have h := Counter.lt_pow_size (n + 2)
  by_cases hz : (n + 2).size = 0
  · rw [hz] at h
    simp only [Nat.pow_zero] at h
    omega
  · omega

end Geb.BitTree.BinaryMachine
