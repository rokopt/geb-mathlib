/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Counter
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq

set_option doc.verso true in
/-!
# The increment phase

A counter register holds the reverse of its digit list, so that cell
{lit}`z` holds digit {lit}`z`, least significant first. The increment of
{name}`Geb.SizeBounded.Logspace.incL` clears the run of ones from cell
{lit}`0` and sets the digit above it. {lit}`incWalk` does exactly that from
a parked head: while it reads a one it writes a zero and moves right, and on
the first zero or blank it writes a one and halts, so that its head ends at
the {lit}`carry` of the digit list, the length of that run. {lit}`inc`
returns the head to cell {lit}`0` afterwards, and its contract transforms the
register by the increment of its digit list.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`carry` — the number of leading ones of a digit list.
* {lit}`incWalk` — clear the leading ones rightwards and set the digit above.
* {lit}`inc` — increment a counter register from a parked head.
* {lit}`incTape`, {lit}`incCfg` — the closed form of {lit}`incWalk`'s tape
  and configurations.

# Main statements

* {lit}`carry_le_length`, {lit}`carry_lt_length_incL` — the carry is within
  the digit list and within its increment.
* {lit}`getElem?_of_lt_carry`, {lit}`getElem?_carry_ne` — the digits below
  the carry are ones and the digit at it is not.
* {lit}`incL_getElem?_of_lt`, {lit}`incL_getElem?_carry`,
  {lit}`incL_getElem?_of_gt` — the increment cellwise.
* {lit}`incWalk_runsTo` — the run of the walk, naming the halted
  configuration and the step count.
* {lit}`inc_transforms` — the contract of the increment.

# Tags

Turing machine, binary counter, increment, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The number of leading ones of a digit list, least significant first. -/
@[expose] def carry : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦
    match b with
    | true => ih + 1
    | false => 0

/-- The carry of the empty list. -/
theorem carry_nil : carry [] = 0 := rfl

/-- The carry stops at a zero digit. -/
theorem carry_cons_false (d : List Bool) : carry (false :: d) = 0 := rfl

/-- The carry counts a one digit. -/
theorem carry_cons_true (d : List Bool) : carry (true :: d) = carry d + 1 := rfl

/-- The carry is within the digit list. -/
theorem carry_le_length : ∀ d : List Bool, carry d ≤ d.length :=
  List.rec (Nat.le_refl 0) fun b d ih ↦ by
    cases b
    · rw [carry_cons_false]
      exact Nat.zero_le _
    · rw [carry_cons_true, List.length_cons]
      exact Nat.succ_le_succ ih

/-- The carry is within the increment. -/
theorem carry_lt_length_incL : ∀ d : List Bool, carry d < (incL d).length :=
  List.rec Nat.zero_lt_one fun b d ih ↦ by
    cases b
    · rw [carry_cons_false, incL_cons_false, List.length_cons]
      exact Nat.zero_lt_succ _
    · rw [carry_cons_true, incL_cons_true, List.length_cons]
      exact Nat.succ_lt_succ ih

/-- The digits below the carry are ones. -/
theorem getElem?_of_lt_carry : ∀ (d : List Bool) (n : ℕ), n < carry d → d[n]? = some true :=
  List.rec (fun n h ↦ absurd h (Nat.not_lt_zero n)) fun b d ih n h ↦ by
    cases b
    · rw [carry_cons_false] at h
      exact absurd h (Nat.not_lt_zero n)
    · rw [carry_cons_true] at h
      cases n with
      | zero => rfl
      | succ n =>
        rw [List.getElem?_cons_succ]
        exact ih n (Nat.lt_of_succ_lt_succ h)

/-- The digit at the carry is not a one. -/
theorem getElem?_carry_ne : ∀ d : List Bool, d[carry d]? ≠ some true :=
  List.rec (Option.some_ne_none true).symm fun b d ih ↦ by
    cases b
    · rw [carry_cons_false, List.getElem?_cons_zero]
      exact fun h ↦ Bool.false_ne_true (Option.some.inj h)
    · rw [carry_cons_true, List.getElem?_cons_succ]
      exact ih

/-- Below the carry the increment has zeros. -/
theorem incL_getElem?_of_lt : ∀ (d : List Bool) (n : ℕ), n < carry d →
    (incL d)[n]? = some false :=
  List.rec (fun n h ↦ absurd h (Nat.not_lt_zero n)) fun b d ih n h ↦ by
    cases b
    · rw [carry_cons_false] at h
      exact absurd h (Nat.not_lt_zero n)
    · rw [carry_cons_true] at h
      rw [incL_cons_true]
      cases n with
      | zero => rfl
      | succ n =>
        rw [List.getElem?_cons_succ]
        exact ih n (Nat.lt_of_succ_lt_succ h)

/-- At the carry the increment has a one. -/
theorem incL_getElem?_carry : ∀ d : List Bool, (incL d)[carry d]? = some true :=
  List.rec rfl fun b d ih ↦ by
    cases b
    · rfl
    · rw [carry_cons_true, incL_cons_true, List.getElem?_cons_succ]
      exact ih

/-- Above the carry the increment agrees with the digit list. -/
theorem incL_getElem?_of_gt : ∀ (d : List Bool) (n : ℕ), carry d < n → (incL d)[n]? = d[n]? :=
  List.rec
    (fun n h ↦ by
      cases n with
      | zero => exact absurd h (Nat.lt_irrefl 0)
      | succ n => rfl)
    fun b d ih n h ↦ by
      cases b
      · cases n with
        | zero => exact absurd h (Nat.lt_irrefl 0)
        | succ n => rfl
      · rw [carry_cons_true] at h
        rw [incL_cons_true]
        cases n with
        | zero => exact absurd h (Nat.not_lt_zero _)
        | succ n =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
          exact ih n (Nat.lt_of_succ_lt_succ h)

/-- A cell of a register holding the reverse of a digit list holds the
corresponding digit. -/
theorem tapeOf_reverse_natCast (d : List Bool) (n : ℕ) : tapeOf d.reverse (n : ℤ) = d[n]? := by
  unfold tapeOf
  rw [List.reverse_reverse, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

/-- Clear the leading ones of the register on tape {lit}`i` rightwards from
its head: reading a one, write a zero and move right; reading a zero or a
blank, write a one and halt. -/
@[expose] def incWalk {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputTape := 0
      workTapes := fun j ↦
        if j = i then
          (if work i = some true then (some (some false), 1) else (some (some true), 0))
        else (none, 0)
      output := none
      state := if work i = some true then some () else none }

/-- Increment the counter on tape {lit}`i` from a parked head: clear the
leading ones, set the digit above, park. -/
@[expose] def inc {k : ℕ} (i : Fin k) := seq (incWalk i) (returnTape i)

/-- The tape of a counter register holding {lit}`d` whose first {lit}`s`
cells have been cleared. -/
@[expose] def incTape (d : List Bool) (s : ℕ) : ℤ → Option Bool :=
  fun z ↦ if 0 ≤ z ∧ z < s then some false else tapeOf d.reverse z

/-- Nothing cleared is the register itself. -/
theorem incTape_zero (d : List Bool) : incTape d 0 = tapeOf d.reverse := by
  funext z
  unfold incTape
  rw [ite_eq_right (fun h ↦ by omega)]

/-- The cell at the head of the cleared run holds the digit there. -/
theorem incTape_self (d : List Bool) (s : ℕ) : incTape d s (s : ℤ) = d[s]? := by
  unfold incTape
  rw [ite_eq_right (fun h ↦ lt_irrefl _ h.2), tapeOf_reverse_natCast]

/-- Clearing the cell at the head of the run extends the run. -/
theorem incTape_update_false (d : List Bool) (s : ℕ) :
    Function.update (incTape d s) (s : ℤ) (some false) = incTape d (s + 1) := by
  funext z
  unfold incTape
  by_cases hz : z = s
  · subst hz
    rw [Function.update_self, ite_eq_left ⟨Int.natCast_nonneg s, by omega⟩]
  · rw [Function.update_of_ne hz]
    by_cases h : 0 ≤ z ∧ z < s
    · rw [ite_eq_left h, ite_eq_left ⟨h.1, by omega⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h ⟨h'.1, by omega⟩)]

/-- Setting the cell at the carry, after clearing the run below it, is the
increment. -/
theorem incTape_update_true (d : List Bool) :
    Function.update (incTape d (carry d)) (carry d : ℤ) (some true) = tapeOf (incL d).reverse := by
  funext z
  by_cases hz0 : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
    by_cases hn : n = carry d
    · subst hn
      rw [Function.update_self, tapeOf_reverse_natCast, incL_getElem?_carry]
    · rw [Function.update_of_ne (by omega), tapeOf_reverse_natCast]
      unfold incTape
      by_cases hlt : n < carry d
      · rw [ite_eq_left ⟨Int.natCast_nonneg n, by omega⟩, incL_getElem?_of_lt d n hlt]
      · rw [ite_eq_right (fun h ↦ hlt (by omega)), tapeOf_reverse_natCast,
          incL_getElem?_of_gt d n (by omega)]
  · rw [Function.update_of_ne (by omega)]
    unfold incTape
    rw [ite_eq_right (fun h ↦ hz0 h.1), tapeOf_neg _ _ (by omega), tapeOf_neg _ _ (by omega)]

/-- The configuration of {name}`incWalk` after {lit}`s` steps from a parked
start in its initial state on a counter register holding {lit}`d`. -/
@[expose] def incCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (d : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapes := Function.update cfg.workTapes i (incTape d s)
    workTapePos := Function.update cfg.workTapePos i (s : ℤ) }

/-- {name}`incWalk` from a parked counter register holding {lit}`d` runs
{lit}`carry d + 1` steps, leaves it holding the increment and its head at
the carry. -/
theorem incWalk_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (d : List Bool) (hw : cfg.workTapes i = tapeOf d.reverse)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : (incL d).length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (incWalk i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (incL d).reverse)
        workTapePos := Function.update cfg.workTapePos i (carry d : ℤ) }
      (carry d + 1) B := by
  have hcB : carry d < B := lt_of_lt_of_le (carry_lt_length_incL d) hB
  have hsym : ∀ s : ℕ, (incCfg i cfg d s).workTapeSymbols i = d[s]? := by
    intro s
    change Function.update cfg.workTapes i (incTape d s) i
      (Function.update cfg.workTapePos i (s : ℤ) i) = _
    rw [Function.update_self, Function.update_self, incTape_self]
  have hstep : ∀ s : ℕ, s < carry d →
      (incWalk i).step (incCfg i cfg d s) = incCfg i cfg d (s + 1) := by
    intro s hs
    have hsome : (incCfg i cfg d s).workTapeSymbols i = some true := by
      rw [hsym s]
      exact getElem?_of_lt_carry d s hs
    have hact : ∀ j : Fin k, ((incWalk i).tr () (incCfg i cfg d s).inputSymbol
        (incCfg i cfg d s).workTapeSymbols).workTapes j =
        if j = i then ((some (some false) : Option (Option Bool)), (1 : SignType))
        else (none, 0) := by
      intro j
      change (if j = i then (if (incCfg i cfg d s).workTapeSymbols i = some true
          then ((some (some false) : Option (Option Bool)), (1 : SignType))
          else (some (some true), 0))
        else (none, 0)) = _
      rw [hsome, ite_eq_left rfl]
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if (incCfg i cfg d s).workTapeSymbols i = some true then some () else none) =
        some ()
      rw [hsome, ite_eq_left rfl]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (incTape d s) j)
            (Function.update cfg.workTapePos j (s : ℤ) j) (some false) =
          Function.update cfg.workTapes j (incTape d (s + 1)) j
        rw [Function.update_self, Function.update_self, Function.update_self,
          incTape_update_false]
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapes i (incTape d s) j =
          Function.update cfg.workTapes i (incTape d (s + 1)) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapePos j (s : ℤ) j + ((1 : SignType) : ℤ) =
          Function.update cfg.workTapePos j ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapePos i (s : ℤ) j + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj, SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hhalt : (incWalk i).step (incCfg i cfg d (carry d)) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (incL d).reverse)
        workTapePos := Function.update cfg.workTapePos i (carry d : ℤ) } := by
    have hne : (incCfg i cfg d (carry d)).workTapeSymbols i ≠ some true := by
      rw [hsym]
      exact getElem?_carry_ne d
    have hact : ∀ j : Fin k, ((incWalk i).tr () (incCfg i cfg d (carry d)).inputSymbol
        (incCfg i cfg d (carry d)).workTapeSymbols).workTapes j =
        if j = i then ((some (some true) : Option (Option Bool)), (0 : SignType))
        else (none, 0) := by
      intro j
      change (if j = i then (if (incCfg i cfg d (carry d)).workTapeSymbols i = some true
          then ((some (some false) : Option (Option Bool)), (1 : SignType))
          else (some (some true), 0))
        else (none, 0)) = _
      rw [ite_eq_right hne]
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if (incCfg i cfg d (carry d)).workTapeSymbols i = some true then some ()
        else none) = none
      rw [ite_eq_right hne]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (incTape d (carry d)) j)
            (Function.update cfg.workTapePos j (carry d : ℤ) j) (some true) =
          Function.update cfg.workTapes j (tapeOf (incL d).reverse) j
        rw [Function.update_self, Function.update_self, Function.update_self,
          incTape_update_true]
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapes i (incTape d (carry d)) j =
          Function.update cfg.workTapes i (tapeOf (incL d).reverse) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapePos j (carry d : ℤ) j + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos j (carry d : ℤ) j
        rw [SignType.coe_zero, add_zero]
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapePos i (carry d : ℤ) j + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos i (carry d : ℤ) j
        rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hout : ∀ s : ℕ, (incWalk i).outputSymbol (incCfg i cfg d s) = none := fun _ ↦ rfl
  have hzero : incCfg i cfg d 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes i (incTape d 0) = cfg.workTapes
      rw [incTape_zero, ← hw, Function.update_eq_self]
    · change Function.update cfg.workTapePos i (((0 : ℕ) : ℤ)) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega, Function.update_eq_self]
    · rfl
  have key := RunsTo.ofFamily (incWalk i) (incCfg i cfg d) (carry d) B _
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl (fun s _ ↦ hout s)
    (fun s hs j ↦ update_workTapePos_bounds i hpos (s : ℤ) (by omega) (by omega) j)
    (fun j ↦ update_workTapePos_bounds i hpos (carry d : ℤ) (by omega) (by omega) j)
  rwa [hzero] at key

/-- {name}`inc` transforms the valuation by incrementing the digit list of
register {lit}`i`, in {lit}`2 * B + 4` steps. The bound on the transformed
valuation is the contract's assumption. -/
theorem inc_transforms {k : ℕ} (i : Fin k) (B : ℕ) :
    Transforms (inc i) (fun σ ↦ Function.update σ i (incL (σ i).reverse).reverse)
      (2 * B + 4) B := by
  intro _ cfg σ hq hpark hσ _ hFB
  have hB : (incL (σ i).reverse).length ≤ B := by
    have h : (Function.update σ i (incL (σ i).reverse).reverse i).length ≤ B := hFB i
    rwa [Function.update_self, List.length_reverse] at h
  have hcl := carry_lt_length_incL (σ i).reverse
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from (hpark i).symm, Function.update_eq_self]
  have r₁ := incWalk_runsTo i { cfg with state := some (incWalk i).q₀ } rfl (σ i).reverse
    (by change cfg.workTapes i = tapeOf (σ i).reverse.reverse
        rw [List.reverse_reverse]
        exact hσ i)
    (hpark i) B hB hpos
  have r₂ := returnTape_runsTo i
    { cfg with
      state := some (returnTape i).q₀
      workTapes := Function.update cfg.workTapes i (tapeOf (incL (σ i).reverse).reverse)
      workTapePos := Function.update cfg.workTapePos i (carry (σ i).reverse : ℤ) }
    rfl (incL (σ i).reverse).reverse
    (by change Function.update cfg.workTapes i (tapeOf (incL (σ i).reverse).reverse) i = _
        rw [Function.update_self])
    (carry (σ i).reverse : ℤ)
    (by change Function.update cfg.workTapePos i (carry (σ i).reverse : ℤ) i = _
        rw [Function.update_self])
    (by omega) (by rw [List.length_reverse]; omega) B
    (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself,
    show ((carry (σ i).reverse : ℤ) + 2).toNat = carry (σ i).reverse + 2 by omega] at r₂
  have hall := r₁.seq r₂
  rw [← liftL_start (incWalk i) (returnTape i) cfg hq] at hall
  rw [show after cfg (Function.update σ i (incL (σ i).reverse).reverse) =
      liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (incL (σ i).reverse).reverse) }
      from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ i (incL (σ i).reverse).reverse l) =
        Function.update cfg.workTapes i (tapeOf (incL (σ i).reverse).reverse) l
      by_cases hl : l = i
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl
    · rfl

end

end Geb.SizeBounded.Logspace.Machine
