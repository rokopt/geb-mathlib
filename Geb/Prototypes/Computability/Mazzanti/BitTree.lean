/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Derived
public import Geb.Prototypes.Computability.BitTree.Machine
public import Geb.Prototypes.Computability.BitTree.Elias.CodeBits
public import Mathlib.Data.List.Induction

set_option doc.verso true in
/-!
# The bit-tree recognizer as an expression of the algebra

The existing tree-and-payload scanner is represented by simultaneous recursion
with two components: a finite mode and a unary pending-tree counter. A leading
one preserves every input bit, including leading zeroes in the bitstring.

## Main definitions

* {lit}`checker` is a unary numerical expression with Boolean output.
* {lit}`scanExpr` is the simultaneous scan over the numerical encoding.

## Main statements

* {lit}`eval_checker` identifies the expression with {name}`Geb.BitTree.validBool`.

## Implementation notes

The counter is a number whose binary digits are all ones. Its binary length is
the pending-tree count. The original input supplies the size-bound argument to
successor. This is ordinary program data, not a semantic recursion-bound proof.
The size invariant of every expression follows from the syntax module.

The correctness proof establishes equality of functions. The existing scanner's
machine bounds therefore remain witnesses for this function; no complexity claim
about the denotational Lean evaluator is made here.

## Tags

bitstring, recognizer, function algebra, simultaneous recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Mazzanti.BitTree

open Expr
open Geb.BitTree (Mode State step scan)
open Geb.BitTree.Elias (fromPayload fromPayload_pos size_fromPayload)

/-- Unary count encoded as a string of binary ones. -/
def unary : ℕ → ℕ := Nat.rec 0 (fun _ n ↦ Nat.bit true n)

/-- Zero counter. -/
@[simp] theorem unary_zero : unary 0 = 0 := rfl

/-- Incrementing the counter appends one binary digit. -/
@[simp] theorem unary_succ (n : ℕ) : unary (n + 1) = Nat.bit true (unary n) := rfl

/-- The representation uses one bit per counter mark. -/
@[simp] theorem size_unary (n : ℕ) : (unary n).size = n :=
  Nat.rec rfl (fun n ih ↦ by
    rw [unary_succ, Nat.size_bit (Nat.bit_ne_zero_iff.mpr (fun _ ↦ rfl)), ih]) n

/-- The counter encoding distinguishes zero. -/
@[simp] theorem unary_eq_zero_iff (n : ℕ) : unary n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hs := size_unary n
    rw [h] at hs
    exact hs.symm
  · rintro rfl
    rfl

/-- Binary predecessor removes one counter mark. -/
@[simp] theorem unary_div_two (n : ℕ) : unary n / 2 = unary (n - 1) := by
  cases n
  · rfl
  · exact Nat.bit_div_two true _

/-- Mode codes are unary counts, allowing a fixed sequence of binary-predecessor tests. -/
def modeCode : Mode → ℕ
  | .tree => 0
  | .string => 1
  | .bit => 3
  | .done => 7
  | .dead => 15

/-- Dispatch on the scanner's mode using only derived conditionals and predecessors. -/
def modeCases {a : ℕ} (mode tree string bit done dead : Expr a) : Expr a :=
  ifZero mode tree (ifZero (halfOf mode) string
    (ifZero (halfOf (halfOf mode)) bit (ifZero (halfOf (halfOf (halfOf mode))) done dead)))

/-- The fixed dispatch selects exactly the indicated mode's expression. -/
theorem eval_modeCases {a : ℕ} (e tree string bit done dead : Expr a)
    (x : Fin a → ℕ) (m : Mode) (he : e.eval x = modeCode m) :
    (modeCases e tree string bit done dead).eval x =
      (match m with
      | .tree => tree
      | .string => string
      | .bit => bit
      | .done => done
      | .dead => dead).eval x := by
  cases m <;> simp [modeCases, he, modeCode]

/-- Step environment: binary pref, original input, previous mode, previous counter. -/
def stepEnv (pref bound : ℕ) (s : State) : Fin 4 → ℕ :=
  ![pref, bound, modeCode s.1, unary s.2]

/-- Next mode, with each branch an expression of the algebra. -/
def modeStep (bit : Bool) : Expr 4 :=
  modeCases (proj 4 2)
    (constant 4 (if bit then 0 else 1))
    (if bit then constant 4 3 else
      ifZero (proj 4 3) (constant 4 0)
        (ifZero (halfOf (proj 4 3)) (constant 4 7) (constant 4 0)))
    (constant 4 1) (constant 4 15) (constant 4 15)

/-- Next counter, bounded by the original input's binary length. -/
def counterStep (bit : Bool) : Expr 4 :=
  modeCases (proj 4 2)
    (if bit then (Expr.succ true).comp ![proj 4 3, proj 4 1] else proj 4 3)
    (if bit then proj 4 3 else halfOf (proj 4 3))
    (proj 4 3) (proj 4 3) (proj 4 3)

/-- The mode expression implements the scanner's finite control. -/
theorem eval_modeStep (bit : Bool) (pref bound : ℕ) (s : State) :
    (modeStep bit).eval (stepEnv pref bound s) = modeCode (step s bit).1 := by
  rw [modeStep, eval_modeCases _ _ _ _ _ _ _ s.1 rfl]
  rcases s with ⟨m, n⟩
  cases m <;> cases bit
  all_goals first | rfl | skip
  suffices h : (if n = 0 then 0 else if n - 1 = 0 then 7 else 0) =
      modeCode (Geb.BitTree.finish n).1 by
    simpa only [stepEnv, step, eval_ifZero, eval_proj, Matrix.cons_val, eval_constant,
      eval_halfOf, unary_div_two, unary_eq_zero_iff, Bool.false_eq_true, ↓reduceIte] using h
  by_cases hz : n = 0
  · subst n
    rfl
  by_cases ho : n = 1
  · subst n
    rfl
  have hp : n - 1 ≠ 0 := by omega
  rw [ite_eq_right hz, ite_eq_right hp, Geb.BitTree.finish, ite_eq_right ho]
  rfl

/-- The counter expression implements the scanner whenever one more mark fits. -/
theorem eval_counterStep (bit : Bool) (pref bound : ℕ) (s : State)
    (hbound : s.2 + 1 ≤ bound.size) :
    (counterStep bit).eval (stepEnv pref bound s) = unary (step s bit).2 := by
  rw [counterStep, eval_modeCases _ _ _ _ _ _ _ s.1 rfl]
  rcases s with ⟨m, n⟩
  have hfit : (Nat.bit true (unary n)).size ≤ bound.size := by
    rw [← unary_succ, size_unary]
    exact hbound
  change (2 * unary n + 1).size ≤ bound.size at hfit
  by_cases hn : n = 1 <;> cases m <;> cases bit <;>
    simp_all [stepEnv, step, Geb.BitTree.finish, sizeBoundedSucc]

/-- Initial values of the two recursion components. -/
def bases : Fin 2 → Expr 1 := ![constant 1 0, constant 1 1]

/-- Skip the leading sentinel bit, then apply the scanner transition. -/
def steps (bit : Bool) : Fin 2 → Expr 4 :=
  ![ifZero (proj 4 0) (constant 4 0) (modeStep bit),
    ifZero (proj 4 0) (constant 4 1) (counterStep bit)]

/-- The selected simultaneous component, with the original input as its sole parameter. -/
def scanExpr (j : Fin 2) : Expr 2 := recursion bases (steps false) (steps true) j

/-- Read out the accepting mode, returning one at acceptance and zero otherwise. -/
def acceptMode : Expr 1 := modeCases (proj 1 0)
  (constant 1 0) (constant 1 0) (constant 1 0) (constant 1 1) (constant 1 0)

/-- Run the scan with the input also used as its counter-capacity parameter, then accept. -/
def checker : Expr 1 := acceptMode.comp ![(scanExpr 0).comp ![proj 1 0, proj 1 0]]

/-- A scanner state as the vector of simultaneous numerical components. -/
def stateCode (s : State) : Fin 2 → ℕ := ![modeCode s.1, unary s.2]

/-- At the leading sentinel, neither component reads the previous state. -/
theorem eval_steps_zero (bit : Bool) (x : Fin 4 → ℕ) (hx : x 0 = 0) (j : Fin 2) :
    (steps bit j).eval x = stateCode (.tree, 1) j := by
  match j with
  | 0 => simp [steps, hx, stateCode, modeCode]
  | 1 => simp [steps, hx, stateCode, unary]

/-- One binary recursion step implements one scanner transition after the sentinel. -/
theorem eval_scanExpr_step (bit : Bool) (pref bound : ℕ) (s : State) (hp : pref ≠ 0)
    (hs : ∀ j, (scanExpr j).eval ![pref, bound] = stateCode s j)
    (hb : s.2 + 1 ≤ bound.size) (j : Fin 2) :
    (scanExpr j).eval ![Nat.bit bit pref, bound] = stateCode (step s bit) j := by
  have he := eval_recursion_bit bases (steps false) (steps true) j bit pref
    (fun h ↦ (hp h).elim) ![bound]
  have henv : Fin.cons pref (Fin.append ![bound]
      (fun i ↦ (recursion bases (steps false) (steps true) i).eval (Fin.cons pref ![bound]))) =
      stepEnv pref bound s := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => exact hs 0
    | 3 => exact hs 1
  rw [henv] at he
  change (scanExpr j).eval ![Nat.bit bit pref, bound] = _ at he
  have hsteps : (if bit then steps true j else steps false j) = steps bit j := by
    cases bit <;> rfl
  rw [hsteps] at he
  match j with
  | 0 =>
    calc
      _ = (modeStep bit).eval (stepEnv pref bound s) := by
        simpa [steps, stepEnv, hp] using he
      _ = _ := eval_modeStep bit pref bound s
  | 1 =>
    calc
      _ = (counterStep bit).eval (stepEnv pref bound s) := by
        simpa [steps, stepEnv, hp] using he
      _ = _ := eval_counterStep bit pref bound s hb

/-- Simultaneous recursion agrees with the existing scanner on every sentinel-encoded word. -/
theorem eval_scanExpr (w : List Bool) : ∀ bound, w.length + 1 ≤ bound.size → ∀ j,
    (scanExpr j).eval ![fromPayload w, bound] = stateCode (scan w) j := by
  refine List.reverseRecOn w ?_ ?_
  · intro bound _ j
    have he := eval_recursion_bit bases (steps false) (steps true) j true 0 (by simp) ![bound]
    change (scanExpr j).eval ![fromPayload [], bound] = _ at he
    exact he.trans (eval_steps_zero true _ rfl j)
  · intro v bit ih bound hb j
    have hv : v.length + 1 ≤ bound.size := by simp only [List.length_append] at hb; omega
    have hc : (scan v).2 + 1 ≤ bound.size := by
      have h := Geb.BitTree.scan_counter_le v
      simp only [List.length_append, List.length_singleton] at hb
      omega
    have he := eval_scanExpr_step bit (fromPayload v) bound (scan v)
      (Nat.ne_of_gt (fromPayload_pos v)) (ih bound hv) hc j
    simpa [fromPayload, scan, List.foldl_append] using he

/-- The algebra expression accepts exactly the existing tree-and-payload language.
The extra leading one preserves empty words and all leading zeroes. -/
theorem eval_checker (w : List Bool) :
    checker.eval ![fromPayload w] = (Geb.BitTree.validBool w).toNat := by
  have hs := eval_scanExpr w (fromPayload w) (by rw [size_fromPayload]) 0
  have hi : (fun i ↦ (![proj 1 0, proj 1 0] i).eval ![fromPayload w]) =
      ![fromPayload w, fromPayload w] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  rw [checker, eval_comp]
  rw [acceptMode, eval_modeCases _ _ _ _ _ _ _ (scan w).1]
  · unfold Geb.BitTree.validBool
    cases (scan w).1 <;> rfl
  · change ((scanExpr 0).comp ![proj 1 0, proj 1 0]).eval ![fromPayload w] = _
    rw [eval_comp, hi]
    exact hs

end Geb.Mazzanti.BitTree
