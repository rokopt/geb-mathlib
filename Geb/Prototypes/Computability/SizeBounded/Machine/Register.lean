/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

set_option doc.verso true

/-!
# Registers of the machine calculus

A work tape holds a bitstring in reversed layout: cell {lit}`z` holds the
{lit}`z`th element of the word's reverse for {lit}`0 ≤ z < length`, and every
other cell is blank. Cell {lit}`0` is the word's last element and cell
{lit}`length - 1` its head, so that consing a bit is one write at the first
blank cell. A register valuation assigns a word to every tape; the predicates
on configurations that every program of the calculus starts from and returns
to are that every head is at cell {lit}`0` and that the tapes hold a
valuation, and a valuation is bounded when every word's length is at most
the bound.

# Main definitions

* {lit}`tapeOf` — the tape contents of a register holding a word.
* {lit}`Parked` — every work head at cell {lit}`0`.
* {lit}`Holds` — the tapes hold a valuation.
* {lit}`Bounded` — every word of a valuation is within a bound.

# Main statements

* {lit}`tapeOf_nil`, {lit}`tapeOf_cons`, {lit}`tapeOf_update_none` — the
  layout of the empty word, consing as one {name}`Function.update`, and
  blanking the head's cell as its inverse.
* {lit}`tapeOf_of_lt`, {lit}`tapeOf_of_le`, {lit}`tapeOf_neg` — the cell
  contents inside, beyond and before the word.
* {lit}`tapeOf_injective` — the layout determines the word.
* {lit}`drop_length_sub_succ`, {lit}`reverse_take_succ` — the list equations
  the copying phases step by.

# Tags

Turing machine, register, bitstring
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The tape contents of a register holding {lit}`w`: cell {lit}`z` holds
{lit}`w.reverse[z]` for {lit}`0 ≤ z < w.length` and is blank elsewhere. -/
@[expose] def tapeOf (w : List Bool) : ℤ → Option Bool :=
  fun z ↦ if 0 ≤ z then w.reverse[z.toNat]? else none

/-- The empty word's register is blank. -/
theorem tapeOf_nil : tapeOf [] = fun _ ↦ none := by
  funext z
  simp [tapeOf]

/-- Consing a bit writes it at the cell after the word. -/
theorem tapeOf_cons (b : Bool) (w : List Bool) :
    tapeOf (b :: w) = Function.update (tapeOf w) (w.length : ℤ) (some b) := by
  funext z
  unfold tapeOf
  by_cases hz : z = w.length
  · subst hz
    simp
  · rw [Function.update_of_ne hz]
    split_ifs with h0
    · rw [List.reverse_cons, List.getElem?_append]
      split_ifs with hlt
      · rfl
      · rw [List.length_reverse] at hlt
        have : z.toNat ≠ w.length := by omega
        simp only [List.getElem?_singleton, List.length_reverse]
        rw [ite_eq_right (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]
    · rfl

/-- Inside the word a cell holds the corresponding element of the reverse. -/
theorem tapeOf_of_lt (w : List Bool) (z : ℤ) (h0 : 0 ≤ z) (h : z < w.length) :
    tapeOf w z = some (w.reverse[z.toNat]'(by simp; omega)) := by
  unfold tapeOf
  rw [ite_eq_left h0, List.getElem?_eq_getElem]

/-- Beyond the word every cell is blank. -/
theorem tapeOf_of_le (w : List Bool) (z : ℤ) (h : w.length ≤ z) : tapeOf w z = none := by
  unfold tapeOf
  split_ifs with h0
  · apply List.getElem?_eq_none
    simp
    omega
  · rfl

/-- Before cell zero every cell is blank. -/
theorem tapeOf_neg (w : List Bool) (z : ℤ) (h : z < 0) : tapeOf w z = none := by
  unfold tapeOf
  rw [ite_eq_right (by omega)]

/-- Blanking the head's cell drops the head. -/
theorem tapeOf_update_none (b : Bool) (w : List Bool) :
    Function.update (tapeOf (b :: w)) (w.length : ℤ) none = tapeOf w := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst hz
    rw [Function.update_self]
    exact (tapeOf_of_le w w.length (le_refl _)).symm
  · rw [Function.update_of_ne hz, tapeOf_cons, Function.update_of_ne hz]

/-- The layout determines the word. -/
theorem tapeOf_injective : Function.Injective tapeOf := by
  intro v w h
  have hrev : v.reverse = w.reverse := by
    apply List.ext_getElem?
    intro n
    have hv : tapeOf v (n : ℤ) = v.reverse[n]? := by
      unfold tapeOf
      rw [ite_eq_left (by omega), Int.toNat_natCast]
    have hw : tapeOf w (n : ℤ) = w.reverse[n]? := by
      unfold tapeOf
      rw [ite_eq_left (by omega), Int.toNat_natCast]
    rw [← hv, ← hw, h]
  exact List.reverse_injective hrev

/-- Dropping one element fewer conses the element at the split. -/
theorem drop_length_sub_succ (w : List Bool) (s : ℕ) (hs : s < w.length) :
    w.drop (w.length - (s + 1)) =
      w.reverse[s]'(by simp; omega) :: w.drop (w.length - s) := by
  have hidx : w.length - (s + 1) = w.length - 1 - s := by omega
  rw [hidx, List.drop_eq_getElem_cons (by omega), List.getElem_reverse]
  congr 2
  omega

/-- The reverse of a longer prefix conses the next element. -/
theorem reverse_take_succ (w : List Bool) (s : ℕ) (hs : s < w.length) :
    (w.take (s + 1)).reverse = w[s] :: (w.take s).reverse := by
  rw [List.take_succ_eq_append_getElem hs, List.reverse_append, List.reverse_singleton,
    List.singleton_append]

/-- Every work head at cell {lit}`0`. -/
@[expose] def Parked {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) : Prop :=
  ∀ i, cfg.workTapePos i = 0

/-- The tapes hold the valuation {lit}`σ`. -/
@[expose] def Holds {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (σ : Fin k → List Bool) : Prop :=
  ∀ i, cfg.workTapes i = tapeOf (σ i)

/-- Every word of the valuation has length at most {lit}`B`. -/
@[expose] def Bounded {k : ℕ} (σ : Fin k → List Bool) (B : ℕ) : Prop :=
  ∀ i, (σ i).length ≤ B

end

end Geb.SizeBounded.Machine
