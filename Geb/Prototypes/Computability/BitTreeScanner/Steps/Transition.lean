/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Cfg

set_option doc.verso true

/-!
# The two-pass tree scanner's transition, resolved

{name}`Geb.BitTreeScanner.bitTreeScanner`'s transition resolved at each case of
its table, in the forms that {lit}`Geb.BitTreeScanner.step_advance`,
{lit}`Geb.BitTreeScanner.step_stay`, {lit}`Geb.BitTreeScanner.step_retreat`
and {lit}`Geb.BitTreeScanner.step_halt` of
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic` consume.

## Main statements

* {lit}`Geb.BitTreeScanner.tr_init` through
  {lit}`Geb.BitTreeScanner.tr_dead_end` — the transition resolved at each
  case of its table.

## Implementation notes

A transition resolution is stated over an arbitrary work-symbol function
wherever the table's row does not read it, and at a triple literal where it
does, which is the form {name}`Geb.BitTreeScanner.workTapeSymbols_eq` reduces
to. A row that is a catch-all in the input column or reads a digit is
resolved at {lit}`some (boolEmb b)` by cases on the bit, or at
{lit}`some (digitEmb d)` by cases on the counter digit; a row reading either
a blank or a zero is resolved at a symbol given to be one of the two.

## Tags

Turing machine, transition, tree, prefix code, binary counter
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

variable (work : Fin 3 → Option (Fin 4)) (t₀ t₁ t₂ x : Option (Fin 4)) (inSym : Option (Fin 4))

section Init

/-- The first step writes the base markers and moves the count and ruler
heads to the lowest digit cell. -/
theorem tr_init :
    bitTreeScanner.tr stInit inSym work =
      stay stSeek (some (some 3), 1) (some (some 3), 0) (some (some 3), 1) := rfl

end Init

section Seek

/-- The counting pass over a bit, at a one of the count: the digit becomes a
zero and the carry moves outward. -/
theorem tr_seek_one (b : Bool) :
    bitTreeScanner.tr stSeek (some (boolEmb b)) ![t₀, t₁, some 1] =
      stay stSeekCarry idle idle (some (some 0), 1) := by
  cases b <;> rfl

/-- The counting pass over a bit, at a zero of the count or above its top:
the digit becomes a one and the bit is consumed. -/
theorem tr_seek_low (b : Bool) (hx : x = none ∨ x = some 0) :
    bitTreeScanner.tr stSeek (some (boolEmb b)) ![t₀, t₁, x] =
      advance stSeek idle idle (some (some 1), 0) := by
  rcases hx with rfl | rfl <;> cases b <;> rfl

/-- The counting pass at the input's end turns back, the ruler head to the
base marker. -/
theorem tr_seek_end : bitTreeScanner.tr stSeek none work = retreat stBack idle idle (none, -1) :=
  rfl

/-- The count's carry passes a one, turning it into a zero. -/
theorem tr_seekCarry_one :
    bitTreeScanner.tr stSeekCarry inSym ![t₀, t₁, some 1] =
      stay stSeekCarry idle idle (some (some 0), 1) := rfl

/-- The count's carry is absorbed at a zero or above the top, which becomes a
one, and the return begins. -/
theorem tr_seekCarry_low (hx : x = none ∨ x = some 0) :
    bitTreeScanner.tr stSeekCarry inSym ![t₀, t₁, x] =
      stay stSeekBack idle idle (some (some 1), -1) := by
  rcases hx with rfl | rfl <;> rfl

/-- The count's return reaching the base marker consumes the bit, stepping to
the lowest digit. -/
theorem tr_seekBack_base (b : Bool) :
    bitTreeScanner.tr stSeekBack (some (boolEmb b)) ![t₀, t₁, some 3] =
      advance stSeek idle idle (none, 1) := by
  cases b <;> rfl

/-- The count's return passes a digit. -/
theorem tr_seekBack_digit (b : Bool) :
    bitTreeScanner.tr stSeekBack inSym ![t₀, t₁, some (boolEmb b)] =
      stay stSeekBack idle idle (none, -1) := by
  cases b <;> rfl

/-- The return over the input passes a bit. -/
theorem tr_back_bit (b : Bool) :
    bitTreeScanner.tr stBack (some (boolEmb b)) work = retreat stBack idle idle idle := by
  cases b <;> rfl

/-- The return over the input reaching its start steps to the first bit, and
the scan begins. -/
theorem tr_back_start : bitTreeScanner.tr stBack none work = advance stMain idle idle idle := rfl

end Seek

section Main

/-- A pair bit at a pending count whose lowest digit is a two: the digit
becomes a one and the carry moves outward, the bit not yet consumed. -/
theorem tr_main_pair_two :
    bitTreeScanner.tr stMain (some (boolEmb true)) ![some 2, t₁, t₂] =
      stay stIncCarry (some (some 1), 1) idle idle := rfl

/-- A pair bit at a pending count whose lowest digit is not a two: the digit
is raised and the bit consumed. -/
theorem tr_main_pair_notTwo (hx : x = none ∨ x = some 0 ∨ x = some 1) :
    bitTreeScanner.tr stMain (some (boolEmb true)) ![x, t₁, t₂] =
      advance stMain (some (some (raise x)), 0) idle idle := by
  rcases hx with rfl | rfl | rfl <;> rfl

/-- A leaf bit in the main state moves the leaf head to the first digit
cell. -/
theorem tr_main_leaf :
    bitTreeScanner.tr stMain (some (boolEmb false)) work =
      advance stZeros idle (none, 1) idle := rfl

/-- The main state at the input's end rejects. -/
theorem tr_main_end : bitTreeScanner.tr stMain none work = halt 0 := rfl

/-- The pending count's carry passes a two, turning it into a one. -/
theorem tr_incCarry_two :
    bitTreeScanner.tr stIncCarry inSym ![some 2, t₁, t₂] =
      stay stIncCarry (some (some 1), 1) idle idle := rfl

/-- The pending count's carry is absorbed at a digit that is not a two, which
is raised, and the return begins. -/
theorem tr_incCarry_notTwo (hx : x = none ∨ x = some 0 ∨ x = some 1) :
    bitTreeScanner.tr stIncCarry inSym ![x, t₁, t₂] =
      stay stIncBack (some (some (raise x)), -1) idle idle := by
  rcases hx with rfl | rfl | rfl <;> rfl

/-- The pending count's return reaching the base marker consumes the pair
bit, stepping to the lowest digit. -/
theorem tr_incBack_base (b : Bool) :
    bitTreeScanner.tr stIncBack (some (boolEmb b)) ![some 3, t₁, t₂] =
      advance stMain (none, 1) idle idle := by
  cases b <;> rfl

/-- The pending count's return passes a digit. -/
theorem tr_incBack_digit (d : Redundant.Digit) :
    bitTreeScanner.tr stIncBack inSym ![some (digitEmb d), t₁, t₂] =
      stay stIncBack (none, -1) idle idle := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

end Main

section Leaf

/-- A zero of the gamma code under any symbol of the ruler: a mark is
written, the leaf head and the ruler head move right. -/
theorem tr_zeros_zero_some (hx : x ≠ none) :
    bitTreeScanner.tr stZeros (some (boolEmb false)) ![t₀, t₁, x] =
      advance stZeros idle (some (some 2), 1) (none, 1) := by
  match x with
  | none => exact absurd rfl hx
  | some 0 => rfl
  | some 1 => rfl
  | some 2 => rfl
  | some 3 => rfl

/-- A zero of the gamma code above the ruler's digits fails: the code is
longer than the input can hold. -/
theorem tr_zeros_zero_blank :
    bitTreeScanner.tr stZeros (some (boolEmb false)) ![t₀, t₁, none] =
      advance stDead idle idle idle := rfl

/-- The one of the gamma code writes the most significant digit and moves the
leaf head left. -/
theorem tr_zeros_one :
    bitTreeScanner.tr stZeros (some (boolEmb true)) work =
      advance stBits idle (some (some 1), -1) idle := rfl

/-- The zeros state at the input's end rejects. -/
theorem tr_zeros_end : bitTreeScanner.tr stZeros none work = halt 0 := rfl

/-- A digit of the gamma code over a mark is written and the leaf head and
the ruler head move left. -/
theorem tr_bits_mark (b : Bool) :
    bitTreeScanner.tr stBits (some (boolEmb b)) ![t₀, some 2, t₂] =
      advance stBits idle (some (some (boolEmb b)), -1) (none, -1) := by
  cases b <;> rfl

/-- The digits state over a mark at the input's end rejects. -/
theorem tr_bits_mark_end : bitTreeScanner.tr stBits none ![t₀, some 2, t₂] = halt 0 := rfl

/-- The digits state at the base marker: the digits are complete, and the
head moves to the lowest to begin the first decrement. -/
theorem tr_bits_base :
    bitTreeScanner.tr stBits inSym ![t₀, some 3, t₂] = stay stBorrowInit idle (none, 1) idle :=
  rfl

/-- A decrement borrows through a zero, in either phase. -/
theorem tr_borrowState_zero (first : Bool) :
    bitTreeScanner.tr (borrowState first) inSym ![t₀, some 0, t₂] =
      stay (borrowState first) idle (some (some 1), 1) idle := by
  cases first <;> rfl

/-- A decrement absorbs the borrow at a one and turns back, in either phase. -/
theorem tr_borrowState_one (first : Bool) :
    bitTreeScanner.tr (borrowState first) inSym ![t₀, some 1, t₂] =
      stay (returnState first) idle (some (some 0), -1) idle := by
  cases first <;> rfl

/-- A decrement's return passes a digit, in either phase. -/
theorem tr_returnState_digit (first : Bool) (b : Bool) :
    bitTreeScanner.tr (returnState first) inSym ![t₀, some (boolEmb b), t₂] =
      stay (returnState first) idle (none, -1) idle := by
  cases first <;> cases b <;> rfl

/-- The first decrement's return reaches the base marker and steps to the
lowest digit, where the countdown begins. -/
theorem tr_returnInit_base :
    bitTreeScanner.tr stReturnInit inSym ![t₀, some 3, t₂] = stay stBorrow idle (none, 1) idle :=
  rfl

/-- A decrement running into blank found the count at zero and turns back to
erase. -/
theorem tr_borrow_blank :
    bitTreeScanner.tr stBorrow inSym ![t₀, none, t₂] = stay stClear idle (none, -1) idle := rfl

/-- A decrement's return reaches the base marker and consumes the payload bit,
stepping to the lowest digit. -/
theorem tr_return_base_bit (b : Bool) :
    bitTreeScanner.tr stReturn (some (boolEmb b)) ![t₀, some 3, t₂] =
      advance stBorrow idle (none, 1) idle := by
  cases b <;> rfl

/-- A decrement's return reaching the base marker at the input's end rejects. -/
theorem tr_return_base_end : bitTreeScanner.tr stReturn none ![t₀, some 3, t₂] = halt 0 := rfl

/-- Erasure blanks a digit and moves left. -/
theorem tr_clear_digit (b : Bool) :
    bitTreeScanner.tr stClear inSym ![t₀, some (boolEmb b), t₂] =
      stay stClear idle (some none, -1) idle := by
  cases b <;> rfl

end Leaf

section Close

/-- Erasure reaching the base marker at an empty pending count closes the
last pending tree: the scan completes. -/
theorem tr_clear_base_blank :
    bitTreeScanner.tr stClear inSym ![none, some 3, t₂] = stay stDone idle idle idle := rfl

/-- Erasure reaching the base marker at a pending count whose lowest digit is
a two: the digit becomes a one, and the next tree is expected. -/
theorem tr_clear_base_two :
    bitTreeScanner.tr stClear inSym ![some 2, some 3, t₂] =
      stay stMain (some (some 1), 0) idle idle := rfl

/-- Erasure reaching the base marker at a pending count whose lowest digit is
a one: the digit becomes a zero, to be tested for being the top. -/
theorem tr_clear_base_one :
    bitTreeScanner.tr stClear inSym ![some 1, some 3, t₂] =
      stay stDecTop (some (some 0), 1) idle idle := rfl

/-- Erasure reaching the base marker at a pending count whose lowest digit is
a zero: the digit becomes a one and the borrow moves outward. -/
theorem tr_clear_base_zero :
    bitTreeScanner.tr stClear inSym ![some 0, some 3, t₂] =
      stay stDecBorrow (some (some 1), 1) idle idle := rfl

/-- The pending count's borrow passes a zero, turning it into a one. -/
theorem tr_decBorrow_zero :
    bitTreeScanner.tr stDecBorrow inSym ![some 0, t₁, t₂] =
      stay stDecBorrow (some (some 1), 1) idle idle := rfl

/-- The pending count's borrow is absorbed at a one, which becomes a zero, to
be tested for being the top. -/
theorem tr_decBorrow_one :
    bitTreeScanner.tr stDecBorrow inSym ![some 1, t₁, t₂] =
      stay stDecTop (some (some 0), 1) idle idle := rfl

/-- The pending count's borrow is absorbed at a two, which becomes a one, and
the return begins. -/
theorem tr_decBorrow_two :
    bitTreeScanner.tr stDecBorrow inSym ![some 2, t₁, t₂] =
      stay stDecBack (some (some 1), -1) idle idle := rfl

/-- The transition of the borrow's family at a zero, at either state. -/
theorem tr_decBorrowCfg_zero (j : ℕ) (inSym : Option (Fin 4)) :
    bitTreeScanner.tr (if j = 0 then stClear else stDecBorrow) inSym ![some 0, some 3, some 3] =
      stay stDecBorrow (some (some 1), 1) idle idle := by
  split_ifs
  · exact tr_clear_base_zero _ _
  · exact tr_decBorrow_zero _ _ _

/-- The transition of the borrow's family at a one, at either state. -/
theorem tr_decBorrowCfg_one (j : ℕ) (inSym : Option (Fin 4)) :
    bitTreeScanner.tr (if j = 0 then stClear else stDecBorrow) inSym ![some 1, some 3, some 3] =
      stay stDecTop (some (some 0), 1) idle idle := by
  split_ifs
  · exact tr_clear_base_one _ _
  · exact tr_decBorrow_one _ _ _

/-- The test above a lowered digit finds blank: the digit was the top and is
to be erased. -/
theorem tr_decTop_blank :
    bitTreeScanner.tr stDecTop inSym ![none, t₁, t₂] = stay stDecErase (none, -1) idle idle :=
  rfl

/-- The test above a lowered digit finds a digit: the return begins. -/
theorem tr_decTop_digit (d : Redundant.Digit) :
    bitTreeScanner.tr stDecTop inSym ![some (digitEmb d), t₁, t₂] =
      stay stDecBack (none, -1) idle idle := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- The erasing step blanks the lowered top digit and the return begins. -/
theorem tr_decErase :
    bitTreeScanner.tr stDecErase inSym work = stay stDecBack (some none, -1) idle idle := rfl

/-- The pending count's return reaching the base marker steps to the lowest
digit, and the next tree is expected. -/
theorem tr_decBack_base :
    bitTreeScanner.tr stDecBack inSym ![some 3, t₁, t₂] = stay stMain (none, 1) idle idle := rfl

/-- The pending count's return passes a digit. -/
theorem tr_decBack_digit (d : Redundant.Digit) :
    bitTreeScanner.tr stDecBack inSym ![some (digitEmb d), t₁, t₂] =
      stay stDecBack (none, -1) idle idle := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

end Close

section End

/-- A bit after completion fails, the leaf head stepping past the base
marker. -/
theorem tr_done_bit (b : Bool) :
    bitTreeScanner.tr stDone (some (boolEmb b)) work = advance stDead idle (none, 1) idle := by
  cases b <;> rfl

/-- Completion at the input's end accepts. -/
theorem tr_done_end : bitTreeScanner.tr stDone none work = halt 1 := rfl

/-- Failure absorbs a bit. -/
theorem tr_dead_bit (b : Bool) :
    bitTreeScanner.tr stDead (some (boolEmb b)) work = advance stDead idle idle idle := by
  cases b <;> rfl

/-- Failure at the input's end rejects. -/
theorem tr_dead_end : bitTreeScanner.tr stDead none work = halt 0 := rfl

end End

end Geb.BitTreeScanner
