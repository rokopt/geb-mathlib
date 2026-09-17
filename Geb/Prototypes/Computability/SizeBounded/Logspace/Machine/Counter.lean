/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Size
public import Geb.Prototypes.Computability.SizeBounded.Machine.Register
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Binary counters on a work tape

A counter holds a natural number in binary on a work tape, least significant
digit at cell {lit}`0`, with no leading zero, so that the number {lit}`0` is
the empty word and a zero test is one read of cell {lit}`0`. In the register
layout of {name}`Geb.SizeBounded.Machine.tapeOf`, whose cell {lit}`z` holds the
{lit}`z`th element of the word's reverse, the register word of the counter is
the reverse of its digit list. The increment turns a run of ones from the
least significant digit into zeros and the digit above them into a one; the
decrement turns a run of zeros into ones and the one above them into a zero,
erasing that digit when it was the most significant.

The digit list of a number is {lit}`ofNat`, the iterate of the increment from
the empty list, so that the increment of a counter holding {lit}`l` holds
{lit}`l + 1` by definition; the decrement of a counter holding {lit}`l + 1`
holds {lit}`l` because the decrement undoes the increment on a canonical list.
The length of the digit list is at most the binary size of the number, which
is what makes a counter bounded by the input's length occupy logarithmically
many cells.

# Main definitions

* {lit}`incL`, {lit}`decL` — the increment and the decrement of a digit list.
* {lit}`canon` — whether a digit list has no leading zero.
* {lit}`value`, {lit}`ofNat` — the number a digit list denotes, and the
  canonical digit list of a number.
* {lit}`counterWord` — the register word of a counter holding a number.

# Main statements

* {lit}`value_incL`, {lit}`canon_incL`, {lit}`decL_incL` — the increment adds
  one, keeps a list canonical, and is undone by the decrement.
* {lit}`value_ofNat`, {lit}`canon_ofNat`, {lit}`decL_ofNat_succ`,
  {lit}`ofNat_eq_nil_iff` — the canonical list of a number denotes it, is
  canonical, decrements to the predecessor's, and is empty exactly at zero.
* {lit}`length_ofNat_le_size` — the canonical list of a number is no longer
  than the number's binary size.
* {lit}`tapeOf_counterWord` — the cell of a counter register holds the
  corresponding digit.

# Tags

binary counter, increment, decrement, logspace, Turing machine
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

open Geb.SizeBounded.Machine (tapeOf)

public section

/-- The increment of a digit list, least significant digit first. -/
@[expose] def incL : List Bool → List Bool :=
  List.rec [true] fun b d ih ↦
    match b with
    | true => false :: ih
    | false => true :: d

/-- The increment of the empty list. -/
theorem incL_nil : incL [] = [true] := rfl

/-- The increment at a zero digit sets it. -/
theorem incL_cons_false (d : List Bool) : incL (false :: d) = true :: d := rfl

/-- The increment at a one digit clears it and carries. -/
theorem incL_cons_true (d : List Bool) : incL (true :: d) = false :: incL d := rfl

/-- The increment is never empty. -/
theorem incL_ne_nil : ∀ d : List Bool, incL d ≠ [] :=
  List.rec (List.cons_ne_nil _ _) fun b _ _ ↦ by
    cases b
    · rw [incL_cons_false]
      exact List.cons_ne_nil _ _
    · rw [incL_cons_true]
      exact List.cons_ne_nil _ _

/-- The decrement of a digit list, least significant digit first: the empty
list stays empty, a leading one becomes a zero or is erased when it is the
only digit, and a zero borrows. -/
@[expose] def decL : List Bool → List Bool :=
  List.rec [] fun b d ih ↦
    match b with
    | true =>
      match d with
      | [] => []
      | _ :: _ => false :: d
    | false => true :: ih

/-- The decrement of the empty list. -/
theorem decL_nil : decL [] = [] := rfl

/-- The decrement of a single one. -/
theorem decL_singleton_true : decL [true] = [] := rfl

/-- The decrement at a one digit above further digits clears it. -/
theorem decL_cons_true_cons (c : Bool) (d : List Bool) :
    decL (true :: c :: d) = false :: c :: d := rfl

/-- The decrement at a zero digit sets it and borrows. -/
theorem decL_cons_false (d : List Bool) : decL (false :: d) = true :: decL d := rfl

/-- Whether a digit list has no leading zero: its last digit is a one, or it is
empty. -/
@[expose] def canon : List Bool → Bool :=
  List.rec true fun b d ih ↦
    match d with
    | [] => b
    | _ :: _ => ih

/-- The empty list is canonical. -/
theorem canon_nil : canon [] = true := rfl

/-- A single digit is canonical exactly when it is a one. -/
theorem canon_singleton (b : Bool) : canon [b] = b := rfl

/-- A digit below further digits does not affect canonicity. -/
theorem canon_cons_cons (b c : Bool) (d : List Bool) : canon (b :: c :: d) = canon (c :: d) := rfl

/-- The number a digit list denotes. -/
@[expose] def value : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦ b.toNat + 2 * ih

/-- The empty list denotes zero. -/
theorem value_nil : value [] = 0 := rfl

/-- A digit list denotes its first digit plus twice the rest. -/
theorem value_cons (b : Bool) (d : List Bool) : value (b :: d) = b.toNat + 2 * value d := rfl

/-- The increment adds one. -/
theorem value_incL : ∀ d : List Bool, value (incL d) = value d + 1 :=
  List.rec rfl fun b d ih ↦ by
    cases b
    · rw [incL_cons_false, value_cons, value_cons]
      change 1 + 2 * value d = 0 + 2 * value d + 1
      omega
    · rw [incL_cons_true, value_cons, value_cons, ih]
      change 0 + 2 * (value d + 1) = 1 + 2 * value d + 1
      omega

/-- The increment keeps a list canonical. -/
theorem canon_incL : ∀ d : List Bool, canon d = true → canon (incL d) = true :=
  List.rec (fun _ ↦ rfl) fun b d ih h ↦ by
    cases d with
    | nil =>
      cases b
      · exact absurd h Bool.false_ne_true
      · rfl
    | cons c d' =>
      rw [canon_cons_cons] at h
      cases b
      · rw [incL_cons_false, canon_cons_cons]
        exact h
      · rw [incL_cons_true]
        obtain ⟨e, d'', he⟩ : ∃ e d'', incL (c :: d') = e :: d'' :=
          match hi : incL (c :: d') with
          | [] => absurd hi (incL_ne_nil _)
          | e :: d'' => ⟨e, d'', rfl⟩
        rw [he, canon_cons_cons, ← he]
        exact ih h

/-- The decrement undoes the increment on a canonical list. -/
theorem decL_incL : ∀ d : List Bool, canon d = true → decL (incL d) = d :=
  List.rec (fun _ ↦ rfl) fun b d ih h ↦ by
    cases d with
    | nil =>
      cases b
      · exact absurd h Bool.false_ne_true
      · rfl
    | cons c d' =>
      rw [canon_cons_cons] at h
      cases b
      · rfl
      · rw [incL_cons_true, decL_cons_false, ih h]

/-- The canonical digit list of a number: the iterate of the increment from the
empty list. -/
@[expose] def ofNat : ℕ → List Bool := Nat.rec [] fun _ ih ↦ incL ih

/-- The canonical list of zero is empty. -/
theorem ofNat_zero : ofNat 0 = [] := rfl

/-- The canonical list of a successor is the increment. -/
theorem ofNat_succ (l : ℕ) : ofNat (l + 1) = incL (ofNat l) := rfl

/-- The canonical list of a number denotes it. -/
theorem value_ofNat : ∀ l : ℕ, value (ofNat l) = l :=
  Nat.rec rfl fun l ih ↦ by rw [ofNat_succ, value_incL, ih]

/-- The canonical list of a number is canonical. -/
theorem canon_ofNat : ∀ l : ℕ, canon (ofNat l) = true :=
  Nat.rec rfl fun l ih ↦ by rw [ofNat_succ]; exact canon_incL _ ih

/-- The decrement of a successor's canonical list is the predecessor's. -/
theorem decL_ofNat_succ (l : ℕ) : decL (ofNat (l + 1)) = ofNat l :=
  decL_incL _ (canon_ofNat l)

/-- The canonical list of a number is empty exactly at zero. -/
theorem ofNat_eq_nil_iff (l : ℕ) : ofNat l = [] ↔ l = 0 := by
  cases l with
  | zero => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | succ l => exact ⟨fun h ↦ absurd h (incL_ne_nil _), fun h ↦ absurd h (Nat.succ_ne_zero l)⟩

/-- The canonical lists of two numbers are equal exactly when the numbers are. -/
theorem ofNat_inj {l l' : ℕ} (h : ofNat l = ofNat l') : l = l' := by
  have := congrArg value h
  rwa [value_ofNat, value_ofNat] at this

/-- A canonical nonempty list denotes at least the power of two of its length
less one. -/
theorem two_pow_pred_le_value : ∀ d : List Bool, canon d = true → d ≠ [] →
    2 ^ (d.length - 1) ≤ value d :=
  List.rec (fun _ h ↦ absurd rfl h) fun b d ih h _ ↦ by
    cases d with
    | nil =>
      cases b
      · exact absurd h Bool.false_ne_true
      · exact Nat.le_refl _
    | cons c d' =>
      rw [canon_cons_cons] at h
      have := ih h (List.cons_ne_nil _ _)
      rw [value_cons, List.length_cons, Nat.add_sub_cancel]
      rw [List.length_cons, Nat.add_sub_cancel] at this
      calc 2 ^ (d'.length + 1) = 2 * 2 ^ d'.length := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ b.toNat + 2 * value (c :: d') := by omega

/-- A canonical list is no longer than the binary size of the number it
denotes. -/
theorem length_le_size_value (d : List Bool) (h : canon d = true) :
    d.length ≤ Nat.size (value d) := by
  cases d with
  | nil => exact Nat.zero_le _
  | cons b d' =>
    have h2 := two_pow_pred_le_value (b :: d') h (List.cons_ne_nil _ _)
    have := Nat.lt_size.mpr h2
    rw [List.length_cons, Nat.add_sub_cancel] at this
    rw [List.length_cons]
    exact this

/-- The canonical list of a number is no longer than the number's binary
size. -/
theorem length_ofNat_le_size (l : ℕ) : (ofNat l).length ≤ Nat.size l := by
  have := length_le_size_value (ofNat l) (canon_ofNat l)
  rwa [value_ofNat] at this

/-- The register word of a counter holding {lit}`l`: the reverse of its digit
list, so that cell {lit}`z` of the register holds digit {lit}`z`. -/
@[expose] def counterWord (l : ℕ) : List Bool := (ofNat l).reverse

/-- The number a counter register holds, read off its word. -/
@[expose] def counterValue (w : List Bool) : ℕ := value w.reverse

/-- Reading the counter word of a number gives the number back. -/
theorem counterValue_counterWord (l : ℕ) : counterValue (counterWord l) = l := by
  unfold counterValue counterWord
  rw [List.reverse_reverse, value_ofNat]

/-- The counter word of a number is no longer than the number's binary size. -/
theorem length_counterWord_le_size (l : ℕ) : (counterWord l).length ≤ Nat.size l := by
  unfold counterWord
  rw [List.length_reverse]
  exact length_ofNat_le_size l

/-- The counter word is empty exactly at zero. -/
theorem counterWord_eq_nil_iff (l : ℕ) : counterWord l = [] ↔ l = 0 := by
  unfold counterWord
  rw [List.reverse_eq_nil_iff]
  exact ofNat_eq_nil_iff l

/-- A cell of a counter register holds the corresponding digit. -/
theorem tapeOf_counterWord (l : ℕ) (z : ℤ) :
    tapeOf (counterWord l) z = if 0 ≤ z then (ofNat l)[z.toNat]? else none := by
  unfold tapeOf counterWord
  rw [List.reverse_reverse]

end

end Geb.SizeBounded.Logspace
