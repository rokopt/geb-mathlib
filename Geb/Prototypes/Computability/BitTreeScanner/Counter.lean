/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Scan
meta import GebMeta  -- shake: keep; supplies the cite docstring role

set_option doc.verso true

/-!
# The redundant binary counter for the pending count

A counter over the digits {lit}`0`, {lit}`1` and {lit}`2`, least significant
first, in which an increment turns a run of twos into ones and raises the
digit above it, and a decrement turns a run of zeros into ones and lowers the
digit above it. This is the redundant binary number system of
{cite}`Okasaki1998` Chapter 9. A machine keeping a counter in this form on a
tape does a constant amount of work per operation amortised: each digit the
carry or the borrow passes was a two or a zero and becomes a one, so twice the
number of digits that are not one is a potential paying for every chain. The
ordinary binary counter has no such potential when increments and decrements
interleave, a count parked below a power of two paying a full chain for each
of a pair bit and a leaf's close in turn.

The counter keeps no leading zero: a decrement that turns the top digit into a
zero erases it instead. The count is then zero exactly when the counter is
empty, which a machine tests with one read, and the counter has at most as
many digits as the count has binary digits.

The pending count of {name}`Geb.BitTreeScanner.scanStep` is replayed in this form
alongside the scan: a pair bit increments, and a bit closing a leaf
decrements. The replay is what a machine's tape holds, and its invariant is
that it denotes the scan's count.

## Main definitions

* {lit}`Geb.BitTreeScanner.Redundant.Digit`, {lit}`Geb.BitTreeScanner.Redundant.value` —
  the digits and the number a digit list denotes.
* {lit}`Geb.BitTreeScanner.Redundant.inc`, {lit}`Geb.BitTreeScanner.Redundant.dec` — the
  increment and the decrement.
* {lit}`Geb.BitTreeScanner.Redundant.nlz` — whether the top digit is not a zero.
* {lit}`Geb.BitTreeScanner.Redundant.carryLength`,
  {lit}`Geb.BitTreeScanner.Redundant.borrowLength`,
  {lit}`Geb.BitTreeScanner.Redundant.nonOnes` — the lengths of a carry and of a
  borrow, and the number of digits that are not one, with their equations at
  each digit.
* {lit}`Geb.BitTreeScanner.closes`, {lit}`Geb.BitTreeScanner.treeStep`,
  {lit}`Geb.BitTreeScanner.runTree`, {lit}`Geb.BitTreeScanner.treeAt` — the replay of the
  pending count in the counter alongside the scan.
* {lit}`Geb.BitTreeScanner.GoodTree` — the replay's invariant.

## Main statements

* {lit}`Geb.BitTreeScanner.Redundant.value_inc`, {lit}`Geb.BitTreeScanner.Redundant.value_dec`
  — the increment and the decrement change the value by one.
* {lit}`Geb.BitTreeScanner.Redundant.nlz_inc`, {lit}`Geb.BitTreeScanner.Redundant.nlz_dec` —
  neither introduces a leading zero.
* {lit}`Geb.BitTreeScanner.Redundant.value_eq_zero_iff` — a counter without leading
  zero denotes zero exactly when empty.
* {lit}`Geb.BitTreeScanner.Redundant.length_le_bits_length` — a counter without
  leading zero has at most as many digits as its value has binary digits.
* {lit}`Geb.BitTreeScanner.Redundant.nonOnes_inc_add_carryLength_le`,
  {lit}`Geb.BitTreeScanner.Redundant.nonOnes_dec_add_borrowLength_le` — a carry or a
  borrow turns as many digits into ones as it passes, at most one digit
  becoming a two or a zero.
* {lit}`Geb.BitTreeScanner.scanStep_eq_close_of_closes` — a bit closing a leaf leaves
  the scan at the state the closed tree leaves.
* {lit}`Geb.BitTreeScanner.goodTree_treeStep`, {lit}`Geb.BitTreeScanner.goodTree_treeAt` —
  the replay denotes the scan's count.

## Implementation notes

The increment and the decrement are each a {name}`List.foldr` into a function
of a flag, the pending carry or borrow, as {name}`Geb.BitTreeScanner.decList` is, so
that they compile and their equations at each head digit hold by {lit}`rfl`;
the decrement's case at a one inspects the rest for emptiness, which is where
the leading zero is erased. Digits are {lit}`Fin 3`, matched at the three
literals, and the canonical form's test is a {name}`decide` rather than
{lit}`!=`, whose {lit}`LawfulBEq` instance at {lit}`Fin` depends on
{lit}`Classical.choice`.

## References

* {cite}`Okasaki1998`

## Tags

binary counter, redundant number system, amortised analysis, pending count
-/

@[expose] public section

namespace Geb.BitTreeScanner

namespace Redundant

/-- A digit of the counter: zero, one or two. -/
abbrev Digit : Type := Fin 3

/-- The number a digit list denotes, least significant digit first. -/
def value (l : List Digit) : ℕ := l.foldr (fun d n ↦ d.val + 2 * n) 0

/-- The empty counter denotes zero. -/
@[simp] theorem value_nil : value [] = 0 := rfl

/-- A counter denotes its head plus twice its tail's value. -/
@[simp] theorem value_cons (d : Digit) (l : List Digit) : value (d :: l) = d.val + 2 * value l :=
  rfl

/-- One digit of the increment, given the rest as a function of whether a
carry is pending: without one the digit passes; with one a zero or a one is
raised and a two becomes a one and carries on. -/
def incStep (d : Digit) (k : Bool → List Digit) (carry : Bool) : List Digit :=
  cond carry (match d with | 0 => 1 :: k false | 1 => 2 :: k false | 2 => 1 :: k true)
    (d :: k false)

/-- The increment as a function of whether a carry is pending; a carry past the
top digit becomes a new top one. -/
def incAux (l : List Digit) : Bool → List Digit := l.foldr incStep fun carry ↦ cond carry [1] []

/-- The increment. -/
def inc (l : List Digit) : List Digit := incAux l true

/-- Without a carry the digits pass. -/
theorem incAux_false (l : List Digit) : incAux l false = l :=
  List.rec (motive := fun l ↦ incAux l false = l) rfl
    (fun d _ ih ↦ by
      change d :: incAux _ false = d :: _
      rw [ih]) l

/-- The increment of the empty counter. -/
@[simp] theorem inc_nil : inc [] = [1] := rfl

/-- A zero at the bottom becomes a one. -/
@[simp] theorem inc_cons_zero (l : List Digit) : inc (0 :: l) = 1 :: l := by
  change 1 :: incAux l false = _
  rw [incAux_false]

/-- A one at the bottom becomes a two. -/
@[simp] theorem inc_cons_one (l : List Digit) : inc (1 :: l) = 2 :: l := by
  change 2 :: incAux l false = _
  rw [incAux_false]

/-- A two at the bottom becomes a one and the carry propagates. -/
@[simp] theorem inc_cons_two (l : List Digit) : inc (2 :: l) = 1 :: inc l := rfl

/-- One digit of the decrement, given the rest as a function of whether a
borrow is pending: without one the digit passes; with one a two becomes a one,
a zero becomes a one and borrows on, and a one becomes a zero, or is erased
when it is the top digit. -/
def decStep (d : Digit) (k : Bool → List Digit) (borrow : Bool) : List Digit :=
  cond borrow
    (match d with
      | 0 => 1 :: k true
      | 1 => (match k false with | [] => [] | r => 0 :: r)
      | 2 => 1 :: k false)
    (d :: k false)

/-- The decrement as a function of whether a borrow is pending; a borrow past
the top digit is dropped, the empty counter denoting zero. -/
def decAux (l : List Digit) : Bool → List Digit := l.foldr decStep fun _ ↦ []

/-- The decrement. -/
def dec (l : List Digit) : List Digit := decAux l true

/-- Without a borrow the digits pass. -/
theorem decAux_false (l : List Digit) : decAux l false = l :=
  List.rec (motive := fun l ↦ decAux l false = l) rfl
    (fun d _ ih ↦ by
      change d :: decAux _ false = d :: _
      rw [ih]) l

/-- The decrement of the empty counter. -/
@[simp] theorem dec_nil : dec [] = [] := rfl

/-- A zero at the bottom becomes a one and the borrow propagates. -/
@[simp] theorem dec_cons_zero (l : List Digit) : dec (0 :: l) = 1 :: dec l := rfl

/-- A two at the bottom becomes a one. -/
@[simp] theorem dec_cons_two (l : List Digit) : dec (2 :: l) = 1 :: l := by
  change 1 :: decAux l false = _
  rw [decAux_false]

/-- A lone one is erased. -/
@[simp] theorem dec_singleton_one : dec [1] = [] := rfl

/-- A one at the bottom of more digits becomes a zero. -/
@[simp] theorem dec_cons_one_cons (e : Digit) (l : List Digit) :
    dec (1 :: e :: l) = 0 :: e :: l := by
  change (match decAux (e :: l) false with | [] => [] | r => 0 :: r) = _
  rw [decAux_false]

/-- Whether the top digit is not a zero: the counter's canonical form. -/
def nlz (l : List Digit) : Bool := l.getLast?.all fun d ↦ decide (d ≠ 0)

/-- The empty counter has no leading zero. -/
@[simp] theorem nlz_nil : nlz [] = true := rfl

/-- A single digit is a leading zero exactly when it is zero. -/
@[simp] theorem nlz_singleton (d : Digit) : nlz [d] = decide (d ≠ 0) := rfl

/-- The top digit of a longer counter is its tail's. -/
@[simp] theorem nlz_cons_cons (d e : Digit) (l : List Digit) :
    nlz (d :: e :: l) = nlz (e :: l) := by
  rw [nlz, nlz, List.getLast?_cons_cons]

/-- The increment is never empty. -/
theorem inc_ne_nil (l : List Digit) : inc l ≠ [] := by
  cases l with
  | nil => rw [inc_nil]; exact List.cons_ne_nil _ _
  | cons d l =>
    match d with
    | 0 => rw [inc_cons_zero]; exact List.cons_ne_nil _ _
    | 1 => rw [inc_cons_one]; exact List.cons_ne_nil _ _
    | 2 => rw [inc_cons_two]; exact List.cons_ne_nil _ _

/-- The increment raises the value by one. -/
theorem value_inc (l : List Digit) : value (inc l) = value l + 1 :=
  List.rec (motive := fun l ↦ value (inc l) = value l + 1) rfl
    (fun d l ih ↦ by
      match d with
      | 0 =>
        rw [inc_cons_zero, value_cons, value_cons]
        change 1 + 2 * value l = 0 + 2 * value l + 1
        omega
      | 1 =>
        rw [inc_cons_one, value_cons, value_cons]
        change 2 + 2 * value l = 1 + 2 * value l + 1
        omega
      | 2 =>
        rw [inc_cons_two, value_cons, value_cons, ih]
        change 1 + 2 * (value l + 1) = 2 + 2 * value l + 1
        omega) l

/-- A counter with no leading zero and a zero at the bottom has more digits. -/
theorem ne_nil_of_nlz_cons_zero (l : List Digit) (h : nlz (0 :: l) = true) : l ≠ [] := by
  intro hl
  subst hl
  exact nomatch h

/-- The tail of a counter with no leading zero and more than one digit has no
leading zero. -/
theorem nlz_of_nlz_cons (d : Digit) (l : List Digit) (h : nlz (d :: l) = true) (hl : l ≠ []) :
    nlz l = true := by
  cases l with
  | nil => exact absurd rfl hl
  | cons e l => rw [nlz_cons_cons] at h; exact h

/-- The decrement of a nonempty counter with no leading zero lowers the value
by one. -/
theorem value_dec (l : List Digit) (hn : nlz l = true) (h : l ≠ []) : value (dec l) + 1 = value l :=
  List.rec (motive := fun l ↦ nlz l = true → l ≠ [] → value (dec l) + 1 = value l)
    (fun _ h ↦ absurd rfl h)
    (fun d l ih hn _ ↦ by
      match d with
      | 0 =>
        have hl := ne_nil_of_nlz_cons_zero l hn
        have := ih (nlz_of_nlz_cons 0 l hn hl) hl
        rw [dec_cons_zero, value_cons, value_cons]
        change 1 + 2 * value (dec l) + 1 = 0 + 2 * value l
        omega
      | 1 =>
        cases l with
        | nil => rfl
        | cons e l =>
          rw [dec_cons_one_cons, value_cons, value_cons]
          change 0 + 2 * value (e :: l) + 1 = 1 + 2 * value (e :: l)
          omega
      | 2 =>
        rw [dec_cons_two, value_cons, value_cons]
        change 1 + 2 * value l + 1 = 2 + 2 * value l
        omega) l hn h

/-- The increment introduces no leading zero. -/
theorem nlz_inc (l : List Digit) (hn : nlz l = true) : nlz (inc l) = true :=
  List.rec (motive := fun l ↦ nlz l = true → nlz (inc l) = true) (fun _ ↦ rfl)
    (fun d l ih hn ↦ by
      match d with
      | 0 =>
        rw [inc_cons_zero]
        cases l with
        | nil => rfl
        | cons e l => rw [nlz_cons_cons] at hn ⊢; exact hn
      | 1 =>
        rw [inc_cons_one]
        cases l with
        | nil => rfl
        | cons e l => rw [nlz_cons_cons] at hn ⊢; exact hn
      | 2 =>
        rw [inc_cons_two]
        obtain ⟨e, r, hr⟩ : ∃ e r, inc l = e :: r := by
          cases hi : inc l with
          | nil => exact absurd hi (inc_ne_nil l)
          | cons e r => exact ⟨e, r, rfl⟩
        rw [hr, nlz_cons_cons, ← hr]
        cases l with
        | nil => rfl
        | cons e' l => rw [nlz_cons_cons] at hn; exact ih hn) l hn

/-- The decrement introduces no leading zero. -/
theorem nlz_dec (l : List Digit) (hn : nlz l = true) : nlz (dec l) = true :=
  List.rec (motive := fun l ↦ nlz l = true → nlz (dec l) = true) (fun _ ↦ rfl)
    (fun d l ih hn ↦ by
      match d with
      | 0 =>
        have hl := ne_nil_of_nlz_cons_zero l hn
        have := ih (nlz_of_nlz_cons 0 l hn hl)
        rw [dec_cons_zero]
        cases hd : dec l with
        | nil => rfl
        | cons e r => rw [nlz_cons_cons, ← hd]; exact this
      | 1 =>
        cases l with
        | nil => rfl
        | cons e l => rw [dec_cons_one_cons, nlz_cons_cons]; rw [nlz_cons_cons] at hn; exact hn
      | 2 =>
        rw [dec_cons_two]
        cases l with
        | nil => rfl
        | cons e l => rw [nlz_cons_cons]; rw [nlz_cons_cons] at hn; exact hn) l hn

/-- A counter with no leading zero denotes zero exactly when it is empty. -/
theorem value_eq_zero_iff (l : List Digit) (hn : nlz l = true) : value l = 0 ↔ l = [] :=
  List.rec (motive := fun l ↦ nlz l = true → (value l = 0 ↔ l = []))
    (fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩)
    (fun d l ih hn ↦ by
      refine ⟨fun h ↦ ?_, fun h ↦ nomatch h⟩
      rw [value_cons] at h
      have hd : d.val = 0 := by omega
      have hv : value l = 0 := by omega
      have hd0 : d = 0 := Fin.ext hd
      subst hd0
      have hl := ne_nil_of_nlz_cons_zero l hn
      exact absurd ((ih (nlz_of_nlz_cons 0 l hn hl)).mp hv) hl) l hn

/-- A nonempty counter with no leading zero denotes at least the power of two
below its digit count. -/
theorem two_pow_le_value (l : List Digit) (hn : nlz l = true) (h : l ≠ []) :
    2 ^ (l.length - 1) ≤ value l :=
  List.rec (motive := fun l ↦ nlz l = true → l ≠ [] → 2 ^ (l.length - 1) ≤ value l)
    (fun _ h ↦ absurd rfl h)
    (fun d l ih hn _ ↦ by
      cases l with
      | nil =>
        rw [nlz_singleton, decide_eq_true_iff] at hn
        rw [List.length_singleton, Nat.sub_self, Nat.pow_zero, value_cons, value_nil]
        have : d.val ≠ 0 := fun h ↦ hn (Fin.ext h)
        omega
      | cons e l =>
        rw [nlz_cons_cons] at hn
        have := ih hn (List.cons_ne_nil e l)
        rw [List.length_cons, Nat.add_sub_cancel] at this
        rw [List.length_cons, Nat.add_sub_cancel, value_cons, List.length_cons, Nat.pow_succ]
        omega) l hn h

/-- A counter with no leading zero has at most as many digits as its value has
binary digits. -/
theorem length_le_bits_length (l : List Digit) (hn : nlz l = true) :
    l.length ≤ (value l).bits.length := by
  cases l with
  | nil => exact Nat.zero_le _
  | cons d l =>
    refine Nat.le_of_not_lt fun hlt ↦ ?_
    have h1 := (bits_length_le_iff (value (d :: l)) ((d :: l).length - 1)).mp (by omega)
    have h2 := two_pow_le_value (d :: l) hn (List.cons_ne_nil d l)
    omega

/-- The length of a carry: the run of twos at the bottom. -/
def carryLength (l : List Digit) : ℕ := l.foldr (fun d n ↦ if d = 2 then n + 1 else 0) 0

/-- The length of a borrow: the run of zeros at the bottom. -/
def borrowLength (l : List Digit) : ℕ := l.foldr (fun d n ↦ if d = 0 then n + 1 else 0) 0

/-- The number of digits that are not one: the potential a chain draws down. -/
def nonOnes (l : List Digit) : ℕ := l.foldr (fun d n ↦ if d = 1 then n else n + 1) 0

/-- The carry's length at the empty counter. -/
@[simp] theorem carryLength_nil : carryLength [] = 0 := rfl

/-- The borrow's length at the empty counter. -/
@[simp] theorem borrowLength_nil : borrowLength [] = 0 := rfl

/-- No digit is not one at the empty counter. -/
@[simp] theorem nonOnes_nil : nonOnes [] = 0 := rfl

/-- The carry passes a two. -/
@[simp] theorem carryLength_cons_two (l : List Digit) : carryLength (2 :: l) = carryLength l + 1 :=
  rfl

/-- The carry stops at a zero. -/
@[simp] theorem carryLength_cons_zero (l : List Digit) : carryLength (0 :: l) = 0 := rfl

/-- The carry stops at a one. -/
@[simp] theorem carryLength_cons_one (l : List Digit) : carryLength (1 :: l) = 0 := rfl

/-- The borrow passes a zero. -/
@[simp] theorem borrowLength_cons_zero (l : List Digit) :
    borrowLength (0 :: l) = borrowLength l + 1 := rfl

/-- The borrow stops at a one. -/
@[simp] theorem borrowLength_cons_one (l : List Digit) : borrowLength (1 :: l) = 0 := rfl

/-- The borrow stops at a two. -/
@[simp] theorem borrowLength_cons_two (l : List Digit) : borrowLength (2 :: l) = 0 := rfl

/-- A zero is not one. -/
@[simp] theorem nonOnes_cons_zero (l : List Digit) : nonOnes (0 :: l) = nonOnes l + 1 := rfl

/-- A one is one. -/
@[simp] theorem nonOnes_cons_one (l : List Digit) : nonOnes (1 :: l) = nonOnes l := rfl

/-- A two is not one. -/
@[simp] theorem nonOnes_cons_two (l : List Digit) : nonOnes (2 :: l) = nonOnes l + 1 := rfl

/-- A carry turns as many digits into ones as it passes, at most one digit
becoming a two. -/
theorem nonOnes_inc_add_carryLength_le (l : List Digit) :
    nonOnes (inc l) + carryLength l ≤ nonOnes l + 1 :=
  List.rec (motive := fun l ↦ nonOnes (inc l) + carryLength l ≤ nonOnes l + 1) (by decide)
    (fun d l ih ↦ by
      match d with
      | 0 => rw [inc_cons_zero, nonOnes_cons_one, nonOnes_cons_zero, carryLength_cons_zero]; omega
      | 1 => rw [inc_cons_one, nonOnes_cons_two, nonOnes_cons_one, carryLength_cons_one]
      | 2 => rw [inc_cons_two, nonOnes_cons_one, nonOnes_cons_two, carryLength_cons_two]; omega) l

/-- A borrow turns as many digits into ones as it passes, at most one digit
becoming a zero. -/
theorem nonOnes_dec_add_borrowLength_le (l : List Digit) :
    nonOnes (dec l) + borrowLength l ≤ nonOnes l + 1 :=
  List.rec (motive := fun l ↦ nonOnes (dec l) + borrowLength l ≤ nonOnes l + 1) (by decide)
    (fun d l ih ↦ by
      match d with
      | 0 => rw [dec_cons_zero, nonOnes_cons_one, nonOnes_cons_zero, borrowLength_cons_zero]; omega
      | 1 =>
        cases l with
        | nil => decide
        | cons e l =>
          rw [dec_cons_one_cons, nonOnes_cons_zero, nonOnes_cons_one, borrowLength_cons_one]
      | 2 => rw [dec_cons_two, nonOnes_cons_one, nonOnes_cons_two, borrowLength_cons_two]; omega) l

/-- The carry is at most the whole counter. -/
theorem carryLength_le_length (l : List Digit) : carryLength l ≤ l.length :=
  List.rec (motive := fun l ↦ carryLength l ≤ l.length) le_rfl
    (fun d l ih ↦ by
      rw [List.length_cons]
      match d with
      | 0 => rw [carryLength_cons_zero]; omega
      | 1 => rw [carryLength_cons_one]; omega
      | 2 => rw [carryLength_cons_two]; omega) l

/-- The borrow is at most the whole counter. -/
theorem borrowLength_le_length (l : List Digit) : borrowLength l ≤ l.length :=
  List.rec (motive := fun l ↦ borrowLength l ≤ l.length) le_rfl
    (fun d l ih ↦ by
      rw [List.length_cons]
      match d with
      | 0 => rw [borrowLength_cons_zero]; omega
      | 1 => rw [borrowLength_cons_one]; omega
      | 2 => rw [borrowLength_cons_two]; omega) l

/-- Below the carry's length a digit is a two. -/
theorem getD_of_lt_carryLength (l : List Digit) : ∀ i, i < carryLength l → l.getD i 0 = 2 :=
  List.rec (motive := fun l ↦ ∀ i, i < carryLength l → l.getD i 0 = 2)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun d l ih i hi ↦ by
      match d with
      | 0 => rw [carryLength_cons_zero] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 1 => rw [carryLength_cons_one] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 2 =>
        cases i with
        | zero => rfl
        | succ i => rw [carryLength_cons_two] at hi; exact ih i (by omega)) l

/-- At the carry's length the digit is not a two. -/
theorem getD_carryLength_ne_two (l : List Digit) : l.getD (carryLength l) 0 ≠ 2 :=
  List.rec (motive := fun l ↦ l.getD (carryLength l) 0 ≠ 2) (by decide)
    (fun d l ih ↦ by
      match d with
      | 0 => rw [carryLength_cons_zero, List.getD_cons_zero]; decide
      | 1 => rw [carryLength_cons_one, List.getD_cons_zero]; decide
      | 2 => rw [carryLength_cons_two, List.getD_cons_succ]; exact ih) l

/-- Below the borrow's length a digit is a zero. -/
theorem getD_of_lt_borrowLength (l : List Digit) : ∀ i, i < borrowLength l → l.getD i 0 = 0 :=
  List.rec (motive := fun l ↦ ∀ i, i < borrowLength l → l.getD i 0 = 0)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun d l ih i hi ↦ by
      match d with
      | 0 =>
        cases i with
        | zero => rfl
        | succ i => rw [borrowLength_cons_zero] at hi; exact ih i (by omega)
      | 1 => rw [borrowLength_cons_one] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 2 => rw [borrowLength_cons_two] at hi; exact absurd hi (Nat.not_lt_zero _)) l

/-- The increment lengthens the counter exactly when the carry runs through
every digit. -/
theorem length_inc (l : List Digit) : (inc l).length = max l.length (carryLength l + 1) :=
  List.rec (motive := fun l ↦ (inc l).length = max l.length (carryLength l + 1)) rfl
    (fun d l ih ↦ by
      rw [List.length_cons]
      match d with
      | 0 => rw [inc_cons_zero, carryLength_cons_zero, List.length_cons]; omega
      | 1 => rw [inc_cons_one, carryLength_cons_one, List.length_cons]; omega
      | 2 => rw [inc_cons_two, carryLength_cons_two, List.length_cons, ih]; omega) l

/-- The increment turns the digits below the carry's length into ones. -/
theorem getD_inc_of_lt (l : List Digit) : ∀ i, i < carryLength l → (inc l).getD i 0 = 1 :=
  List.rec (motive := fun l ↦ ∀ i, i < carryLength l → (inc l).getD i 0 = 1)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun d l ih i hi ↦ by
      match d with
      | 0 => rw [carryLength_cons_zero] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 1 => rw [carryLength_cons_one] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 2 =>
        rw [inc_cons_two]
        cases i with
        | zero => rfl
        | succ i => rw [carryLength_cons_two] at hi; exact ih i (by omega)) l

/-- The increment raises the digit at the carry's length: a one becomes a two,
a zero or the blank above the top a one. -/
theorem getD_inc_carryLength (l : List Digit) :
    (inc l).getD (carryLength l) 0 = if l.getD (carryLength l) 0 = 1 then 2 else 1 :=
  List.rec (motive := fun l ↦
      (inc l).getD (carryLength l) 0 = if l.getD (carryLength l) 0 = 1 then 2 else 1) rfl
    (fun d l ih ↦ by
      match d with
      | 0 => rfl
      | 1 => rfl
      | 2 =>
        rw [inc_cons_two, carryLength_cons_two, List.getD_cons_succ, List.getD_cons_succ, ih]) l

/-- The increment leaves the digits above the carry's length. -/
theorem getD_inc_of_gt (l : List Digit) :
    ∀ i, carryLength l < i → (inc l).getD i 0 = l.getD i 0 :=
  List.rec (motive := fun l ↦ ∀ i, carryLength l < i → (inc l).getD i 0 = l.getD i 0)
    (fun i hi ↦ by
      rw [inc_nil]
      cases i with
      | zero => exact absurd hi (Nat.lt_irrefl 0)
      | succ i => rfl)
    (fun d l ih i hi ↦ by
      match d with
      | 0 =>
        rw [inc_cons_zero]
        cases i with
        | zero => rw [carryLength_cons_zero] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i => rfl
      | 1 =>
        rw [inc_cons_one]
        cases i with
        | zero => rw [carryLength_cons_one] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i => rfl
      | 2 =>
        rw [inc_cons_two]
        cases i with
        | zero => rw [carryLength_cons_two] at hi; exact absurd hi (Nat.not_lt_zero _)
        | succ i => rw [carryLength_cons_two] at hi; exact ih i (by omega)) l

/-- The decrement shortens the counter exactly when a one at the top absorbs
the borrow. -/
theorem length_dec (l : List Digit) :
    (dec l).length =
      if l.getD (borrowLength l) 0 = 1 ∧ borrowLength l + 1 = l.length then l.length - 1
      else l.length :=
  List.rec (motive := fun l ↦ (dec l).length =
      if l.getD (borrowLength l) 0 = 1 ∧ borrowLength l + 1 = l.length then l.length - 1
      else l.length) rfl
    (fun d l ih ↦ by
      match d with
      | 0 =>
        rw [dec_cons_zero, borrowLength_cons_zero, List.getD_cons_succ, List.length_cons,
          List.length_cons, ih]
        have := borrowLength_le_length l
        by_cases h : l.getD (borrowLength l) 0 = 1 ∧ borrowLength l + 1 = l.length
        · rw [ite_eq_left h, ite_eq_left ⟨h.1, by omega⟩]
          omega
        · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h ⟨h'.1, by omega⟩)]
      | 1 =>
        cases l with
        | nil => rfl
        | cons e l =>
          rw [dec_cons_one_cons, borrowLength_cons_one]
          simp only [List.length_cons]
          rw [ite_eq_right (fun h ↦ by omega)]
      | 2 =>
        rw [dec_cons_two, borrowLength_cons_two, ite_eq_right (fun h ↦ nomatch h.1)]
        simp only [List.length_cons]) l

/-- The decrement turns the digits below the borrow's length into ones. -/
theorem getD_dec_of_lt (l : List Digit) : ∀ i, i < borrowLength l → (dec l).getD i 0 = 1 :=
  List.rec (motive := fun l ↦ ∀ i, i < borrowLength l → (dec l).getD i 0 = 1)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun d l ih i hi ↦ by
      match d with
      | 0 =>
        rw [dec_cons_zero]
        cases i with
        | zero => rfl
        | succ i => rw [borrowLength_cons_zero] at hi; exact ih i (by omega)
      | 1 => rw [borrowLength_cons_one] at hi; exact absurd hi (Nat.not_lt_zero _)
      | 2 => rw [borrowLength_cons_two] at hi; exact absurd hi (Nat.not_lt_zero _)) l

/-- The decrement lowers the digit at the borrow's length: a two becomes a
one, and a one a zero, or blank when it was the top. -/
theorem getD_dec_borrowLength (l : List Digit) :
    (dec l).getD (borrowLength l) 0 = if l.getD (borrowLength l) 0 = 2 then 1 else 0 :=
  List.rec (motive := fun l ↦
      (dec l).getD (borrowLength l) 0 = if l.getD (borrowLength l) 0 = 2 then 1 else 0) rfl
    (fun d l ih ↦ by
      match d with
      | 0 =>
        rw [dec_cons_zero, borrowLength_cons_zero, List.getD_cons_succ, List.getD_cons_succ, ih]
      | 1 =>
        cases l with
        | nil => rfl
        | cons e l => rfl
      | 2 => rfl) l

/-- The decrement leaves the digits above the borrow's length. -/
theorem getD_dec_of_gt (l : List Digit) :
    ∀ i, borrowLength l < i → (dec l).getD i 0 = l.getD i 0 :=
  List.rec (motive := fun l ↦ ∀ i, borrowLength l < i → (dec l).getD i 0 = l.getD i 0)
    (fun _ _ ↦ rfl)
    (fun d l ih i hi ↦ by
      match d with
      | 0 =>
        rw [dec_cons_zero]
        cases i with
        | zero => rw [borrowLength_cons_zero] at hi; exact absurd hi (Nat.not_lt_zero _)
        | succ i => rw [borrowLength_cons_zero] at hi; exact ih i (by omega)
      | 1 =>
        cases i with
        | zero => rw [borrowLength_cons_one] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i =>
          cases l with
          | nil => rfl
          | cons e l => rw [dec_cons_one_cons]; rfl
      | 2 =>
        rw [dec_cons_two]
        cases i with
        | zero => rw [borrowLength_cons_two] at hi; exact absurd hi (Nat.lt_irrefl 0)
        | succ i => rfl) l

end Redundant

section Replay

open Redundant

variable (W : ℕ)

/-- Whether a bit closes a leaf: read inside one, it leaves the scan expecting
a tree or complete. -/
def closes (s : Scan) (b : Bool) : Bool :=
  decide (s.mode ≠ .term ∧ ((scanStep W s b).mode = .term ∨ (scanStep W s b).mode = .done))

/-- The counter's step alongside the scan's: a pair bit increments, a bit
closing a leaf decrements, any other bit leaves it. -/
def treeStep (s : Scan) (b : Bool) (l : List Digit) : List Digit :=
  if s.mode = .term ∧ b = true then inc l else if closes W s b then dec l else l

/-- The scan with the counter: the state and the counter so far. -/
def runTree (w : List Bool) (p : Scan × List Digit) : Scan × List Digit :=
  w.foldl (fun p b ↦ (scanStep W p.1 b, treeStep W p.1 b p.2)) p

/-- The counter after a word, from the initial state and the empty counter. -/
def treeAt (w : List Bool) : List Digit := (runTree W w (init, [])).2

/-- The scan with the counter reads the empty word as nothing. -/
@[simp] theorem runTree_nil (p : Scan × List Digit) : runTree W [] p = p := rfl

/-- The scan with the counter reads the head bit first. -/
@[simp] theorem runTree_cons (b : Bool) (w : List Bool) (p : Scan × List Digit) :
    runTree W (b :: w) p = runTree W w (scanStep W p.1 b, treeStep W p.1 b p.2) := rfl

/-- The scan with the counter reads a concatenation's earlier part first. -/
theorem runTree_append (u v : List Bool) (p : Scan × List Digit) :
    runTree W (u ++ v) p = runTree W v (runTree W u p) := List.foldl_append

/-- The scan with the counter carries the scan. -/
theorem runTree_fst (w : List Bool) :
    ∀ p : Scan × List Digit, (runTree W w p).1 = scanFrom W w p.1 :=
  List.rec (motive := fun w ↦ ∀ p : Scan × List Digit, (runTree W w p).1 = scanFrom W w p.1)
    (fun _ ↦ rfl) (fun b _ ih p ↦ by rw [runTree_cons, ih, scanFrom_cons]) w

/-- The counter after a prefix extended by one bit is the counter's step at the
prefix's state. -/
theorem treeAt_take_succ (w : List Bool) (k : ℕ) (h : k < w.length) :
    treeAt W (w.take (k + 1)) = treeStep W (scanAt W (w.take k)) w[k] (treeAt W (w.take k)) := by
  rw [List.take_succ_eq_append_getElem h, treeAt, runTree_append, runTree_cons, runTree_nil,
    runTree_fst]
  rfl

/-- The replay's invariant: the counter has no leading zero and denotes the
scan's pending count. -/
def GoodTree (s : Scan) (l : List Digit) : Prop := nlz l = true ∧ value l = s.count

/-- The invariant holds initially. -/
theorem goodTree_init : GoodTree init [] := ⟨rfl, rfl⟩

/-- A bit closing a leaf leaves the scan at the state the closed tree leaves. -/
theorem scanStep_eq_close_of_closes (s : Scan) (b : Bool) (h : closes W s b = true) :
    scanStep W s b = close s.count := by
  rw [closes, decide_eq_true_iff] at h
  obtain ⟨hm, hmode⟩ := h
  obtain ⟨m, c, wd, d⟩ := s
  cases m with
  | term => exact absurd rfl hm
  | zeros =>
    cases b with
    | false =>
      by_cases hW : W < wd
      · rw [scanStep_zeros_false_of_lt W _ _ _ hW] at hmode
        obtain h | h := hmode <;> exact nomatch h
      · rw [scanStep_zeros_false W _ _ _ (by omega)] at hmode
        obtain h | h := hmode <;> exact nomatch h
    | true =>
      rw [scanStep_zeros_true] at hmode ⊢
      rw [settleDigits] at hmode ⊢
      by_cases hfull : [true].length = wd + 1
      · rw [ite_eq_left hfull] at hmode ⊢
        rw [settleCount] at hmode ⊢
        cases hf : allFalse (decList [true]) with
        | true => rfl
        | false =>
          rw [hf] at hmode
          obtain h | h := hmode <;> exact nomatch h
      · rw [ite_eq_right hfull] at hmode
        obtain h | h := hmode <;> exact nomatch h
  | bits =>
    rw [scanStep_bits] at hmode ⊢
    rw [settleDigits] at hmode ⊢
    by_cases hfull : (b :: d).length = wd
    · rw [ite_eq_left hfull] at hmode ⊢
      rw [settleCount] at hmode ⊢
      cases hf : allFalse (decList (b :: d)) with
      | true => rfl
      | false =>
        rw [hf] at hmode
        obtain h | h := hmode <;> exact nomatch h
    · rw [ite_eq_right hfull] at hmode
      obtain h | h := hmode <;> exact nomatch h
  | count =>
    rw [scanStep_count] at hmode ⊢
    rw [settleCount] at hmode ⊢
    cases hf : allFalse (decList d) with
    | true => rfl
    | false =>
      rw [hf] at hmode
      obtain h | h := hmode <;> exact nomatch h
  | done =>
    rw [scanStep_done] at hmode
    obtain h | h := hmode <;> exact nomatch h
  | dead =>
    rw [scanStep_dead] at hmode
    obtain h | h := hmode <;> exact nomatch h

/-- A bit not closing a leaf and not a pair bit leaves the pending count. -/
theorem count_scanStep_of_not_closes (s : Scan) (b : Bool) (hm : ¬ (s.mode = .term ∧ b = true))
    (h : closes W s b = false) : (scanStep W s b).count = s.count := by
  rw [closes, decide_eq_false_iff_not] at h
  obtain ⟨m, c, wd, d⟩ := s
  cases m with
  | term =>
    cases b with
    | true => exact absurd ⟨rfl, rfl⟩ hm
    | false => rfl
  | zeros =>
    cases b with
    | false =>
      by_cases hW : W < wd
      · rw [scanStep_zeros_false_of_lt W _ _ _ hW]
      · rw [scanStep_zeros_false W _ _ _ (by omega)]
    | true =>
      rw [scanStep_zeros_true, settleDigits] at h ⊢
      by_cases hfull : [true].length = wd + 1
      · rw [ite_eq_left hfull] at h ⊢
        rw [settleCount] at h ⊢
        cases hf : allFalse (decList [true]) with
        | true =>
          rw [hf] at h
          cases c with
          | zero => exact absurd ⟨(fun h ↦ nomatch h), Or.inr rfl⟩ h
          | succ c => exact absurd ⟨(fun h ↦ nomatch h), Or.inl rfl⟩ h
        | false => rfl
      · rw [ite_eq_right hfull]
  | bits =>
    rw [scanStep_bits, settleDigits] at h ⊢
    by_cases hfull : (b :: d).length = wd
    · rw [ite_eq_left hfull] at h ⊢
      rw [settleCount] at h ⊢
      cases hf : allFalse (decList (b :: d)) with
      | true =>
        rw [hf] at h
        cases c with
        | zero => exact absurd ⟨(fun h ↦ nomatch h), Or.inr rfl⟩ h
        | succ c => exact absurd ⟨(fun h ↦ nomatch h), Or.inl rfl⟩ h
      | false => rfl
    · rw [ite_eq_right hfull]
  | count =>
    rw [scanStep_count, settleCount] at h ⊢
    cases hf : allFalse (decList d) with
    | true =>
      rw [hf] at h
      cases c with
      | zero => exact absurd ⟨(fun h ↦ nomatch h), Or.inr rfl⟩ h
      | succ c => exact absurd ⟨(fun h ↦ nomatch h), Or.inl rfl⟩ h
    | false => rfl
  | done => rw [scanStep_done]
  | dead => rw [scanStep_dead]

/-- The counter's step preserves the invariant. -/
theorem goodTree_treeStep (s : Scan) (b : Bool) (l : List Digit) (h : GoodTree s l) :
    GoodTree (scanStep W s b) (treeStep W s b l) := by
  obtain ⟨hn, hv⟩ := h
  rw [treeStep]
  by_cases hm : s.mode = .term ∧ b = true
  · rw [ite_eq_left hm]
    obtain ⟨m, c, wd, d⟩ := s
    obtain ⟨hm, hb⟩ := hm
    change m = .term at hm
    subst hm hb
    rw [scanStep_term_true]
    exact ⟨nlz_inc l hn, by rw [value_inc, hv]⟩
  · rw [ite_eq_right hm]
    cases hc : closes W s b with
    | true =>
      rw [ite_eq_left rfl, scanStep_eq_close_of_closes W s b hc]
      refine ⟨nlz_dec l hn, ?_⟩
      rcases hcount : s.count with _ | c
      · rw [hcount] at hv
        rw [(value_eq_zero_iff l hn).mp hv, dec_nil, close_zero]
        rfl
      · have hne : l ≠ [] := fun hl ↦ by rw [hl] at hv; exact absurd hv.symm (by rw [hcount]; simp)
        have := value_dec l hn hne
        rw [close_succ]
        change value (dec l) = c
        omega
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      exact ⟨hn, by rw [count_scanStep_of_not_closes W s b hm hc, hv]⟩

/-- The scan with the counter from a state satisfying the invariant satisfies
it. -/
theorem goodTree_runTree (w : List Bool) :
    ∀ p : Scan × List Digit, GoodTree p.1 p.2 → GoodTree (runTree W w p).1 (runTree W w p).2 :=
  List.rec
    (motive := fun w ↦ ∀ p : Scan × List Digit, GoodTree p.1 p.2 →
      GoodTree (runTree W w p).1 (runTree W w p).2)
    (fun _ h ↦ h)
    (fun b _ ih p h ↦ by rw [runTree_cons]; exact ih _ (goodTree_treeStep W p.1 b p.2 h)) w

/-- The counter after any word denotes the scan's pending count. -/
theorem goodTree_treeAt (w : List Bool) : GoodTree (scanAt W w) (treeAt W w) := by
  have := goodTree_runTree W w (init, []) goodTree_init
  rw [runTree_fst] at this
  exact this

end Replay

end Geb.BitTreeScanner
