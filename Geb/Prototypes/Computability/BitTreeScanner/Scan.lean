/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Encoding

set_option doc.verso true

/-!
# The left-to-right scan recognizing spelled trees

A single left-to-right pass over a bitstring carrying a mode, a counter and a
list of binary digits, which accepts exactly the spellings of
{name}`Geb.BitTreeScanner.spell`. The mode records whether the scan expects a tree,
is reading the zeros of a leaf's gamma code, its digits, or its payload, has
completed the one tree it expects, or has failed; the counter is the number of
trees pending beyond the one in progress; the digits are the leaf's length as
read, least significant first, then the payload bits remaining, decremented as
each is read.

The counter is the pending count of {lit}`RankedAlphabet.Binary.depth` less
one, so that it is never negative and the completed scan is a mode rather
than a count. Validity is one condition on the final state, that its mode is
the completed one, and {lit}`Geb.BitTreeScanner.valid_iff_exists_spell` identifies
the words satisfying it with the spellings.

## Main definitions

* {lit}`Geb.BitTreeScanner.Mode`, {lit}`Geb.BitTreeScanner.Scan` — the scan's modes and its
  state.
* {lit}`Geb.BitTreeScanner.close` — the state a completed tree leaves at a pending
  count.
* {lit}`Geb.BitTreeScanner.decList`, {lit}`Geb.BitTreeScanner.allFalse` — the decrement of a
  digit list, least significant digit first, and its test for zero.
* {lit}`Geb.BitTreeScanner.settleCount`, {lit}`Geb.BitTreeScanner.settleDigits` — the state
  after a payload bit and after a length digit, closing the leaf when no
  payload remains and starting the countdown when the digits are complete.
* {lit}`Geb.BitTreeScanner.scanStep`, {lit}`Geb.BitTreeScanner.scanFrom`,
  {lit}`Geb.BitTreeScanner.init`, {lit}`Geb.BitTreeScanner.scanFinal` — the scan.
* {lit}`Geb.BitTreeScanner.validBool`, {lit}`Geb.BitTreeScanner.Valid` — what it accepts.

## Main statements

* {lit}`Geb.BitTreeScanner.valueLE_decList`, {lit}`Geb.BitTreeScanner.allFalse_iff` — the
  decrement lowers the value by one, and the zero test is the value's.
* {lit}`Geb.BitTreeScanner.scanFrom_spell` — a spelling scanned from the expecting
  mode at any pending count completes that count.
* {lit}`Geb.BitTreeScanner.valid_spell` — every spelling is valid.
* {lit}`Geb.BitTreeScanner.exists_spell_of_valid` — every valid word is a spelling.
* {lit}`Geb.BitTreeScanner.valid_iff_exists_spell` — the valid words are exactly the
  spellings.
* {lit}`Geb.BitTreeScanner.eq_nil_of_spell_eq_spell_append` — no spelling is a
  proper prefix of another: the encoding is a prefix code.
* {lit}`Geb.BitTreeScanner.scanFinal_take_succ` — the scan of a prefix extended by
  one bit, the form a machine step against the scan consumes.

## Implementation notes

The scan reads from the list's head, so {lit}`scanFrom` is a {name}`List.foldl`
and a step on a prefix extended at its end is {name}`List.foldl_append`. The
right-to-left scan of {lit}`RankedAlphabet.scanFrom` reads a word's last bit
first because a prefix code is read in preorder from the left; here the
machine also reads from the left, in one pass, so nothing reverses.

The decrement of a digit list is a {name}`List.foldr` into a function of a
flag recording whether the borrow has been absorbed, so that it compiles and
its equations at each head digit hold by {lit}`rfl`; the code generator does
not compile {name}`List.rec`, and a self-recursive definition is barred.

{lit}`exists_spell_of_valid` recurses on a bound on the word's length rather
than on the word: the pair case applies its hypothesis to the remainder the
left child leaves, which is not a structural subterm. The leaf case is the
three phase lemmas {lit}`exists_of_zeros`, {lit}`exists_of_settleDigits` and
{lit}`exists_of_settleCount`, each recursing on the word through its phase and
handing the remainder to the next.

A {lit}`scanStep` equation at a mode whose row of the match is a catch-all in
the bit column is proved by cases on the bit: the compiled matcher inspects
the bit there, so the equation is not {lit}`rfl` at a variable bit.

## Tags

binary tree, prefix code, scan, recognizer, counter automaton, Elias gamma code
-/

@[expose] public section

namespace Geb.BitTreeScanner

/-- The scan's mode. -/
inductive Mode where
  /-- Expecting a tree. -/
  | term
  /-- Inside a leaf, reading the zeros of its gamma code. -/
  | zeros
  /-- Inside a leaf, reading the digits of its gamma code. -/
  | bits
  /-- Inside a leaf, reading its payload while counting down. -/
  | count
  /-- The one expected tree complete, nothing pending. -/
  | done
  /-- Failed: a bit read after completion. -/
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- The scan's state: its mode, the count of trees pending beyond the one in
progress, the number of digit cells the current leaf's gamma code has claimed,
and the digits read or remaining, least significant first. -/
@[ext] structure Scan where
  /-- The mode. -/
  mode : Mode
  /-- The count of trees pending beyond the one in progress. -/
  count : ℕ
  /-- The number of digit cells the current leaf's gamma code has claimed: the
  zeros read so far, then the digits' total. -/
  width : ℕ
  /-- The digits read so far, then the payload bits remaining, least
  significant first. -/
  digits : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- The state a completed tree leaves at a pending count: complete when
nothing is pending, else expecting the next tree with one fewer pending. -/
def close : ℕ → Scan
  | 0 => ⟨.done, 0, 0, []⟩
  | c + 1 => ⟨.term, c, 0, []⟩

section Digits

/-- One digit of the decrement, given the rest as a function of whether the
borrow has been absorbed: once absorbed the digit passes; otherwise a one
absorbs it and a zero propagates it. -/
def decStep (b : Bool) (k : Bool → List Bool) (absorbed : Bool) : List Bool :=
  cond absorbed (b :: k true) (cond b (false :: k true) (true :: k false))

/-- The decrement as a function of whether the borrow has been absorbed. -/
def decAux (d : List Bool) : Bool → List Bool := d.foldr decStep fun _ ↦ []

/-- The decrement of a digit list, least significant digit first: the zeros
below the lowest one become ones and that one a zero. The empty list and the
all-zero list return zeros. -/
def decList (d : List Bool) : List Bool := decAux d false

/-- Whether every digit is zero. -/
def allFalse (d : List Bool) : Bool := d.all fun b ↦ !b

/-- Once the borrow is absorbed the remaining digits pass. -/
theorem decAux_true (d : List Bool) : decAux d true = d :=
  List.rec (motive := fun d ↦ decAux d true = d) rfl
    (fun b _ ih ↦ by
      change b :: decAux _ true = b :: _
      rw [ih]) d

/-- The decrement of the empty list. -/
@[simp] theorem decList_nil : decList [] = [] := rfl

/-- A zero below the lowest one becomes a one and the borrow propagates. -/
@[simp] theorem decList_cons_false (d : List Bool) : decList (false :: d) = true :: decList d :=
  rfl

/-- The lowest one becomes a zero and the digits above it pass. -/
@[simp] theorem decList_cons_true (d : List Bool) : decList (true :: d) = false :: d := by
  change false :: decAux d true = false :: d
  rw [decAux_true]

/-- The decrement keeps the length. -/
theorem length_decList (d : List Bool) : (decList d).length = d.length :=
  List.rec (motive := fun d ↦ (decList d).length = d.length) rfl
    (fun b _ ih ↦ by cases b <;> simp only [decList_cons_false, decList_cons_true,
      List.length_cons, ih]) d

/-- The zero test of the empty list. -/
@[simp] theorem allFalse_nil : allFalse [] = true := rfl

/-- The zero test of a digit list is its head's and its tail's. -/
@[simp] theorem allFalse_cons (b : Bool) (d : List Bool) :
    allFalse (b :: d) = (!b && allFalse d) := rfl

/-- A digit list is all zeros exactly when it denotes zero. -/
theorem allFalse_iff (d : List Bool) : allFalse d = true ↔ valueLE d = 0 :=
  List.rec (motive := fun d ↦ allFalse d = true ↔ valueLE d = 0) (by simp)
    (fun b d ih ↦ by
      rw [allFalse_cons, valueLE_cons, Nat.bit_eq_zero_iff, Bool.and_eq_true, ← ih]
      cases b <;> simp) d

/-- The decrement of a digit list denoting a positive number lowers its value by
one. -/
theorem valueLE_decList (d : List Bool) (h : valueLE d ≠ 0) :
    valueLE (decList d) + 1 = valueLE d :=
  List.rec (motive := fun d ↦ valueLE d ≠ 0 → valueLE (decList d) + 1 = valueLE d)
    (fun h ↦ absurd rfl h)
    (fun b d ih h ↦ by
      cases b with
      | false =>
        rw [valueLE_cons, Nat.bit_val] at h ⊢
        rw [decList_cons_false, valueLE_cons, Nat.bit_val, ← ih (by simp at h; omega)]
        simp only [Bool.toNat_true, Bool.toNat_false]
        omega
      | true =>
        rw [decList_cons_true, valueLE_cons, valueLE_cons, Nat.bit_val, Nat.bit_val]
        simp only [Bool.toNat_true, Bool.toNat_false]) d h

end Digits

/-- The state after a payload bit, the digits being the payload remaining:
the leaf closes when none remains, and the countdown continues otherwise. -/
def settleCount (c w : ℕ) (d : List Bool) : Scan :=
  cond (allFalse d) (close c) ⟨.count, c, w, d⟩

/-- The state after a length digit: when the digits fill the width the length
is complete, the payload remaining is one less than it, and the countdown
starts; otherwise more digits follow. -/
def settleDigits (c w : ℕ) (d : List Bool) : Scan :=
  if d.length = w then settleCount c w (decList d) else ⟨.bits, c, w, d⟩

/-- One step of the scan, reading one bit. A pair bit raises the count and a
leaf bit opens a leaf; a leaf's gamma code is its zeros, each widening the
digit cells, then a one and as many digits, most significant first, as zeros
were read; each payload bit lowers the remaining count; after completion any
bit fails, and failure absorbs. -/
def scanStep (s : Scan) (b : Bool) : Scan :=
  match s.mode, b with
  | .term, true => ⟨.term, s.count + 1, 0, []⟩
  | .term, false => ⟨.zeros, s.count, 0, []⟩
  | .zeros, false => ⟨.zeros, s.count, s.width + 1, []⟩
  | .zeros, true => settleDigits s.count (s.width + 1) [true]
  | .bits, _ => settleDigits s.count s.width (b :: s.digits)
  | .count, _ => settleCount s.count s.width (decList s.digits)
  | .done, _ => ⟨.dead, s.count, 0, []⟩
  | .dead, _ => s

/-- The scan of a word from a state, reading the word's head first. -/
def scanFrom (w : List Bool) (s : Scan) : Scan := w.foldl scanStep s

/-- The initial state: expecting one tree, nothing pending. -/
def init : Scan := ⟨.term, 0, 0, []⟩

/-- The scan of a word from the initial state. -/
def scanFinal (w : List Bool) : Scan := scanFrom w init

/-- Whether a word spells a tree: the scan completes. -/
def validBool (w : List Bool) : Bool := decide ((scanFinal w).mode = .done)

/-- A word spells a tree. -/
def Valid (w : List Bool) : Prop := validBool w = true

/-- {name}`Valid` is a {lit}`Bool` equation, so membership is decidable.
Instance search does not unfold the {lit}`def`, so the instance is
supplied. -/
instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ = true))

section Equations

/-- Nothing pending: completion. -/
@[simp] theorem close_zero : close 0 = ⟨.done, 0, 0, []⟩ := rfl

/-- Something pending: the next tree is expected. -/
@[simp] theorem close_succ (c : ℕ) : close (c + 1) = ⟨.term, c, 0, []⟩ := rfl

/-- No payload remaining: the leaf closes. -/
theorem settleCount_of_allFalse (c w : ℕ) (d : List Bool) (h : allFalse d = true) :
    settleCount c w d = close c := by
  rw [settleCount, h]
  rfl

/-- Payload remaining: the countdown continues. -/
theorem settleCount_of_not_allFalse (c w : ℕ) (d : List Bool) (h : allFalse d = false) :
    settleCount c w d = ⟨.count, c, w, d⟩ := by
  rw [settleCount, h]
  rfl

/-- The digits fill the width: the countdown starts at one less than the
length. -/
theorem settleDigits_of_length_eq (c w : ℕ) (d : List Bool) (h : d.length = w) :
    settleDigits c w d = settleCount c w (decList d) := by
  rw [settleDigits, ite_eq_left h]

/-- The digits do not fill the width: more digits follow. -/
theorem settleDigits_of_length_ne (c w : ℕ) (d : List Bool) (h : d.length ≠ w) :
    settleDigits c w d = ⟨.bits, c, w, d⟩ := by
  rw [settleDigits, ite_eq_right h]

/-- A pair bit raises the pending count. -/
@[simp] theorem scanStep_term_true (c w : ℕ) (d : List Bool) :
    scanStep ⟨.term, c, w, d⟩ true = ⟨.term, c + 1, 0, []⟩ := rfl

/-- A leaf bit opens a leaf. -/
@[simp] theorem scanStep_term_false (c w : ℕ) (d : List Bool) :
    scanStep ⟨.term, c, w, d⟩ false = ⟨.zeros, c, 0, []⟩ := rfl

/-- A zero of the gamma code widens the digit cells. -/
@[simp] theorem scanStep_zeros_false (c w : ℕ) (d : List Bool) :
    scanStep ⟨.zeros, c, w, d⟩ false = ⟨.zeros, c, w + 1, []⟩ := rfl

/-- The one of the gamma code is its most significant digit. -/
@[simp] theorem scanStep_zeros_true (c w : ℕ) (d : List Bool) :
    scanStep ⟨.zeros, c, w, d⟩ true = settleDigits c (w + 1) [true] := rfl

/-- A digit of the gamma code is prepended, being less significant than those
read. -/
@[simp] theorem scanStep_bits (c w : ℕ) (d : List Bool) (b : Bool) :
    scanStep ⟨.bits, c, w, d⟩ b = settleDigits c w (b :: d) := by
  cases b <;> rfl

/-- A payload bit lowers the remaining count. -/
@[simp] theorem scanStep_count (c w : ℕ) (d : List Bool) (b : Bool) :
    scanStep ⟨.count, c, w, d⟩ b = settleCount c w (decList d) := by
  cases b <;> rfl

/-- A bit after completion fails. -/
@[simp] theorem scanStep_done (c w : ℕ) (d : List Bool) (b : Bool) :
    scanStep ⟨.done, c, w, d⟩ b = ⟨.dead, c, 0, []⟩ := by
  cases b <;> rfl

/-- Failure absorbs. -/
@[simp] theorem scanStep_dead (c w : ℕ) (d : List Bool) (b : Bool) :
    scanStep ⟨.dead, c, w, d⟩ b = ⟨.dead, c, w, d⟩ := by
  cases b <;> rfl

/-- The empty word leaves the state. -/
@[simp] theorem scanFrom_nil (s : Scan) : scanFrom [] s = s := rfl

/-- The scan of the empty word is the initial state. -/
@[simp] theorem scanFinal_nil : scanFinal [] = init := rfl

/-- The scan reads the head bit first. -/
@[simp] theorem scanFrom_cons (b : Bool) (w : List Bool) (s : Scan) :
    scanFrom (b :: w) s = scanFrom w (scanStep s b) := rfl

/-- The scan of a concatenation reads the earlier part first. -/
theorem scanFrom_append (u v : List Bool) (s : Scan) :
    scanFrom (u ++ v) s = scanFrom v (scanFrom u s) := List.foldl_append

/-- A failed scan reads no further. -/
theorem scanFrom_dead (w : List Bool) (c wd : ℕ) (d : List Bool) :
    scanFrom w ⟨.dead, c, wd, d⟩ = ⟨.dead, c, wd, d⟩ :=
  List.rec (motive := fun w ↦ scanFrom w ⟨.dead, c, wd, d⟩ = ⟨.dead, c, wd, d⟩) rfl
    (fun b _ ih ↦ by rw [scanFrom_cons, scanStep_dead]; exact ih) w

/-- The scan of a prefix extended by one bit is the scan of the prefix followed
by that bit. -/
theorem scanFinal_take_succ (w : List Bool) (k : ℕ) (h : k < w.length) :
    scanFinal (w.take (k + 1)) = scanStep (scanFinal (w.take k)) w[k] := by
  rw [List.take_succ_eq_append_getElem h, scanFinal, scanFinal, scanFrom_append]
  rfl

end Equations

section Soundness

/-- The zeros of a gamma code widen the digit cells by their number. -/
theorem scanFrom_replicate_false (j : ℕ) :
    ∀ c w, scanFrom (List.replicate j false) ⟨.zeros, c, w, []⟩ = ⟨.zeros, c, w + j, []⟩ :=
  Nat.rec (motive := fun j ↦ ∀ c w,
      scanFrom (List.replicate j false) ⟨.zeros, c, w, []⟩ = ⟨.zeros, c, w + j, []⟩)
    (fun _ _ ↦ rfl)
    (fun j ih c w ↦ by
      rw [List.replicate_succ, scanFrom_cons, scanStep_zeros_false, ih, Nat.add_assoc,
        Nat.add_comm 1 j]) j

/-- Reading digits in the digit mode accumulates them, least significant first,
and settles when they fill the width. -/
theorem scanFrom_bits (rest : List Bool) :
    ∀ (c w : ℕ) (d : List Bool), d.length < w → d.length + rest.length ≤ w →
      scanFrom rest ⟨.bits, c, w, d⟩ =
        if d.length + rest.length = w then settleCount c w (decList (rest.reverse ++ d))
        else ⟨.bits, c, w, rest.reverse ++ d⟩ :=
  List.rec
    (motive := fun rest ↦ ∀ (c w : ℕ) (d : List Bool), d.length < w →
      d.length + rest.length ≤ w →
      scanFrom rest ⟨.bits, c, w, d⟩ =
        if d.length + rest.length = w then settleCount c w (decList (rest.reverse ++ d))
        else ⟨.bits, c, w, rest.reverse ++ d⟩)
    (fun c w d hlt _ ↦ by
      rw [List.length_nil, Nat.add_zero, ite_eq_right (Nat.ne_of_lt hlt), scanFrom_nil,
        List.reverse_nil, List.nil_append])
    (fun b rest ih c w d hlt hle ↦ by
      rw [scanFrom_cons, scanStep_bits, List.length_cons]
      by_cases hfull : (b :: d).length = w
      · rw [List.length_cons] at hfull
        have hrest : rest = [] := by
          rw [List.length_cons] at hle
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        rw [settleDigits_of_length_eq _ _ _ (by rw [List.length_cons]; exact hfull), scanFrom_nil,
          ite_eq_left (by rw [List.length_nil]; omega), List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append]
      · rw [List.length_cons] at hfull
        rw [settleDigits_of_length_ne _ _ _ (by rw [List.length_cons]; exact hfull),
          ih c w (b :: d) (by rw [List.length_cons]; omega)
            (by rw [List.length_cons] at hle ⊢; omega),
          List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
          show d.length + 1 + rest.length = d.length + (rest.length + 1) by omega]) rest

/-- Reading the payload in the countdown, as many bits as the digits denote,
closes the leaf. -/
theorem scanFrom_settleCount (s : List Bool) :
    ∀ (c w : ℕ) (d : List Bool), valueLE d = s.length →
      scanFrom s (settleCount c w d) = close c :=
  List.rec
    (motive := fun s ↦ ∀ (c w : ℕ) (d : List Bool), valueLE d = s.length →
      scanFrom s (settleCount c w d) = close c)
    (fun c w d h ↦ by
      rw [settleCount_of_allFalse _ _ _ ((allFalse_iff d).mpr h), scanFrom_nil])
    (fun b s ih c w d h ↦ by
      rw [List.length_cons] at h
      have hne : valueLE d ≠ 0 := by omega
      rw [settleCount_of_not_allFalse _ _ _ (by
          rw [← Bool.not_eq_true, allFalse_iff]; exact hne),
        scanFrom_cons, scanStep_count]
      exact ih c w (decList d) (by have := valueLE_decList d hne; omega)) s

/-- Reading the one of a gamma code and the digits below it, from the zeros
mode after as many zeros as digits, starts the countdown at one less than the
digits' value. -/
theorem scanFrom_true_reverse (r : List Bool) (c : ℕ) :
    scanFrom (true :: r.reverse) ⟨.zeros, c, r.length, []⟩ =
      settleCount c (r.length + 1) (decList (r ++ [true])) := by
  rw [scanFrom_cons, scanStep_zeros_true]
  cases r with
  | nil => rfl
  | cons b r =>
    rw [settleDigits_of_length_ne _ _ _ (by rw [List.length_singleton, List.length_cons]; omega),
      scanFrom_bits _ c _ [true] (by rw [List.length_singleton, List.length_cons]; omega)
        (by rw [List.length_singleton, List.length_reverse]; omega),
      ite_eq_left (by rw [List.length_singleton, List.length_reverse]; omega),
      List.reverse_reverse]

/-- A leaf body read from the zeros mode at no zeros closes the leaf: the gamma
code's zeros and digits start the countdown at the payload's length, and the
payload runs it down. -/
theorem scanFrom_leafBody (s : List Bool) (c : ℕ) :
    scanFrom (leafBody s) ⟨.zeros, c, 0, []⟩ = close c := by
  obtain ⟨r, hr⟩ := exists_bits_eq_append_true (s.length + 1) (Nat.succ_pos _)
  have hval : valueLE (r ++ [true]) = s.length + 1 := by rw [← hr, valueLE_bits]
  rw [leafBody, gamma, hr, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.append_assoc,
    scanFrom_append, scanFrom_replicate_false, Nat.zero_add, scanFrom_append,
    scanFrom_true_reverse]
  exact scanFrom_settleCount s c _ _ (by
    have := valueLE_decList _ (Nat.ne_of_gt (valueLE_append_true_pos r))
    omega)

/-- A spelling read in the expecting mode completes the pending count. -/
theorem scanFrom_spell (t : BitTree) : ∀ c, scanFrom (spell t) ⟨.term, c, 0, []⟩ = close c :=
  PFunctor.FreeM.rec (motive := fun t ↦ ∀ c, scanFrom (spell t) ⟨.term, c, 0, []⟩ = close c)
    (fun s c ↦ by rw [spell_pure, scanFrom_cons, scanStep_term_false, scanFrom_leafBody])
    (fun a k ih c ↦ by
      rw [spell_liftBind, scanFrom_cons, scanStep_term_true, scanFrom_append, ih false,
        close_succ, ih true]) t

/-- Every spelling is valid. -/
theorem valid_spell (t : BitTree) : Valid (spell t) := by
  unfold Valid validBool scanFinal init
  rw [scanFrom_spell t 0]
  rfl

end Soundness

section Completeness

/-- A word completing the scan from the countdown begins with as many bits as
the digits denote, the remainder completing the scan from the state the leaf
leaves. -/
theorem exists_of_settleCount (w : List Bool) :
    ∀ (c width : ℕ) (d : List Bool), (scanFrom w (settleCount c width d)).mode = .done →
      ∃ s v, w = s ++ v ∧ s.length = valueLE d ∧ (scanFrom v (close c)).mode = .done :=
  List.rec
    (motive := fun w ↦ ∀ (c width : ℕ) (d : List Bool),
      (scanFrom w (settleCount c width d)).mode = .done →
      ∃ s v, w = s ++ v ∧ s.length = valueLE d ∧ (scanFrom v (close c)).mode = .done)
    (fun c width d h ↦ by
      cases hf : allFalse d with
      | true =>
        rw [settleCount_of_allFalse _ _ _ hf] at h
        exact ⟨[], [], rfl, ((allFalse_iff d).mp hf).symm, h⟩
      | false =>
        rw [settleCount_of_not_allFalse _ _ _ hf, scanFrom_nil] at h
        exact nomatch h)
    (fun b w ih c width d h ↦ by
      cases hf : allFalse d with
      | true =>
        rw [settleCount_of_allFalse _ _ _ hf] at h
        exact ⟨[], b :: w, rfl, ((allFalse_iff d).mp hf).symm, h⟩
      | false =>
        rw [settleCount_of_not_allFalse _ _ _ hf, scanFrom_cons, scanStep_count] at h
        obtain ⟨s, v, hw, hlen, hv⟩ := ih c width (decList d) h
        have hne : valueLE d ≠ 0 := fun h0 ↦ Bool.false_ne_true (hf ▸ (allFalse_iff d).mpr h0)
        exact ⟨b :: s, v, by rw [hw, List.cons_append],
          by rw [List.length_cons, hlen, valueLE_decList d hne], hv⟩) w

/-- A word completing the scan from complete digits: the countdown lemma at the
digits' value less one. -/
theorem exists_of_settleDigits_full (w : List Bool) (c width : ℕ) (r : List Bool)
    (hfull : (r ++ [true]).length = width)
    (h : (scanFrom w (settleDigits c width (r ++ [true]))).mode = .done) :
    ∃ rest s v, w = rest ++ s ++ v ∧ (r ++ [true]).length + rest.length = width ∧
      s.length + 1 = valueLE (rest.reverse ++ (r ++ [true])) ∧
      (scanFrom v (close c)).mode = .done := by
  rw [settleDigits_of_length_eq _ _ _ hfull] at h
  obtain ⟨s, v, hw, hlen, hv⟩ := exists_of_settleCount w c width _ h
  refine ⟨[], s, v, by rw [hw, List.nil_append], by rw [List.length_nil, hfull, Nat.add_zero], ?_,
    hv⟩
  rw [List.reverse_nil, List.nil_append, hlen]
  exact valueLE_decList _ (Nat.ne_of_gt (valueLE_append_true_pos r))

/-- A word completing the scan from the digit mode begins with the digits
still to read, then as many payload bits as the whole digits denote less one,
the remainder completing the scan from the state the leaf leaves. -/
theorem exists_of_settleDigits (w : List Bool) :
    ∀ (c width : ℕ) (r : List Bool), (r ++ [true]).length ≤ width →
      (scanFrom w (settleDigits c width (r ++ [true]))).mode = .done →
      ∃ rest s v, w = rest ++ s ++ v ∧ (r ++ [true]).length + rest.length = width ∧
        s.length + 1 = valueLE (rest.reverse ++ (r ++ [true])) ∧
        (scanFrom v (close c)).mode = .done :=
  List.rec
    (motive := fun w ↦ ∀ (c width : ℕ) (r : List Bool), (r ++ [true]).length ≤ width →
      (scanFrom w (settleDigits c width (r ++ [true]))).mode = .done →
      ∃ rest s v, w = rest ++ s ++ v ∧ (r ++ [true]).length + rest.length = width ∧
        s.length + 1 = valueLE (rest.reverse ++ (r ++ [true])) ∧
        (scanFrom v (close c)).mode = .done)
    (fun c width r _ h ↦ by
      by_cases hfull : (r ++ [true]).length = width
      · exact exists_of_settleDigits_full [] c width r hfull h
      · rw [settleDigits_of_length_ne _ _ _ hfull, scanFrom_nil] at h
        exact nomatch h)
    (fun b w ih c width r hle h ↦ by
      by_cases hfull : (r ++ [true]).length = width
      · exact exists_of_settleDigits_full (b :: w) c width r hfull h
      · rw [settleDigits_of_length_ne _ _ _ hfull, scanFrom_cons, scanStep_bits,
          ← List.cons_append] at h
        obtain ⟨rest, s, v, hw, hlen, hval, hv⟩ := ih c width (b :: r)
          (by rw [List.length_append, List.length_singleton] at hle hfull ⊢
              rw [List.length_cons]; omega) h
        refine ⟨b :: rest, s, v, by rw [hw]; simp only [List.cons_append], ?_, ?_, hv⟩
        · rw [List.length_append, List.length_singleton, List.length_cons] at hlen ⊢
          omega
        · rw [hval, List.reverse_cons, List.append_assoc, List.singleton_append,
            List.cons_append]) w

/-- A word completing the scan from the zeros mode begins with more zeros, a
one, as many digits as zeros in all, then as many payload bits as the digits
denote less one, the remainder completing the scan from the state the leaf
leaves. -/
theorem exists_of_zeros (w : List Bool) :
    ∀ (c j : ℕ), (scanFrom w ⟨.zeros, c, j, []⟩).mode = .done →
      ∃ k rest s v, w = List.replicate k false ++ true :: (rest ++ s ++ v) ∧
        rest.length = j + k ∧ s.length + 1 = valueLE (rest.reverse ++ [true]) ∧
        (scanFrom v (close c)).mode = .done :=
  List.rec
    (motive := fun w ↦ ∀ (c j : ℕ), (scanFrom w ⟨.zeros, c, j, []⟩).mode = .done →
      ∃ k rest s v, w = List.replicate k false ++ true :: (rest ++ s ++ v) ∧
        rest.length = j + k ∧ s.length + 1 = valueLE (rest.reverse ++ [true]) ∧
        (scanFrom v (close c)).mode = .done)
    (fun _ _ h ↦ by rw [scanFrom_nil] at h; exact nomatch h)
    (fun b w ih c j h ↦ by
      cases b with
      | false =>
        rw [scanFrom_cons, scanStep_zeros_false] at h
        obtain ⟨k, rest, s, v, hw, hlen, hval, hv⟩ := ih c (j + 1) h
        exact ⟨k + 1, rest, s, v, by rw [hw, List.replicate_succ, List.cons_append],
          by omega, hval, hv⟩
      | true =>
        rw [scanFrom_cons, scanStep_zeros_true] at h
        obtain ⟨rest, s, v, hw, hlen, hval, hv⟩ :=
          exists_of_settleDigits w c (j + 1) []
            (by rw [List.nil_append, List.length_singleton]; omega) h
        refine ⟨0, rest, s, v, by rw [hw]; rfl, ?_, hval, hv⟩
        rw [List.nil_append, List.length_singleton] at hlen
        omega) w

/-- A word of bounded length completing the scan from the expecting mode begins
with a spelling, the remainder completing the scan from the state the tree
leaves. The recursion is on the bound: the pair case applies its hypothesis
to the remainder the left child leaves, which is not a structural subterm of
the word. -/
theorem exists_spell_append_of_length_le (n : ℕ) :
    ∀ w : List Bool, w.length ≤ n → ∀ c, (scanFrom w ⟨.term, c, 0, []⟩).mode = .done →
      ∃ t v, w = spell t ++ v ∧ (scanFrom v (close c)).mode = .done :=
  Nat.rec
    (motive := fun n ↦ ∀ w : List Bool, w.length ≤ n → ∀ c,
      (scanFrom w ⟨.term, c, 0, []⟩).mode = .done →
        ∃ t v, w = spell t ++ v ∧ (scanFrom v (close c)).mode = .done)
    (fun w hw c h ↦ by
      cases w with
      | nil => exact nomatch h
      | cons b w => exact absurd hw (by simp))
    (fun n ih w hw c h ↦ by
      cases w with
      | nil => exact nomatch h
      | cons b w =>
        rw [List.length_cons] at hw
        cases b with
        | false =>
          rw [scanFrom_cons, scanStep_term_false] at h
          obtain ⟨k, rest, s, v, hw', hlen, hval, hv⟩ := exists_of_zeros w c 0 h
          refine ⟨leaf s, v, ?_, hv⟩
          rw [hw', spell_leaf, leafBody, hval, gamma_valueLE, List.length_reverse,
            List.reverse_reverse, hlen, Nat.zero_add]
          simp only [List.cons_append, List.append_assoc]
        | true =>
          rw [scanFrom_cons, scanStep_term_true] at h
          obtain ⟨l, v₁, hw₁, hv₁⟩ := ih w (by omega) (c + 1) h
          have hv₁len : v₁.length ≤ n := by
            have := congrArg List.length hw₁
            rw [List.length_append] at this
            omega
          rw [close_succ] at hv₁
          obtain ⟨r, v, hv, hvv⟩ := ih v₁ hv₁len c hv₁
          exact ⟨pair l r, v, by rw [hw₁, hv, spell_pair, List.cons_append, List.append_assoc],
            hvv⟩) n

/-- A word completing the scan from the completed mode is empty: a bit read
after completion fails, and failure absorbs. -/
theorem eq_nil_of_mode_scanFrom_done_eq_done (w : List Bool) (c wd : ℕ) (d : List Bool)
    (h : (scanFrom w ⟨.done, c, wd, d⟩).mode = .done) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w =>
    rw [scanFrom_cons, scanStep_done, scanFrom_dead] at h
    exact nomatch h

/-- Every valid word is a spelling. -/
theorem exists_spell_of_valid {w : List Bool} (h : Valid w) : ∃ t, spell t = w := by
  have h' : (scanFrom w ⟨.term, 0, 0, []⟩).mode = .done := of_decide_eq_true h
  obtain ⟨t, v, hw, hv⟩ := exists_spell_append_of_length_le w.length w le_rfl 0 h'
  rw [close_zero] at hv
  rw [eq_nil_of_mode_scanFrom_done_eq_done v 0 0 [] hv, List.append_nil] at hw
  exact ⟨t, hw.symm⟩

/-- The valid words are exactly the spellings. -/
theorem valid_iff_exists_spell (w : List Bool) : Valid w ↔ ∃ t, spell t = w :=
  ⟨exists_spell_of_valid, fun ⟨t, ht⟩ ↦ ht ▸ valid_spell t⟩

/-- No spelling is a proper prefix of another: the scan completes at the end
of the shorter and fails on any bit after it. -/
theorem eq_nil_of_spell_eq_spell_append (t t' : BitTree) (v : List Bool)
    (h : spell t = spell t' ++ v) : v = [] := by
  have hv : (scanFrom v (close 0)).mode = .done := by
    rw [← scanFrom_spell t' 0, ← scanFrom_append, ← h, scanFrom_spell t 0]
    rfl
  exact eq_nil_of_mode_scanFrom_done_eq_done v 0 0 [] hv

end Completeness


end Geb.BitTreeScanner
