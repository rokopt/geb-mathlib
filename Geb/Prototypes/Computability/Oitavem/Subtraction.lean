/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
public import Mathlib.Tactic.Ring

set_option doc.verso true in
/-!
# Digitwise subtraction of shortlex words

A signed carry scan subtracts the sentinel encodings of two words and adds one.
Removing trailing zeroes and the final sentinel recovers their saturated shortlex
difference. The arithmetic scans digits rather than decoding either whole word.

## Main definitions

* {lit}`subDigits` scans paired digits with a carry in the interval from minus one to one.
* {lit}`shortlexSub` pads the sentinel encodings, subtracts, and normalizes the result.

## Main statements

* {lit}`subDigits_spec` proves the reconstruction invariant of the scan.
* {lit}`subDigits_carry_mem` bounds its carry throughout the recursion.
* {lit}`shortlexSub_eq_numericSub` identifies the algorithm with the existing word model.

## Implementation notes

The digit algorithm and its constructive proof were developed with Aristotle and
adapted to the existing encoding. These are arithmetic specifications for a machine
implementation: the Lean lists in this module are not logarithmic work tapes.
A machine must scan the virtual arguments and regenerate digits for output.

## Tags

binary arithmetic, subtraction, shortlex, carry
-/

set_option doc.verso true

namespace Geb.Oitavem

open Geb.BitTreeScanner (ofBits ofBits_nil ofBits_cons)

public section

/-- A signed carry encoded by a blank, zero, or one work-tape cell. -/
@[expose] def carryValue : Option Bool → ℤ
  | none => -1
  | some false => 0
  | some true => 1

/-- Subtract two digits with a finite carry, returning the next carry and output digit. -/
@[expose] def subBit (a b : Bool) (c : Option Bool) : Option Bool × Bool :=
  let d := (a.toNat : ℤ) - b.toNat + carryValue c
  (if d < 0 then none else some (decide (2 ≤ d)), decide (d % 2 = 1))

/-- The finite transition represents exactly the signed quotient used by the scan. -/
theorem carryValue_subBit (a b : Bool) (c : Option Bool) :
    carryValue (subBit a b c).1 = ((a.toNat : ℤ) - b.toNat + carryValue c) / 2 := by
  cases a <;> cases b <;> cases c with
  | none => decide
  | some c => cases c <;> decide

/-! ## Values of bit lists -/

/-- The value of a concatenation. -/
theorem ofBits_append (l m : List Bool) :
    ofBits (l ++ m) = ofBits l + 2 ^ l.length * ofBits m := by
  revert l
  refine List.rec ?_ ?_
  · simp
  · intro b bs ih
    simp only [List.cons_append, ofBits_cons, Nat.bit_val, ih, List.length_cons, pow_succ]
    ring

/-- A bit list of length {lit}`n` has value less than {lit}`2 ^ n`. -/
theorem ofBits_lt_two_pow (l : List Bool) : ofBits l < 2 ^ l.length := by
  revert l
  refine List.rec ?_ ?_
  · simp
  · intro b bs ih
    have : b.toNat ≤ 1 := by cases b <;> simp
    simp only [ofBits_cons, Nat.bit_val, List.length_cons, pow_succ]
    omega

/-- A list of {lit}`false`s has value zero. -/
theorem ofBits_replicate_false (n : ℕ) : ofBits (List.replicate n false) = 0 := by
  revert n
  refine Nat.rec ?_ ?_
  · rfl
  · intro n ih
    simp [List.replicate_succ, ofBits_cons, Nat.bit_val, ih]

/-- Value zero means every digit is {lit}`false`. -/
theorem ofBits_eq_zero_iff (l : List Bool) : ofBits l = 0 ↔ ∀ b ∈ l, b = false := by
  revert l
  refine List.rec ?_ ?_
  · simp only [ofBits_nil, List.not_mem_nil, false_implies, implies_true]
  · intro b bs ih
    simp only [ofBits_cons, Nat.bit_val, List.mem_cons, forall_eq_or_imp]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine ⟨?_, ih.mp ?_⟩
      · cases b
        · rfl
        · simp only [Bool.toNat_true] at h
          omega
      · cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;> omega
    · rw [h.1, ih.mpr h.2]
      rfl

/-! ## Trailing zeros and the sentinel -/

/-- Remove the trailing {lit}`false`s of a bit list. -/
@[expose] def trim : List Bool → List Bool :=
  List.rec [] fun b _ t ↦ if t.isEmpty && !b then [] else b :: t

/-- An empty list has no significant digits. -/
@[simp] theorem trim_nil : trim [] = [] := rfl

/-- Trimming keeps a head precisely when it or its tail has a significant digit. -/
@[simp] theorem trim_cons (b : Bool) (bs : List Bool) :
    trim (b :: bs) = if (trim bs).isEmpty && !b then [] else b :: trim bs := rfl

/-- Appending a zero does not change the significant prefix. -/
theorem trim_append_false (w : List Bool) : trim (w ++ [false]) = trim w := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    simp only [List.cons_append, trim_cons, ih]

/-- An appended one is the new last significant digit. -/
theorem trim_append_true (w : List Bool) : trim (w ++ [true]) = w ++ [true] := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    simp [ih]

/-- Trimming only shortens a word. -/
theorem length_trim_le (w : List Bool) : (trim w).length ≤ w.length := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    rw [trim_cons]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ ih

/-- The significant digits are an initial segment of the original word. -/
theorem take_length_trim (w : List Bool) : w.take (trim w).length = trim w := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    rw [trim_cons]
    split
    · rfl
    · simpa only [List.length_cons, List.take_succ_cons] using congrArg (b :: ·) ih

/-- Normalization needs only the index of the last significant digit. -/
theorem dropLast_trim_eq_take (w : List Bool) :
    (trim w).dropLast = w.take ((trim w).length - 1) := by
  rw [List.dropLast_eq_take, ← take_length_trim w, List.take_take]
  simp only [List.length_take, Nat.min_eq_left (length_trim_le w), Nat.min_eq_left (Nat.sub_le ..)]

/-- Removing trailing {lit}`false`s preserves the value. -/
theorem ofBits_trim (l : List Bool) : ofBits (trim l) = ofBits l := by
  revert l
  refine List.rec ?_ ?_
  · rfl
  · intro b bs ih
    rw [trim_cons]
    split
    · rename_i h
      simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at ih
      simp [ofBits_nil, ofBits_cons, Nat.bit_val, h2, ← ih]
    · simp [ofBits_cons, Nat.bit_val, ih]

/-- A trimmed nonempty bit list ends in {lit}`true`. -/
theorem getLast?_trim (l : List Bool) (h : trim l ≠ []) : (trim l).getLast? = some true := by
  revert l
  refine List.rec ?_ ?_
  · intro h
    simp at h
  · intro b bs ih h
    by_cases hbs : trim bs = []
    · have hb : b = true := by
        by_contra hb
        simp only [Bool.not_eq_true] at hb
        rw [trim_cons, hbs] at h
        simp [hb] at h
      rw [trim_cons, hbs, hb]
      simp
    · have hc : ((trim bs).isEmpty && !b) = false := by simp [List.isEmpty_iff, hbs]
      rw [trim_cons, hc]
      simp only [Bool.false_eq_true, ite_false]
      rw [List.getLast?_cons_of_ne_nil hbs]
      exact ih hbs

/-- A bit list of value zero trims to the empty list. -/
theorem trim_eq_nil_of_ofBits_eq_zero (l : List Bool) (h : ofBits l = 0) : trim l = [] := by
  by_cases hne : trim l = []
  · exact hne
  · exfalso
    have hmem : true ∈ trim l := List.mem_of_getLast? (getLast?_trim l hne)
    have h0 : ofBits (trim l) = 0 := by rw [ofBits_trim]; exact h
    exact Bool.noConfusion ((ofBits_eq_zero_iff _).mp h0 true hmem)

/-- Stripping trailing {lit}`false`s and then the sentinel inverts {lit}`ofBits`: the result
is the rank notation of the value's predecessor. -/
theorem dropLast_trim (l : List Bool) : (trim l).dropLast = unrank (ofBits l - 1) := by
  by_cases h : ofBits l = 0
  · rw [trim_eq_nil_of_ofBits_eq_zero l h, h]
    rfl
  · have hne : trim l ≠ [] := by
      intro hnil
      exact h (by rw [← ofBits_trim, hnil]; rfl)
    have hlast : (trim l).getLast hne = true := by
      have h1 := getLast?_trim l hne
      rw [List.getLast?_eq_some_getLast hne] at h1
      exact Option.some_injective _ h1
    have hsplit : (trim l).dropLast ++ [true] = trim l := by
      conv_rhs => rw [← List.dropLast_append_getLast hne]
      rw [hlast]
    have hrank : rank ((trim l).dropLast) = ofBits l - 1 := by
      rw [rank, hsplit, ofBits_trim]
    rw [← hrank, unrank_rank]

/-! ## The digitwise scan -/

/-- Pad a bit list with {lit}`false`s to length at least {lit}`n`. -/
@[expose] def padTo (l : List Bool) (n : ℕ) : List Bool :=
  l ++ List.replicate (n - l.length) false

/-- Padding with {lit}`false`s preserves the value. -/
theorem ofBits_padTo (l : List Bool) (n : ℕ) : ofBits (padTo l n) = ofBits l := by
  simp [padTo, ofBits_append, ofBits_replicate_false]

/-- A list padded to a length at least its own has that length. -/
theorem length_padTo (l : List Bool) (n : ℕ) (h : l.length ≤ n) : (padTo l n).length = n := by
  simp [padTo]
  omega

/-- Padding does not change the digits that are read. -/
theorem getD_padTo (l : List Bool) (n j : ℕ) (h : j < n) :
    (padTo l n)[j]?.getD false = l[j]?.getD false := by
  rcases lt_or_ge j l.length with hj | hj
  · rw [padTo, List.getElem?_append_left hj]
  · rw [padTo, List.getElem?_append_right hj, List.getElem?_replicate]
    rw [List.getElem?_eq_none hj]
    have : j - l.length < n - l.length := by omega
    simp [this]

/-- One scan of paired digits: thread the signed carry through the positions, emitting one
digit at each, and return the final carry together with the emitted digits. -/
@[expose] def subDigits : List (Bool × Bool) → ℤ → ℤ × List Bool :=
  List.rec (fun c ↦ (c, [])) fun p _ ih c ↦
    let d : ℤ := (p.1.toNat : ℤ) - (p.2.toNat : ℤ) + c
    let r := ih (d / 2)
    (r.1, decide (d % 2 = 1) :: r.2)

/-- One digit is emitted per position. -/
theorem subDigits_length (ps : List (Bool × Bool)) (c : ℤ) :
    (subDigits ps c).2.length = ps.length := by
  revert ps c
  refine List.rec ?_ ?_
  · intro c
    rfl
  · intro p ps ih c
    exact congrArg Nat.succ (ih (((p.1.toNat : ℤ) - p.2.toNat + c) / 2))

/-- A digit is zero or one. -/
theorem toNat_le_one (a : Bool) : (a.toNat : ℤ) ≤ 1 := by cases a <;> decide

/-- The scan at one position, with the current digits and carry spelled out. -/
theorem subDigits_cons (a b : Bool) (ps : List (Bool × Bool)) (c : ℤ) :
    subDigits ((a, b) :: ps) c =
      ((subDigits ps (((a.toNat : ℤ) - (b.toNat : ℤ) + c) / 2)).1,
        decide (((a.toNat : ℤ) - (b.toNat : ℤ) + c) % 2 = 1) ::
          (subDigits ps (((a.toNat : ℤ) - (b.toNat : ℤ) + c) / 2)).2) := rfl

/-- The finite carry obtained by scanning a prefix of digit pairs. -/
@[expose] def subCarry (ps : List (Bool × Bool)) (c : Option Bool) : Option Bool :=
  ps.foldl (fun c p ↦ (subBit p.1 p.2 c).1) c

/-- The finite representation follows the arithmetic carry exactly. -/
theorem carryValue_subCarry (ps : List (Bool × Bool)) (c : Option Bool) :
    carryValue (subCarry ps c) = (subDigits ps (carryValue c)).1 := by
  revert ps c
  refine List.rec ?_ ?_
  · intro c
    rfl
  · intro p ps ih c
    change carryValue (subCarry ps (subBit p.1 p.2 c).1) = _
    rw [ih, carryValue_subBit]
    rfl

/-- A scan can be resumed from the carry saved after any prefix. -/
theorem subDigits_append (ps qs : List (Bool × Bool)) (c : ℤ) :
    subDigits (ps ++ qs) c =
      ((subDigits qs (subDigits ps c).1).1,
        (subDigits ps c).2 ++ (subDigits qs (subDigits ps c).1).2) := by
  revert ps c
  refine List.rec ?_ ?_
  · intro c
    rfl
  · intro p ps ih c
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, subDigits_cons, ih]

/-- One more digit updates the saved finite carry and appends its output bit. -/
theorem subDigits_append_one (ps : List (Bool × Bool)) (a b : Bool) (c : Option Bool) :
    subDigits (ps ++ [(a, b)]) (carryValue c) =
      (carryValue (subBit a b (subCarry ps c)).1,
        (subDigits ps (carryValue c)).2 ++ [(subBit a b (subCarry ps c)).2]) := by
  rw [subDigits_append, ← carryValue_subCarry, carryValue_subBit]
  rfl

/-- A finite carry also resumes after a prefix. -/
theorem subCarry_append_one (ps : List (Bool × Bool)) (a b : Bool) (c : Option Bool) :
    subCarry (ps ++ [(a, b)]) c = (subBit a b (subCarry ps c)).1 := by
  simp only [subCarry, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Recomputing a prefix produces exactly the corresponding prefix of the output. -/
theorem subDigits_take (ps : List (Bool × Bool)) (c : ℤ) (j : ℕ) (hj : j ≤ ps.length) :
    (subDigits (ps.take j) c).2 = (subDigits ps c).2.take j := by
  have he := congrArg Prod.snd (subDigits_append (ps.take j) (ps.drop j) c)
  rw [List.take_append_drop] at he
  rw [he, List.take_append_of_le_length (by simpa [subDigits_length] using hj)]
  exact (List.take_of_length_le (by simp [subDigits_length, Nat.min_eq_left hj])).symm

/-- The number of digits to emit after the sign and last significant index are known. -/
@[expose] def subOutputLength (ps : List (Bool × Bool)) : ℕ :=
  if (subCarry ps (some true)).isNone then 0 else (trim (subDigits ps 1).2).length - 1

/-- Normalization never needs more digits than were scanned. -/
theorem subOutputLength_le (ps : List (Bool × Bool)) : subOutputLength ps ≤ ps.length := by
  unfold subOutputLength
  split
  · omega
  · have h := length_trim_le (subDigits ps 1).2
    rw [subDigits_length] at h
    omega

/-- The second scan emits the normalized result, or nothing for a negative difference. -/
theorem subDigits_take_subOutputLength (ps : List (Bool × Bool)) :
    (subDigits (ps.take (subOutputLength ps)) 1).2 =
      if 0 ≤ (subDigits ps 1).1 then (trim (subDigits ps 1).2).dropLast else [] := by
  have hc := carryValue_subCarry ps (some true)
  change carryValue (subCarry ps (some true)) = (subDigits ps 1).1 at hc
  rw [subDigits_take ps 1 _ (subOutputLength_le ps), subOutputLength, ← hc]
  cases he : subCarry ps (some true) with
  | none => simp [carryValue]
  | some b =>
    cases b <;> simp [carryValue, dropLast_trim_eq_take]

/-- The carry stays in {lit}`{-1, 0, 1}`. -/
theorem subDigits_carry_mem (ps : List (Bool × Bool)) (c : ℤ) (h0 : -1 ≤ c) (h1 : c ≤ 1) :
    -1 ≤ (subDigits ps c).1 ∧ (subDigits ps c).1 ≤ 1 := by
  revert ps c
  refine List.rec ?_ ?_
  · intro c h0 h1
    exact ⟨h0, h1⟩
  · intro p ps ih c h0 h1
    obtain ⟨a, b⟩ := p
    have ha := toNat_le_one a
    have hb := toNat_le_one b
    have hd0 : -1 ≤ ((a.toNat : ℤ) - (b.toNat : ℤ) + c) / 2 := by omega
    have hd1 : ((a.toNat : ℤ) - (b.toNat : ℤ) + c) / 2 ≤ 1 := by omega
    have hrec := ih _ hd0 hd1
    rw [subDigits_cons]
    exact ⟨hrec.1, hrec.2⟩

/-- The reconstruction invariant: the emitted digits and the final carry together account
for the difference of the two scanned words and the initial carry. -/
theorem subDigits_spec (ps : List (Bool × Bool)) (c : ℤ) :
    (ofBits (subDigits ps c).2 : ℤ) + 2 ^ ps.length * (subDigits ps c).1
      = (ofBits (ps.map Prod.fst) : ℤ) - (ofBits (ps.map Prod.snd) : ℤ) + c := by
  revert ps c
  refine List.rec ?_ ?_
  · intro c
    simp only [subDigits, ofBits_nil, List.map_nil, List.length_nil, pow_zero,
      Nat.cast_zero, one_mul]
    omega
  · intro p ps ih c
    obtain ⟨a, b⟩ := p
    rw [subDigits_cons]
    obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (a.toNat : ℤ) - (b.toNat : ℤ) + c := ⟨_, rfl⟩
    rw [← hd]
    have hih := ih (d / 2)
    have hbit : ((decide (d % 2 = 1)).toNat : ℤ) = d % 2 := by
      rcases Int.emod_two_eq_zero_or_one d with h | h
      · rw [h]; rfl
      · rw [h]; rfl
    obtain ⟨P, hP⟩ : ∃ P : ℤ, P = 2 ^ ps.length * (subDigits ps (d / 2)).1 := ⟨_, rfl⟩
    rw [← hP] at hih
    have hpow : (2 : ℤ) ^ (ps.length + 1) * (subDigits ps (d / 2)).1 = 2 * P := by
      rw [hP, pow_succ, mul_comm ((2 : ℤ) ^ ps.length) 2, mul_assoc]
    simp only [ofBits_cons, Nat.bit_val, List.map_cons, List.length_cons,
      Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, hpow, hbit]
    omega

/-! ## The algorithm on two words -/

/-- The digit pairs scanned for {lit}`v` and {lit}`w`: the sentinelled words, padded with
{lit}`false` to the scan length, paired position by position. -/
@[expose] def bitPairs (v w : List Bool) : List (Bool × Bool) :=
  (padTo (w ++ [true]) (max v.length w.length + 1)).zip
    (padTo (v ++ [true]) (max v.length w.length + 1))

/-- The digitwise difference: scan the digit pairs with initial carry {lit}`1`, and, unless
the final carry is negative, strip the emitted digits of their trailing {lit}`false`s and of
the sentinel. -/
@[expose] def shortlexSub (v w : List Bool) : List Bool :=
  let r := subDigits (bitPairs v w) 1
  if 0 ≤ r.1 then (trim r.2).dropLast else []

/-- The scan length bounds the sentinelled words. -/
theorem length_append_true_le (v w : List Bool) :
    (w ++ [true]).length ≤ max v.length w.length + 1 ∧
      (v ++ [true]).length ≤ max v.length w.length + 1 :=
  ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
    by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- The scan visits one position per digit of the padded words. -/
theorem length_bitPairs (v w : List Bool) :
    (bitPairs v w).length = max v.length w.length + 1 := by
  obtain ⟨hw, hv⟩ := length_append_true_le v w
  simp [bitPairs, length_padTo _ _ hw, length_padTo _ _ hv]

/-- At each position the scan reads the digit of {lit}`w ++ [true]` and the digit of
{lit}`v ++ [true]`, treating positions beyond a word's end as {lit}`false`. -/
theorem bitPairs_getElem (v w : List Bool) (j : ℕ) (hj : j < (bitPairs v w).length) :
    (bitPairs v w)[j] = ((w ++ [true])[j]?.getD false, (v ++ [true])[j]?.getD false) := by
  obtain ⟨hw, hv⟩ := length_append_true_le v w
  have hj' : j < max v.length w.length + 1 := by rwa [length_bitPairs] at hj
  have hjw : j < (padTo (w ++ [true]) (max v.length w.length + 1)).length := by
    rw [length_padTo _ _ hw]; exact hj'
  have hjv : j < (padTo (v ++ [true]) (max v.length w.length + 1)).length := by
    rw [length_padTo _ _ hv]; exact hj'
  have hgw := getD_padTo (w ++ [true]) (max v.length w.length + 1) j hj'
  have hgv := getD_padTo (v ++ [true]) (max v.length w.length + 1) j hj'
  rw [List.getElem?_eq_getElem hjw, Option.getD_some] at hgw
  rw [List.getElem?_eq_getElem hjv, Option.getD_some] at hgv
  have hzip : (bitPairs v w)[j] =
      ((padTo (w ++ [true]) (max v.length w.length + 1))[j]'hjw,
        (padTo (v ++ [true]) (max v.length w.length + 1))[j]'hjv) := List.getElem_zip
  rw [hzip, hgw, hgv]

/-- The first digits scanned are those of {lit}`w ++ [true]`. -/
theorem ofBits_map_fst_bitPairs (v w : List Bool) :
    ofBits ((bitPairs v w).map Prod.fst) = ofBits (w ++ [true]) := by
  obtain ⟨hw, hv⟩ := length_append_true_le v w
  rw [bitPairs, List.map_fst_zip (by rw [length_padTo _ _ hw, length_padTo _ _ hv]),
    ofBits_padTo]

/-- The second digits scanned are those of {lit}`v ++ [true]`. -/
theorem ofBits_map_snd_bitPairs (v w : List Bool) :
    ofBits ((bitPairs v w).map Prod.snd) = ofBits (v ++ [true]) := by
  obtain ⟨hw, hv⟩ := length_append_true_le v w
  rw [bitPairs, List.map_snd_zip (by rw [length_padTo _ _ hw, length_padTo _ _ hv]),
    ofBits_padTo]

/-- The scan of two words: the emitted digits and the final carry account for the difference
of the two sentinelled words, plus one. -/
theorem bitPairs_spec (v w : List Bool) :
    (ofBits (subDigits (bitPairs v w) 1).2 : ℤ)
        + 2 ^ (max v.length w.length + 1) * (subDigits (bitPairs v w) 1).1
      = (ofBits (w ++ [true]) : ℤ) - (ofBits (v ++ [true]) : ℤ) + 1 := by
  have := subDigits_spec (bitPairs v w) 1
  rw [length_bitPairs, ofBits_map_fst_bitPairs, ofBits_map_snd_bitPairs] at this
  exact this

/-- The digitwise difference of two words is the word of rank {lit}`rank w - rank v`. -/
theorem shortlexSub_eq_numericSub (v w : List Bool) : shortlexSub v w = numericSub v w := by
  obtain ⟨hw, hv⟩ := length_append_true_le v w
  set L := max v.length w.length + 1 with hL
  set r := subDigits (bitPairs v w) 1 with hr
  have hspec := bitPairs_spec v w
  rw [← hL, ← hr] at hspec
  have hcarry : -1 ≤ r.1 ∧ r.1 ≤ 1 := by
    rw [hr]; exact subDigits_carry_mem _ 1 (by decide) (by decide)
  have hlen : r.2.length = L := by rw [hr, subDigits_length, length_bitPairs]
  have hcastpow : ((2 ^ L : ℕ) : ℤ) = (2 : ℤ) ^ L := Nat.cast_pow 2 L
  have hbound : (ofBits r.2 : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    have h := ofBits_lt_two_pow r.2
    rw [hlen] at h
    omega
  have hA : (ofBits (w ++ [true]) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    have h1 := ofBits_lt_two_pow (w ++ [true])
    have h2 : (2 : ℕ) ^ (w ++ [true]).length ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hw
    have h3 : ofBits (w ++ [true]) < 2 ^ L := lt_of_lt_of_le h1 h2
    omega
  have hA1 : (1 : ℤ) ≤ (ofBits (w ++ [true]) : ℤ) := by
    have h := Nat.succ_le_of_lt (Geb.BitTreeScanner.ofBits_append_true_pos w)
    omega
  have hB1 : (1 : ℤ) ≤ (ofBits (v ++ [true]) : ℤ) := by
    have h := Nat.succ_le_of_lt (Geb.BitTreeScanner.ofBits_append_true_pos v)
    omega
  have hrkA : (ofBits (w ++ [true]) : ℤ) = (rank w : ℤ) + 1 := by
    have h := (rank_add_one w).symm
    omega
  have hrkB : (ofBits (v ++ [true]) : ℤ) = (rank v : ℤ) + 1 := by
    have h := (rank_add_one v).symm
    omega
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ((2 ^ L : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hcastpow, ← hT] at hspec
  rw [← hT] at hbound hA
  have hpos : (0 : ℤ) ≤ (ofBits r.2 : ℤ) := Int.natCast_nonneg _
  rw [hrkA, hrkB] at hspec
  rw [shortlexSub, numericSub, ← hr]
  split
  · rename_i hc
    rw [dropLast_trim]
    have hc0 : r.1 = 0 := by
      by_cases h : r.1 = 0
      · exact h
      · have h1 : r.1 = 1 := by
          have hc2 := hcarry.2
          omega
        rw [h1, mul_one] at hspec
        exfalso
        omega
    rw [hc0, mul_zero] at hspec
    have : ofBits r.2 - 1 = rank w - rank v := by omega
    rw [this]
  · rename_i hc
    have hc1 : r.1 = -1 := by
      have h1 := hcarry.1
      omega
    rw [hc1, mul_neg_one] at hspec
    have : rank w - rank v = 0 := by omega
    rw [this, unrank_zero]

end

end Geb.Oitavem
