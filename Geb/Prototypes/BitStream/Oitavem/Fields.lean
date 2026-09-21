/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Sig
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigEdge
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The numerals of a label as expressions

A label of the bundle signature is a set bit, five tag bits and eight coded
numbers. From a pointer to the label, held as an end segment of the word,
the pointer to each numeral is the numeral scanner's end at the pointer to
the one before, and the atomic constraints of the signature's table are
the comparisons of numerals at two pointers: the equality and order tests
and the sum check of the size-bounded algebra's recognizer, the sum check
with the label's set bit as its coded zero for a successor relation, and
the reading of a numeral into a counter compared with a constant. When the
word holds the codes of a list of numbers past the tag, each pointer lies
at its numeral and each constraint's expression reads as the constraint at
the numbers; and when the scanner accepts at each of a number of pointers,
the word holds that many codes there.

# Main definitions

* {lit}`dropC`, {lit}`fieldPtr`, {lit}`fpos` — a pointer advanced by a
  constant, the pointer to a numeral, and the position of a numeral.
* {lit}`constAt` — the numeral at a pointer is a constant.
* {lit}`atomBounded`, {lit}`atomExpr`, {lit}`atomsExpr` — a constraint
  whose constant fits any label, and a constraint, and a table of
  constraints, as expressions.

# Main statements

* {lit}`drop_fpos`, {lit}`sem_fieldPtr`, {lit}`ok_fieldPtr` — on a word
  holding codes past the tag, the pointers lie at the numerals and the
  scanner accepts at each.
* {lit}`fields_of_ok` — when the scanner accepts at a number of pointers,
  the word holds that many codes.
* {lit}`sem_atom`, {lit}`sem_atomsExpr` — a constraint's expression reads
  as the constraint at the numbers, and a table's as the check of the
  table.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, binary numeral, coded signature, label
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem.FieldExpr

open Geb.SizeBounded.Logspace (LOf tailAppL sem_tailAppL constL sem_constL)
open Geb.SizeBounded.Logspace.WTree (boolWord isTrueWord eqSeg sem_eqSeg)
open Geb.SizeBounded.Logspace.WTree.Numeral (natCode)
open Geb.SizeBounded.Logspace.WTree.NumExpr (drop_min_length)
open Geb.SizeBounded.Logspace.WTree.SigLabel
open Geb.SizeBounded.Logspace.WTree.SigEdge (orF sem_orF)
open Geb.BitStream.Oitavem (Fields Atom codes ofList)

public section

variable {n : ℕ}

/-- A pointer advanced by a constant number of bits. -/
@[expose] def dropC : ℕ → LOf n → LOf n
  | 0, p => p
  | k + 1, p => tailAppL (dropC k p)

/-- The advanced pointer's meaning. -/
theorem sem_dropC (k : ℕ) (p : LOf n) (x : Fin n → List Bool) (y : List Bool) (pos : ℕ)
    (hp : p.sem x = y.drop pos) : (dropC k p).sem x = y.drop (pos + k) := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [dropC, sem_tailAppL, ih, List.tail_drop, Nat.add_assoc]

/-- The pointer to a numeral of a label: past the six header bits, then the
scanner's end at the pointer to each numeral before. -/
@[expose] def fieldPtr (W p : LOf n) : ℕ → LOf n
  | 0 => dropC 6 p
  | i + 1 => numEndAt W (fieldPtr W p i)

/-- The position of a numeral: past the header and the codes before it. -/
@[expose] def fpos (pos : ℕ) (l : List ℕ) (i : ℕ) : ℕ :=
  pos + 6 + ((l.take i).map fun m ↦ (natCode m).length).sum

/-- The position of the first numeral. -/
theorem fpos_zero (pos : ℕ) (l : List ℕ) : fpos pos l 0 = pos + 6 := by
  simp only [fpos, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]

/-- The position of the next numeral. -/
theorem fpos_succ (pos : ℕ) (l : List ℕ) (i : ℕ) (h : i < l.length) :
    fpos pos l (i + 1) = fpos pos l i + (natCode l[i]).length := by
  simp only [fpos, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_assoc]

/-- The codes of a list split at a position. -/
theorem codes_drop (l : List ℕ) (i : ℕ) (h : i < l.length) :
    codes (l.drop i) = natCode l[i] ++ codes (l.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- The length of the codes of a list. -/
theorem length_codes (l : List ℕ) : (codes l).length = (l.map fun m ↦ (natCode m).length).sum := by
  simp only [codes, List.length_flatMap]

section Parse

variable (x : Fin n → List Bool) (y : List Bool) (W p : LOf n) (pos : ℕ) (l : List ℕ)
  (rest : List Bool) (hW : W.sem x = y) (hp : p.sem x = y.drop pos) (hpos : pos + 6 ≤ y.length)
  (hy : y.drop (pos + 6) = codes l ++ rest)

include hy in
/-- The word from a numeral's position: the codes from that numeral, then
the rest. -/
theorem drop_fpos : ∀ i, i ≤ l.length → y.drop (fpos pos l i) = codes (l.drop i) ++ rest
  | 0, _ => by rw [fpos_zero, hy, List.drop_zero]
  | i + 1, h => by
    rw [fpos_succ pos l i h, ← List.drop_drop, drop_fpos i (Nat.le_of_lt h), codes_drop l i h,
      List.append_assoc, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append]

include hy in
/-- The word from a numeral's position: its code, then the codes after it
and the rest. -/
theorem drop_fpos_cons (i : ℕ) (h : i < l.length) :
    y.drop (fpos pos l i) = natCode l[i] ++ (codes (l.drop (i + 1)) ++ rest) := by
  rw [drop_fpos y pos l rest hy i (Nat.le_of_lt h), codes_drop l i h, List.append_assoc]

include hpos hy in
/-- A numeral's position lies within the word. -/
theorem fpos_le (i : ℕ) : fpos pos l i ≤ y.length := by
  have hd := congrArg List.length hy
  rw [List.length_drop, List.length_append, length_codes] at hd
  have hi : ((l.take i).map fun m ↦ (natCode m).length).sum ≤
      (l.map fun m ↦ (natCode m).length).sum := by
    rw [← List.take_append_drop i l, List.map_append, List.sum_append, List.take_append_drop]
    exact Nat.le_add_right _ _
  unfold fpos
  omega

include hW hp hpos hy in
/-- The pointer to a numeral lies at its position. -/
theorem sem_fieldPtr : ∀ i, i ≤ l.length → (fieldPtr W p i).sem x = y.drop (fpos pos l i)
  | 0, _ => by rw [fieldPtr, sem_dropC 6 p x y pos hp, fpos_zero]
  | i + 1, h => by
    rw [fieldPtr, sem_numEndAt x y W _ _ hW (sem_fieldPtr i (Nat.le_of_lt h))
      (fpos_le y pos l rest hpos hy i), endPos_of y _ l[i] _ (drop_fpos_cons y pos l rest hy i h),
      fpos_succ pos l i h]

include hW hp hpos hy in
/-- The scanner accepts at the pointer to every numeral. -/
theorem ok_fieldPtr (i : ℕ) (h : i < l.length) : (numOkAt W (fieldPtr W p i)).sem x = [true] := by
  rw [sem_numOkAt x y W _ _ hW (sem_fieldPtr x y W p pos l rest hW hp hpos hy i (Nat.le_of_lt h))
    (fpos_le y pos l rest hpos hy i)]
  rw [show nrunOk y (fpos pos l i) = true from (nrunOk_iff y _).mpr
    ⟨l[i], _, drop_fpos_cons y pos l rest hy i h⟩]
  rfl

include hW hp hpos hy in
/-- The word splits at a numeral: the word before it, its code and the word
after it. -/
theorem split_fieldPtr (i : ℕ) (h : i < l.length) :
    (fieldPtr W p i).sem x = y.drop (fpos pos l i) ∧
      y = y.take (fpos pos l i) ++ natCode l[i] ++ codes (l.drop (i + 1)) ++ rest ∧
      (y.take (fpos pos l i)).length = fpos pos l i := by
  obtain ⟨hy', hu⟩ :=
    split_at y _ _ (natCode_append_ne_nil _ _) (drop_fpos_cons y pos l rest hy i h)
  exact ⟨sem_fieldPtr x y W p pos l rest hW hp hpos hy i (Nat.le_of_lt h),
    by rw [List.append_assoc, List.append_assoc]; exact hy', hu⟩

end Parse

/-- When the scanner accepts at a number of pointers, the word holds that
many codes past the header. -/
theorem fields_of_ok (x : Fin n → List Bool) (y : List Bool) (W p : LOf n) (pos : ℕ)
    (hW : W.sem x = y) (hp : p.sem x = y.drop pos) (hpos : pos + 6 ≤ y.length) : ∀ k : ℕ,
    (∀ i < k, (numOkAt W (fieldPtr W p i)).sem x = [true]) →
      ∃ (l : List ℕ) (rest : List Bool), l.length = k ∧ y.drop (pos + 6) = codes l ++ rest
  | 0, _ => ⟨[], y.drop (pos + 6), rfl, rfl⟩
  | k + 1, hok => by
    obtain ⟨l, rest, hl, hy⟩ := fields_of_ok x y W p pos hW hp hpos k fun i hi ↦
      hok i (Nat.lt_succ_of_lt hi)
    have hptr := sem_fieldPtr x y W p pos l rest hW hp hpos hy k (Nat.le_of_eq hl.symm)
    have hrest : y.drop (fpos pos l k) = rest := by
      have h := drop_fpos y pos l rest hy k (Nat.le_of_eq hl.symm)
      rw [List.drop_of_length_le (Nat.le_of_eq hl)] at h
      exact h
    obtain ⟨m, rest', hm, _⟩ := numOkAt_eq x y W _ _ hW hptr
      (fpos_le y pos l rest hpos hy k) (hok k (Nat.lt_succ_self k))
    refine ⟨l ++ [m], rest', by rw [List.length_append, hl]; rfl, ?_⟩
    rw [hy, show codes (l ++ [m]) = codes l ++ natCode m by
      simp only [codes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil],
      List.append_assoc, ← hm, hrest]

/-- The numeral at a pointer is a constant: the reading into a counter
compared with the word dropped by the constant. -/
@[expose] def constAt (c : ℕ) (W q : LOf n) : LOf n := eqSeg (natValueAt W q) (dropC c W)

/-- The constant test's meaning at a pointer to a coded number, for a
constant below the word's length. -/
theorem sem_constAt (c : ℕ) (W q : LOf n) (x : Fin n → List Bool) (y : List Bool) (hW : W.sem x = y)
    (hc : c < y.length) (tq A : ℕ) (uq rq : List Bool) (hq : q.sem x = y.drop tq)
    (huq : uq.length = tq) (hy : y = uq ++ natCode A ++ rq) :
    (constAt c W q).sem x = boolWord (decide (A = c)) := by
  rw [constAt, sem_eqSeg _ _ x y (min A y.length) c
    (by rw [natValueAt_natCode x y W q uq rq A tq hW hq huq hy, drop_min_length])
    (by rw [sem_dropC c W x y 0 (by rw [hW, List.drop_zero]), Nat.zero_add])
    (Nat.min_le_right _ _) (Nat.le_of_lt hc)]
  exact boolWord_decide_congr _ _ ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- A constraint is bounded when its constant, if any, is at most three, so
that it lies below the length of any word holding a label. -/
@[expose] def atomBounded : Atom → Bool
  | .const _ c => decide (c ≤ 3)
  | _ => true

/-- A constraint as an expression at the word and a pointer to the label:
the comparison of the numerals at the pointers, the label's set bit as the
coded zero of a successor relation. -/
@[expose] def atomExpr (W p : LOf n) : Atom → LOf n
  | .eq i j => natEqAt W (fieldPtr W p i) (fieldPtr W p j)
  | .const i c => constAt c W (fieldPtr W p i)
  | .succ i j => natSumAt true W (fieldPtr W p i) p (fieldPtr W p j)
  | .lt i j => natLtAt W (fieldPtr W p i) (fieldPtr W p j)
  | .bit i => orF (constAt 0 W (fieldPtr W p i)) (constAt 1 W (fieldPtr W p i))

/-- The code of zero is one set bit. -/
theorem natCode_zero : natCode 0 = [true] := rfl

/-- A number's list entry, as numerals. -/
theorem ofList_getElem (l : List ℕ) (i : Fin 8) (h : l.length = 8) :
    ofList l i = l[i.1]'(by rw [h]; exact i.2) := by
  simp only [ofList, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i.1 < l.length by rw [h]; exact i.2), Option.getD_some]

section Atoms

variable (x : Fin n → List Bool) (y : List Bool) (W p : LOf n) (pos : ℕ) (l : List ℕ)
  (rest : List Bool) (hW : W.sem x = y) (hp : p.sem x = y.drop pos) (hl : l.length = 8)
  (hy : y.drop (pos + 6) = codes l ++ rest) (hzero : y.drop pos = true :: y.drop (pos + 1))

include hW hp hl hy in
/-- The numeral at a field pointer, with the word split there. -/
theorem field_split (i : ℕ) (hi : i < 8) :
    (fieldPtr W p i).sem x = y.drop (fpos pos l i) ∧
      y = y.take (fpos pos l i) ++ natCode (ofList l ⟨i, hi⟩) ++ (codes (l.drop (i + 1)) ++ rest) ∧
      (y.take (fpos pos l i)).length = fpos pos l i := by
  have hpos : pos + 6 ≤ y.length := by
    have hd := congrArg List.length hy
    have h0 := codes_drop l 0 (by omega)
    rw [List.drop_zero] at h0
    rw [List.length_drop, List.length_append, h0, List.length_append] at hd
    have := Geb.SizeBounded.Logspace.WTree.Numeral.length_natCode l[0]
    omega
  obtain ⟨h1, h2, h3⟩ := split_fieldPtr x y W p pos l rest hW hp hpos hy i (by rw [hl]; exact hi)
  refine ⟨h1, ?_, h3⟩
  rw [ofList_getElem l ⟨i, hi⟩ hl, ← List.append_assoc]
  exact h2

include hW hp hl hy hzero in
/-- A constraint's expression reads as the constraint at the numbers. -/
theorem sem_atom (h6 : pos + 6 ≤ y.length) : ∀ a : Atom, atomBounded a = true →
    (atomExpr W p a).sem x = boolWord (a.holds (ofList l))
  | .eq i j, _ => by
    obtain ⟨hi1, hi2, hi3⟩ := field_split x y W p pos l rest hW hp hl hy i.1 i.2
    obtain ⟨hj1, hj2, hj3⟩ := field_split x y W p pos l rest hW hp hl hy j.1 j.2
    exact natEqAt_natCode x y W _ _ _ _ _ _ _ _ _ _ hW hi1 hj1 hi3 hi2 hj3 hj2
  | .const i c, hc => by
    obtain ⟨hi1, hi2, hi3⟩ := field_split x y W p pos l rest hW hp hl hy i.1 i.2
    have hc' : c ≤ 3 := of_decide_eq_true hc
    exact sem_constAt c W _ x y hW (by omega) _ _ _ _ hi1 hi3 hi2
  | .succ i j, _ => by
    obtain ⟨hi1, hi2, hi3⟩ := field_split x y W p pos l rest hW hp hl hy i.1 i.2
    obtain ⟨hj1, hj2, hj3⟩ := field_split x y W p pos l rest hW hp hl hy j.1 j.2
    have hz : y = y.take pos ++ natCode 0 ++ y.drop (pos + 1) := by
      rw [natCode_zero, List.append_assoc, List.singleton_append, ← hzero, List.take_append_drop]
    change (natSumAt true W (fieldPtr W p i) p (fieldPtr W p j)).sem x = _
    rw [natSumAt_natCode x y true W _ p _ _ _ _ _ _ _ (ofList l i) 0 (ofList l j) _ _ _
      hW hi1 hp hj1 hi3 hi2 (List.length_take_of_le (by omega)) hz hj3 hj2]
    change _ = boolWord (decide (ofList l j = ofList l i + 1))
    exact boolWord_decide_congr _ _ ⟨fun h ↦ by simp only [Bool.toNat_true] at h; omega,
      fun h ↦ by simp only [Bool.toNat_true]; omega⟩
  | .lt i j, _ => by
    obtain ⟨hi1, hi2, hi3⟩ := field_split x y W p pos l rest hW hp hl hy i.1 i.2
    obtain ⟨hj1, hj2, hj3⟩ := field_split x y W p pos l rest hW hp hl hy j.1 j.2
    exact natLtAt_natCode x y W _ _ _ _ _ _ _ _ _ _ hW hi1 hj1 hi3 hi2 hj3 hj2
  | .bit i, _ => by
    obtain ⟨hi1, hi2, hi3⟩ := field_split x y W p pos l rest hW hp hl hy i.1 i.2
    change (orF (constAt 0 W (fieldPtr W p i)) (constAt 1 W (fieldPtr W p i))).sem x = _
    rw [sem_orF _ _ x _ _ (sem_constAt 0 W _ x y hW (by omega) _ _ _ _ hi1 hi3 hi2)
      (sem_constAt 1 W _ x y hW (by omega) _ _ _ _ hi1 hi3 hi2)]
    change _ = boolWord (decide (ofList l i ≤ 1))
    rw [show (⟨i.1, i.2⟩ : Fin 8) = i from rfl]
    congr 1
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
    constructor <;> intro h <;> omega

/-- A table of constraints as an expression: the conjunction of the
constraints' expressions. -/
@[expose] def atomsExpr (W p : LOf n) : List Atom → LOf n
  | [] => constL n [true]
  | a :: as => andF (atomExpr W p a) (atomsExpr W p as)

include hW hp hl hy hzero in
/-- A table's expression reads as the check of the table at the numbers. -/
theorem sem_atomsExpr (h6 : pos + 6 ≤ y.length) : ∀ as : List Atom,
    (∀ a ∈ as, atomBounded a = true) →
    (atomsExpr W p as).sem x = boolWord (as.all (Atom.holds (ofList l)))
  | [], _ => sem_constL n [true] x
  | a :: as, hb => by
    rw [atomsExpr, sem_andF _ _ x _ _
      (sem_atom x y W p pos l rest hW hp hl hy hzero h6 a (hb a List.mem_cons_self))
      (sem_atomsExpr h6 as fun a' ha' ↦ hb a' (List.mem_cons_of_mem a ha')), List.all_cons]

end Atoms

end

end Geb.BitStream.Oitavem.FieldExpr
