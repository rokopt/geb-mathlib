/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Fields
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The label check of the bundle signature as an expression

The label condition of the bundle signature, {name}`Geb.BitStream.Oitavem.coded`,
as an expression of arity four: at the word, the remaining word from a
label, the word dropped by one more than the label's length, and the word
dropped by a node's arity, it decides whether the label is the code of a
shape with that arity. The label's first bit is tested, the five tag bits
are read by a dispatch and select the constructor's table of constraints,
the numeral scanner is run at the eight numeral pointers, the last pointer
is compared with the label's end, the table is evaluated at the numerals,
and the arity is compared with the seventh numeral read into a counter.

# Main definitions

* {lit}`onBits` — the dispatch on a number of bits at a pointer.
* {lit}`oksExpr` — the scanner's acceptance at each of a number of numeral
  pointers.
* {lit}`kindOk`, {lit}`labelOk` — the check at a constructor, and the label
  check.

# Main statements

* {lit}`sem_onBits`, {lit}`sem_onBits_short` — the dispatch selects by the
  bits, and yields the empty word when fewer bits remain.
* {lit}`computesLabel` — the label check computes the signature's label
  condition on every word.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, coded signature, label, recognizer
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem.LabelExpr

open Geb.SizeBounded.Logspace (LOf tailAppL sem_tailAppL constL sem_constL)
open Geb.SizeBounded.Logspace.WTree (CodedSig boolWord isTrueWord isTrueWord_boolWord eqSeg
  sem_eqSeg onBitAt sem_onBitAt Loc labelAt)
open Geb.SizeBounded.Logspace.WTree.Numeral (natCode)
open Geb.SizeBounded.Logspace.WTree.NumExpr (drop_min_length)
open Geb.SizeBounded.Logspace.WTree.SigLabel
open Geb.Oitavem (Shape)
open Geb.BitStream.Oitavem
open Geb.BitStream.Oitavem.FieldExpr

public section

variable {n : ℕ}

/-- The dispatch on a number of bits at a pointer: the expression at the
bits read, the empty word when fewer bits remain. -/
@[expose] def onBits (p : LOf n) : ℕ → (List Bool → LOf n) → LOf n
  | 0, f => f []
  | k + 1, f =>
    onBitAt p (constL n []) (onBits (tailAppL p) k fun bs ↦ f (true :: bs))
      (onBits (tailAppL p) k fun bs ↦ f (false :: bs))

/-- The dispatch selects the expression at the bits at the pointer. -/
theorem sem_onBits (x : Fin n → List Bool) : ∀ (k : ℕ) (p : LOf n) (f : List Bool → LOf n)
    (bs r : List Bool), bs.length = k → p.sem x = bs ++ r → (onBits p k f).sem x = (f bs).sem x
  | 0, p, f, bs, r, hbs, _ => by
    rw [List.length_eq_zero_iff] at hbs
    rw [hbs]
    rfl
  | k + 1, p, f, bs, r, hbs, hp => by
    cases bs with
    | nil => cases hbs
    | cons b bs =>
      rw [List.length_cons, Nat.add_right_cancel_iff] at hbs
      rw [List.cons_append] at hp
      have ht : (tailAppL p).sem x = bs ++ r := by rw [sem_tailAppL, hp]; rfl
      rw [onBits, sem_onBitAt _ _ _ _ x b _ hp]
      cases b
      · rw [ite_eq_right (by decide)]
        exact sem_onBits x k _ _ bs r hbs ht
      · rw [ite_eq_left rfl]
        exact sem_onBits x k _ _ bs r hbs ht

/-- The dispatch yields the empty word when fewer bits remain at the pointer
than it reads. -/
theorem sem_onBits_short (x : Fin n → List Bool) : ∀ (k : ℕ) (p : LOf n) (f : List Bool → LOf n)
    (bs : List Bool), bs.length < k → p.sem x = bs → (onBits p k f).sem x = []
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, p, f, bs, hbs, hp => by
    cases bs with
    | nil => rw [onBits, sem_onBitAt_nil _ _ _ _ x hp, sem_constL]
    | cons b bs =>
      rw [List.length_cons, Nat.add_lt_add_iff_right] at hbs
      have ht : (tailAppL p).sem x = bs := by rw [sem_tailAppL, hp]; rfl
      rw [onBits, sem_onBitAt _ _ _ _ x b _ hp]
      cases b
      · rw [ite_eq_right (by decide)]
        exact sem_onBits_short x k _ _ bs hbs ht
      · rw [ite_eq_left rfl]
        exact sem_onBits_short x k _ _ bs hbs ht

/-- Every numeral pointer is an end segment of the word. -/
theorem fieldPtr_seg (x : Fin n → List Bool) (y : List Bool) (W p : LOf n) (pos : ℕ)
    (hW : W.sem x = y) (hp : p.sem x = y.drop pos) :
    ∀ i, ∃ t, t ≤ y.length ∧ (fieldPtr W p i).sem x = y.drop t
  | 0 => by
    rw [fieldPtr, sem_dropC 6 p x y pos hp]
    rcases Nat.le_total (pos + 6) y.length with h | h
    · exact ⟨pos + 6, h, rfl⟩
    · exact ⟨y.length, Nat.le_refl _, by rw [List.drop_of_length_le h, List.drop_length]⟩
  | i + 1 => by
    obtain ⟨t, ht, hptr⟩ := fieldPtr_seg x y W p pos hW hp i
    rw [fieldPtr, sem_numEndAt x y W _ t hW hptr ht]
    exact ⟨_, nrun_endPos_le t 0 y, rfl⟩

/-- The scanner's acceptance at each of a number of numeral pointers. -/
@[expose] def oksExpr (W p : LOf n) : ℕ → LOf n
  | 0 => constL n [true]
  | i + 1 => andF (numOkAt W (fieldPtr W p i)) (oksExpr W p i)

/-- The acceptances' meaning: the flag of the scanner accepting at every
pointer. -/
theorem sem_oksExpr (x : Fin n → List Bool) (y : List Bool) (W p : LOf n) (pos : ℕ)
    (hW : W.sem x = y) (hp : p.sem x = y.drop pos) : ∀ k, (oksExpr W p k).sem x =
      boolWord (decide (∀ i < k, (numOkAt W (fieldPtr W p i)).sem x = [true]))
  | 0 => by
    rw [oksExpr, sem_constL, boolWord_decide, ite_eq_left fun i hi ↦ absurd hi (Nat.not_lt_zero i)]
  | k + 1 => by
    obtain ⟨t, ht, hptr⟩ := fieldPtr_seg x y W p pos hW hp k
    rw [oksExpr, sem_andF _ _ x _ _ (sem_numOkAt x y W _ t hW hptr ht)
      (sem_oksExpr x y W p pos hW hp k)]
    refine congrArg boolWord ?_
    have hk : (numOkAt W (fieldPtr W p k)).sem x = [true] ↔ nrunOk y t = true := by
      rw [sem_numOkAt x y W _ t hW hptr ht]
      cases nrunOk y t <;> decide
    rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact hk.mpr h1
    · intro h
      exact ⟨hk.mp (h k (Nat.lt_succ_self k)), fun i hi ↦ h i (Nat.lt_succ_of_lt hi)⟩

/-- The check at a constructor: the scanner accepts at the eight numeral
pointers, the last pointer ends at the label's end, the constructor's table
holds at the numerals, and the arity is the seventh numeral. -/
@[expose] def kindOk (kd : Kind) : LOf 4 :=
  andF (oksExpr W4 L4 8)
    (andF (endsAt (fieldPtr W4 L4 8) R4)
      (andF (atomsExpr W4 L4 (atoms kd)) (eqSeg K4 (natValueAt W4 (fieldPtr W4 L4 6)))))

/-- The label check: the label's set bit, the dispatch on the tag, and the
check at the constructor the tag reads to. -/
@[expose] def labelOk : LOf 4 :=
  onBitAt L4 (constL 4 [])
    (onBits (tailAppL L4) 5 fun bs ↦ (readTag bs).elim (constL 4 []) kindOk)
    (constL 4 [])

/-- Every constraint of every table is bounded. -/
theorem atoms_bounded (kd : Kind) : ∀ a ∈ atoms kd, atomBounded a = true := by
  cases kd <;> decide

/-- Five bits that read to a constructor are its tag. -/
theorem tag_of_readTag' (bs : List Bool) (h5 : bs.length = 5) (kd : Kind)
    (h : readTag bs = some kd) : bs = tag kd := by
  match bs, h5, h with
  | [b0, b1, b2, b3, b4], _, h => exact tag_of_readTag b0 b1 b2 b3 b4 kd h

/-- A shape built from numerals has the table holding at them. -/
theorem check_eq_true_of_build {kd : Kind} {fs : Fields} {a : Option Shape}
    (h : build kd fs = some a) : check kd fs = true := by
  unfold build at h
  split at h
  · assumption
  · cases h

/-- The code of a shape, unfolded. -/
theorem code_eq (a : Option Shape) :
    code a = true :: (tag (kind a) ++ codes (List.ofFn (fields a))) := rfl

/-- The word from a label that is a code. -/
theorem drop_of_label (y : List Bool) (l : Loc) (a : Option Shape) (ha : labelAt y l = code a) :
    y.drop l.pos = true :: (tag (kind a) ++
      (codes (List.ofFn (fields a)) ++ y.drop (l.pos + l.len))) := by
  rw [← label_append y l, ha, code_eq, List.cons_append, List.append_assoc]

/-- The word dropped by six more than a position. -/
theorem drop_add_six (y : List Bool) (pos : ℕ) : y.drop (pos + 6) = (y.drop pos).drop 6 := by
  rw [List.drop_drop, Nat.add_comm]

section Correct

variable (y : List Bool) (l : Loc) (k : ℕ) (hs : Loc.Sound y l) (hk : k + 1 ≤ y.length)

include hs in
/-- A label that is a code: the word from it begins with a set bit, the tag
and the codes of the numerals; the label has at least six bits; the numerals
lie past the header; and the label's length is the header's and the codes'. -/
theorem of_label_code (a : Option Shape) (ha : labelAt y l = code a) :
    y.drop l.pos = true :: (tag (kind a) ++
        (codes (List.ofFn (fields a)) ++ y.drop (l.pos + l.len))) ∧
      6 ≤ l.len ∧
      y.drop (l.pos + 6) = codes (List.ofFn (fields a)) ++ y.drop (l.pos + l.len) ∧
      l.len = 6 + (codes (List.ofFn (fields a))).length := by
  have hd := drop_of_label y l a ha
  have hlen := length_label y l hs
  rw [ha, code_eq, List.length_cons, List.length_append, length_tag] at hlen
  refine ⟨hd, by omega, ?_, by omega⟩
  rw [drop_add_six, hd, List.drop_succ_cons, List.drop_left' (length_tag _)]

/-- An appended list cut past its first part. -/
theorem take_append_length_add {α : Type} (l₁ l₂ : List α) (c : ℕ) :
    (l₁ ++ l₂).take (l₁.length + c) = l₁ ++ l₂.take c := by
  induction l₁ with
  | nil => simp only [List.length_nil, Nat.zero_add, List.nil_append]
  | cons a l ih =>
    rw [List.cons_append, List.length_cons, Nat.add_right_comm, List.take_succ_cons, ih]
    rfl

/-- The label at a location whose word begins with a set bit and five more
bits, cut at the label's length. -/
theorem labelAt_of_form (bs r : List Bool) (hw : y.drop l.pos = true :: (bs ++ r))
    (hbs : bs.length = 5) (c : ℕ) (hlen : l.len = 6 + c) :
    labelAt y l = true :: (bs ++ r.take c) := by
  rw [labelAt, hw, hlen, show 6 + c = (5 + c) + 1 by omega, List.take_succ_cons,
    show 5 + c = bs.length + c by omega, take_append_length_add]

/-- A word either begins with a set bit and five more bits, or does not. -/
theorem form_or (w : List Bool) :
    (∃ bs r : List Bool, bs.length = 5 ∧ w = true :: (bs ++ r)) ∨
      ∀ bs r : List Bool, bs.length = 5 → w ≠ true :: (bs ++ r) := by
  rcases w with _ | ⟨_ | _, w'⟩
  · exact Or.inr fun _ _ _ h ↦ by cases h
  · exact Or.inr fun _ _ _ h ↦ by cases (List.cons.inj h).1
  · by_cases h5 : 5 ≤ w'.length
    · exact Or.inl ⟨w'.take 5, w'.drop 5, List.length_take_of_le h5,
        by rw [List.take_append_drop]⟩
    · refine Or.inr fun bs r hbs h ↦ h5 ?_
      have := congrArg List.length (List.cons.inj h).2
      rw [List.length_append, hbs] at this
      omega

/-- The label check at a label that does not begin with a set bit and five
more bits: the empty word. -/
theorem sem_labelOk_short (h : ∀ bs r : List Bool, bs.length = 5 →
    y.drop l.pos ≠ true :: (bs ++ r)) : labelOk.sem (envL y l k) = [] := by
  rw [labelOk]
  rcases hw : y.drop l.pos with _ | ⟨_ | _, w'⟩
  · rw [sem_onBitAt_nil _ _ _ _ _ (by rw [sem_L4, hw]), sem_constL]
  · rw [sem_onBitAt _ _ _ _ _ false w' (by rw [sem_L4, hw]), ite_eq_right (by decide), sem_constL]
  · rw [sem_onBitAt _ _ _ _ _ true w' (by rw [sem_L4, hw]), ite_eq_left rfl]
    refine sem_onBits_short _ 5 _ _ w' ?_ (by rw [sem_tailAppL, sem_L4, hw]; rfl)
    by_contra hlen
    rw [Nat.not_lt] at hlen
    exact h (w'.take 5) (w'.drop 5) (List.length_take_of_le hlen)
      (by rw [hw, List.take_append_drop])

include hs hk in
/-- At a sound label and an arity below the word's length, the label check
reads as the signature's label condition. -/
theorem labelOk_eq :
    isTrueWord (labelOk.sem (envL y l k)) = coded.labelSpec (labelAt y l) k := by
  rw [Bool.eq_iff_iff, labelSpec_eq_true_iff]
  rcases form_or (y.drop l.pos) with ⟨bs, r, hbs, hw⟩ | hform
  · have hpos : l.pos + 6 ≤ y.length := by
      have := congrArg List.length hw
      rw [List.length_drop, List.length_cons, List.length_append, hbs] at this
      omega
    have hzero : y.drop l.pos = true :: y.drop (l.pos + 1) := by
      rw [← List.tail_drop, hw]
      rfl
    have hr : y.drop (l.pos + 6) = r := by
      rw [drop_add_six, hw, List.drop_succ_cons, List.drop_left' hbs]
    rw [labelOk, sem_onBitAt _ _ _ _ _ true _ (by rw [sem_L4, hw]), ite_eq_left rfl,
      sem_onBits _ 5 _ _ bs r hbs (by rw [sem_tailAppL, sem_L4, hw]; rfl)]
    cases hkd : readTag bs with
    | none =>
      rw [Option.elim_none, sem_constL]
      refine ⟨fun h ↦ absurd h (by decide), fun ⟨a, ha, _⟩ ↦ ?_⟩
      obtain ⟨hd, -, -, -⟩ := of_label_code y l hs a ha
      rw [hw] at hd
      have := List.append_inj_left (List.cons.inj hd).2 (by rw [hbs, length_tag])
      rw [this, readTag_tag] at hkd
      cases hkd
    | some kd =>
      rw [Option.elim_some, kindOk,
        isTrueWord_andF_iff _ _ _ _ (sem_oksExpr (envL y l k) y W4 L4 l.pos rfl rfl 8),
        decide_eq_true_eq]
      refine Decidable.byCases
        (p := ∀ i < 8, (numOkAt W4 (fieldPtr W4 L4 i)).sem (envL y l k) = [true])
        (dec := Nat.decidableBallLT 8 fun i _ ↦
          (numOkAt W4 (fieldPtr W4 L4 i)).sem (envL y l k) = [true])
        (fun hall ↦ ?_) fun hall ↦ ?_
      · obtain ⟨l', rest', hl', hy'⟩ :=
          fields_of_ok (envL y l k) y W4 L4 l.pos rfl rfl hpos 8 hall
        have hE := sem_fieldPtr (envL y l k) y W4 L4 l.pos l' rest' rfl rfl hpos hy' 8
          (Nat.le_of_eq hl'.symm)
        have hends := sem_endsAt (fieldPtr W4 L4 8) R4 (envL y l k) y _ (l.pos + l.len) hE
          (fpos_le y l.pos l' rest' hpos hy' 8) (sem_R4 y l k) hs.2
        have hatoms : (atomsExpr W4 L4 (atoms kd)).sem (envL y l k) =
            boolWord (check kd (ofList l')) :=
          sem_atomsExpr (envL y l k) y W4 L4 l.pos l' rest' rfl rfl hl' hy' hzero hpos (atoms kd)
            (atoms_bounded kd)
        obtain ⟨h61, h62, h63⟩ :=
          field_split (envL y l k) y W4 L4 l.pos l' rest' rfl rfl hl' hy' 6 (by decide)
        have hcard : (eqSeg K4 (natValueAt W4 (fieldPtr W4 L4 6))).sem (envL y l k) =
            boolWord (decide (k = min (ofList l' 6) y.length)) :=
          sem_eqSeg _ _ (envL y l k) y k _ rfl
            (by rw [natValueAt_natCode (envL y l k) y W4 _ _ _ _ _ rfl h61 h63 h62]
                exact (drop_min_length y _).symm)
            (by omega) (Nat.min_le_right _ _)
        rw [isTrueWord_andF_iff _ _ _ _ hends, isTrueWord_andF_iff _ _ _ _ hatoms, hcard,
          isTrueWord_boolWord]
        simp only [decide_eq_true_eq]
        have hfpos : fpos l.pos l' 8 = l.pos + 6 + (codes l').length := by
          rw [fpos, List.take_of_length_le (Nat.le_of_eq hl'), ← length_codes]
        have hmin : k = min (ofList l' 6) y.length ↔ k = ofList l' 6 := by
          constructor
          · intro h
            rcases Nat.le_total (ofList l' 6) y.length with h' | h'
            · rw [Nat.min_eq_left h'] at h
              exact h
            · rw [Nat.min_eq_right h'] at h
              omega
          · intro h
            rw [h, Nat.min_eq_left (by omega)]
        constructor
        · rintro ⟨-, hend, hchk, hkk⟩
          have hbuild : build kd (ofList l') = some (mk kd (ofList l')) := by
            rw [build, ite_eq_left hchk]
          obtain ⟨hkind, hfields⟩ := kind_fields_of_build hbuild
          refine ⟨mk kd (ofList l'), ?_, ?_⟩
          · change labelAt y l = code (mk kd (ofList l'))
            rw [code_eq, hkind, hfields, ofFn_ofList l' hl',
              labelAt_of_form y l bs r hw hbs (codes l').length (by omega),
              tag_of_readTag' bs hbs kd hkd, ← hr, hy', List.take_left]
          · refine (card_eq (mk kd (ofList l'))).trans ?_
            rw [hfields]
            exact (hmin.mp hkk).symm
        · rintro ⟨a, ha, hca⟩
          obtain ⟨hd, -, hdrop, hlen⟩ := of_label_code y l hs a ha
          have hl2 : l' = List.ofFn (fields a) ∧ rest' = y.drop (l.pos + l.len) := by
            have h1 := readFields_codes_append l' rest'
            have h2 := readFields_codes_append (List.ofFn (fields a)) (y.drop (l.pos + l.len))
            rw [hl'] at h1
            rw [List.length_ofFn] at h2
            rw [← hy', hdrop, h2, Option.some.injEq, Prod.mk.injEq] at h1
            exact ⟨h1.1.symm, h1.2.symm⟩
          obtain ⟨rfl, rfl⟩ := hl2
          have hkd' : kd = kind a := by
            rw [hw] at hd
            have := List.append_inj_left (List.cons.inj hd).2 (by rw [hbs, length_tag])
            rw [this, readTag_tag, Option.some.injEq] at hkd
            exact hkd.symm
          refine ⟨hall, by omega, ?_, ?_⟩
          · rw [hkd', ofList_ofFn]
            exact check_eq_true_of_build (build_kind_fields a)
          · rw [hmin, ofList_ofFn]
            exact hca.symm.trans (card_eq a)
      · refine ⟨fun h ↦ absurd h.1 hall, fun ⟨a, ha, _⟩ ↦ absurd ?_ hall⟩
        obtain ⟨-, -, hdrop, -⟩ := of_label_code y l hs a ha
        exact fun i hi ↦ ok_fieldPtr (envL y l k) y W4 L4 l.pos _ _ rfl rfl hpos hdrop i
          (by rw [List.length_ofFn]; exact hi)
  · rw [sem_labelOk_short y l k hform]
    refine ⟨fun h ↦ absurd h (by decide), fun ⟨a, ha, _⟩ ↦ ?_⟩
    obtain ⟨hd, -, -, -⟩ := of_label_code y l hs a ha
    exact (hform (tag (kind a)) _ (length_tag _) hd).elim

end Correct

/-- The label check computes the signature's label condition on every word. -/
theorem computesLabel (y : List Bool) : coded.ComputesLabel labelOk y :=
  fun l k hs hk ↦ labelOk_eq y l k hs hk

end

end Geb.BitStream.Oitavem.LabelExpr
