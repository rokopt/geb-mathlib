/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Label
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The edge check of the bundle signature as an expression

The edge condition of the bundle signature, {name}`Geb.BitStream.Oitavem.coded`,
as an expression of arity six: at the word, a parent label's remaining word
and length counter, a child label's, and the word dropped by the child's
position, it decides whether the child's shape produces the arity the
parent's shape requires at that position, given that both labels decode. A
root child is rejected by its tag's first bit. Otherwise the position is
compared with the parent's seventh numeral, its number of children, and the
child's first two numerals, the arity it produces, are compared with the
parent's third and fourth at the first position and with its fifth and sixth
after, so that no dispatch on either shape's constructor is needed.

# Main definitions

* {lit}`pfield`, {lit}`cfield` — the pointers to the parent's and the
  child's numerals.
* {lit}`headCase`, {lit}`tailCase`, {lit}`someChild`, {lit}`edgeOk` — the
  comparisons at the first position and after, the check of a wrapped
  child, and the edge check.

# Main statements

* {lit}`computesEdge` — the edge check computes the signature's edge
  condition on every word.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, coded signature, edge, recognizer
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem.EdgeExpr

open Geb.SizeBounded.Logspace (LOf tailAppL sem_tailAppL constL sem_constL cond4L sem_cond4L)
open Geb.SizeBounded.Logspace.WTree (CodedSig boolWord isTrueWord isTrueWord_boolWord isZeroSeg
  sem_isZeroSeg cond4Sem_drop_length_sub onBitAt sem_onBitAt Loc labelAt)
open Geb.SizeBounded.Logspace.WTree.SigLabel (andF sem_andF leSeg sem_leSeg natEqAt natEqAt_natCode
  natValueAt natValueAt_natCode isTrueWord_andF_iff lend_le)
open Geb.SizeBounded.Logspace.WTree.SigEdge (W6 L6 C6 J6 envE sem_W6 sem_L6 sem_C6 sem_J6
  sem_J6_tail)
open Geb.Oitavem (Shape Initial)
open Geb.BitStream.Oitavem
open Geb.BitStream.Oitavem.FieldExpr
open Geb.BitStream.Oitavem.LabelExpr (of_label_code)

public section

/-- The pointer to a numeral of the parent's label. -/
abbrev pfield (i : ℕ) : LOf 6 := fieldPtr W6 L6 i

/-- The pointer to a numeral of the child's label. -/
abbrev cfield (i : ℕ) : LOf 6 := fieldPtr W6 C6 i

/-- At the first position: the child produces the arity the parent requires
of its first child. -/
@[expose] def headCase : LOf 6 :=
  andF (natEqAt W6 (cfield 0) (pfield 2)) (natEqAt W6 (cfield 1) (pfield 3))

/-- After the first position: the child produces the arity the parent
requires of its other children. -/
@[expose] def tailCase : LOf 6 :=
  andF (natEqAt W6 (cfield 0) (pfield 4)) (natEqAt W6 (cfield 1) (pfield 5))

/-- The check of a wrapped child: the position is below the parent's number
of children, and the case of the position. -/
@[expose] def someChild : LOf 6 :=
  andF (leSeg (tailAppL J6) (natValueAt W6 (pfield 6)))
    (cond4L (isZeroSeg J6 W6) headCase tailCase tailCase)

/-- The edge check: the dispatch on the child's first tag bit, which rejects
a root child. -/
@[expose] def edgeOk : LOf 6 :=
  onBitAt (tailAppL C6) (constL 6 []) (constL 6 []) someChild

/-- The tag of a shape of Logs begins with a clear bit. -/
theorem tag_kind_some (c : Shape) : ∃ bs, tag (kind (some c)) = false :: bs := by
  cases c with
  | initial p => cases p <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- The edge check computes the signature's edge condition on every word. -/
theorem computesEdge (y : List Bool) : coded.ComputesEdge edgeOk y := by
  intro l l' j hs hs' hj hd hd'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hd'
  have hla : labelAt y l = code a := (code_of_decode ha).symm
  have hlc : labelAt y l' = code c := (code_of_decode hc).symm
  obtain ⟨hdp, h6p, hdropp, -⟩ := of_label_code y l hs a hla
  obtain ⟨hdc, h6c, hdropc, -⟩ := of_label_code y l' hs' c hlc
  have hposp : l.pos + 6 ≤ y.length := by
    have := lend_le y l hs
    omega
  have hposc : l'.pos + 6 ≤ y.length := by
    have := lend_le y l' hs'
    omega
  change isTrueWord (edgeOk.sem (envE y l l' j)) = coded.edgeSpec (labelAt y l) j (labelAt y l')
  unfold CodedSig.edgeSpec
  rw [ha, hc]
  dsimp only
  change isTrueWord (edgeOk.sem (envE y l l' j)) = if h : j < coded.card a then
    decide (sig.q c = sig.rCurried a (coded.dir a ⟨j, h⟩)) else false
  have hC1 : (tailAppL C6).sem (envE y l l' j) =
      tag (kind c) ++ (codes (List.ofFn (fields c)) ++ y.drop (l'.pos + l'.len)) := by
    rw [sem_tailAppL, sem_C6, hdc]
    rfl
  cases c with
  | none =>
    rw [edgeOk, sem_onBitAt _ _ _ _ _ true _ (by rw [hC1]; rfl), ite_eq_left rfl, sem_constL]
    change false = _
    by_cases hjc : j < coded.card a
    · rw [dite_eq_left hjc, rCurried_dir_eq a j hjc]
      symm
      exact decide_eq_false fun h ↦ by cases h
    · rw [dite_eq_right hjc]
  | some c' =>
    obtain ⟨bs, hbs⟩ := tag_kind_some c'
    rw [hbs, List.cons_append] at hC1
    rw [edgeOk, sem_onBitAt _ _ _ _ _ false _ hC1, ite_eq_right (by decide), someChild]
    have hlp : (List.ofFn (fields a)).length = 8 := List.length_ofFn
    have hlc' : (List.ofFn (fields (some c'))).length = 8 := List.length_ofFn
    obtain ⟨p2a, p2b, p2c⟩ :=
      field_split (envE y l l' j) y W6 L6 l.pos _ _ rfl rfl hlp hdropp 2 (by decide)
    obtain ⟨p3a, p3b, p3c⟩ :=
      field_split (envE y l l' j) y W6 L6 l.pos _ _ rfl rfl hlp hdropp 3 (by decide)
    obtain ⟨p4a, p4b, p4c⟩ :=
      field_split (envE y l l' j) y W6 L6 l.pos _ _ rfl rfl hlp hdropp 4 (by decide)
    obtain ⟨p5a, p5b, p5c⟩ :=
      field_split (envE y l l' j) y W6 L6 l.pos _ _ rfl rfl hlp hdropp 5 (by decide)
    obtain ⟨p6a, p6b, p6c⟩ :=
      field_split (envE y l l' j) y W6 L6 l.pos _ _ rfl rfl hlp hdropp 6 (by decide)
    obtain ⟨c0a, c0b, c0c⟩ :=
      field_split (envE y l l' j) y W6 C6 l'.pos _ _ rfl rfl hlc' hdropc 0 (by decide)
    obtain ⟨c1a, c1b, c1c⟩ :=
      field_split (envE y l l' j) y W6 C6 l'.pos _ _ rfl rfl hlc' hdropc 1 (by decide)
    have ep : ∀ (i : ℕ) (hi : i < 8), ofList (List.ofFn (fields a)) ⟨i, hi⟩ = fields a ⟨i, hi⟩ :=
      fun i hi ↦ congrFun (ofList_ofFn _) _
    have ec : ∀ (i : ℕ) (hi : i < 8),
        ofList (List.ofFn (fields (some c'))) ⟨i, hi⟩ = fields (some c') ⟨i, hi⟩ :=
      fun i hi ↦ congrFun (ofList_ofFn _) _
    have hle : (leSeg (tailAppL J6) (natValueAt W6 (pfield 6))).sem (envE y l l' j) =
        boolWord (decide (min (j + 1) y.length ≤ fields a 6)) := by
      rw [sem_leSeg _ _ _ y (j + 1) (fields a 6) (sem_J6_tail y l l' j)
        (by rw [natValueAt_natCode (envE y l l' j) y W6 _ _ _ _ _ rfl p6a p6c p6b, ep 6]; rfl)]
    have hhead : headCase.sem (envE y l l' j) = boolWord
        (decide (fields (some c') 0 = fields a 2) && decide (fields (some c') 1 = fields a 3)) := by
      rw [headCase, sem_andF _ _ _ _ _
        (natEqAt_natCode (envE y l l' j) y W6 _ _ _ _ _ _ _ _ _ _ rfl c0a p2a c0c c0b p2c p2b)
        (natEqAt_natCode (envE y l l' j) y W6 _ _ _ _ _ _ _ _ _ _ rfl c1a p3a c1c c1b p3c p3b),
        ec 0, ec 1, ep 2, ep 3]
      rfl
    have htail : tailCase.sem (envE y l l' j) = boolWord
        (decide (fields (some c') 0 = fields a 4) && decide (fields (some c') 1 = fields a 5)) := by
      rw [tailCase, sem_andF _ _ _ _ _
        (natEqAt_natCode (envE y l l' j) y W6 _ _ _ _ _ _ _ _ _ _ rfl c0a p4a c0c c0b p4c p4b)
        (natEqAt_natCode (envE y l l' j) y W6 _ _ _ _ _ _ _ _ _ _ rfl c1a p5a c1c c1b p5c p5b),
        ec 0, ec 1, ep 4, ep 5]
      rfl
    have hcond : (cond4L (isZeroSeg J6 W6) headCase tailCase tailCase).sem (envE y l l' j) =
        if j = 0 then headCase.sem (envE y l l' j) else tailCase.sem (envE y l l' j) := by
      rw [sem_cond4L, sem_isZeroSeg J6 W6 _ y j (sem_J6 y l l' j) (sem_W6 y l l' j),
        cond4Sem_drop_length_sub y j (by omega)]
    have hq : sig.q (some c') = some (fields (some c') 0, fields (some c') 1) := q_eq (some c')
    rw [Bool.eq_iff_iff, isTrueWord_andF_iff _ _ _ _ hle, hcond, decide_eq_true_eq, hq]
    by_cases hjc : j < coded.card a
    · rw [dite_eq_left hjc, rCurried_dir_eq a j hjc, decide_eq_true_eq, Option.some.injEq]
      have hj' : min (j + 1) y.length ≤ fields a 6 := by
        rw [card_eq] at hjc
        omega
      by_cases hj0 : j = 0
      · rw [ite_eq_left hj0, ite_eq_left hj0, hhead, isTrueWord_boolWord, Bool.and_eq_true,
          decide_eq_true_eq, decide_eq_true_eq, Prod.mk.injEq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hj', h⟩⟩
      · rw [ite_eq_right hj0, ite_eq_right hj0, htail, isTrueWord_boolWord, Bool.and_eq_true,
          decide_eq_true_eq, decide_eq_true_eq, Prod.mk.injEq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hj', h⟩⟩
    · rw [dite_eq_right hjc]
      refine ⟨fun h ↦ absurd h.1 ?_, fun h ↦ absurd h (by decide)⟩
      rw [card_eq] at hjc
      omega

end

end Geb.BitStream.Oitavem.EdgeExpr
