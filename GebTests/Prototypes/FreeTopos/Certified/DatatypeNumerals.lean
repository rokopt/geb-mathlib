/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.DatatypeSoundness
public import GebTests.Prototypes.FreeTopos.Agreement.Reader

set_option doc.verso true in
/-!
# The digits of a label, as the datatype language's compilers compute them

The soundness of a whole program of the datatype language's stage-1 compiler assumes two facts
about the compilers that depend on no program: that the reader reads the digits the typing
writes for a label as the label, and that the expansion of numeral abbreviations fixes each of
those digits. Both hold of the compilers' mirror, whose definitions are the values the kernel
loads ({lit}`DatatypeMirror.hypFns_loaded`). The typing's digits of a tree read the tree's label
alone, and at a leaf they are the label's shortest decimal spelling, as the metalogic's printer
writes it ({name}`GebTests.Prototypes.FreeTopos.Agreement.Printer.decimalChars_eq`): the two
programs define the digits by the same expression. The reader reads a spelling's characters as
the number spelled ({name}`GebTests.Prototypes.FreeTopos.Agreement.Reader.numeral_eq`,
{name}`Geb.Kernel.numeral?_decOf`), and the expansion of numeral abbreviations rewrites atoms
alone, which a digit's leaf is not.

## Main statements

* {lit}`decimalChars_label` — the digits of a tree are those of the leaf of its label.
* {lit}`numeral_decimalChars` — the reader reads the digits of a tree's label as the label.
* {lit}`charsFixed_decimalChars` — the expansion of numeral abbreviations fixes the digits of a
  tree's label.

## Tags

internal language, datatypes, kernel, mirror, numerals, test
-/

set_option doc.verso true

@[expose] public section

open GebMirror.DatatypeSoundness

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeNumerals

open Geb Geb.Kernel
open GebTests.Prototypes.FreeTopos.Agreement.Printer (countStep msbStep repeat_succ' charsT
  decimalChars_eq)
open GebTests.Prototypes.FreeTopos.Agreement.Reader (numeral_eq)
open scoped FinEnum

/-- Iterations from two states that one step makes equal agree after any further steps. -/
theorem repeat_succ_congr {α : Type} (s : α → α) {a b : α} (h : s a = s b) (k : ℕ) :
    Nat.repeat s (k + 1) a = Nat.repeat s (k + 1) b := by
  rw [repeat_succ', repeat_succ', h]

/-- The typing's digits of a tree are those of the leaf of its label: the comparison, the
logarithm and the divisions they are computed by read the label alone. -/
theorem decimalChars_label (t : Tree) :
    «Typing.decimalChars» t = «Typing.decimalChars» (leaf t.label) := by
  by_cases hc : (Const.eq t (leaf 0)).label ≠ 0
  · have hc' : (Const.eq (leaf t.label) (leaf 0)).label ≠ 0 := hc
    exact (ite_eq_left hc).trans (ite_eq_left hc').symm
  · have hc' : ¬(Const.eq (leaf t.label) (leaf 0)).label ≠ 0 := hc
    have hs : countStep (leaf 0, t) = countStep (leaf 0, leaf t.label) :=
      (ite_eq_right hc).trans (ite_eq_right hc').symm
    have hn := congrArg Prod.fst (repeat_succ_congr countStep hs t.label.log2)
    have hm : ∀ k : ℕ,
        (Nat.repeat msbStep k (t, [])).2 = (Nat.repeat msbStep k (leaf t.label, [])).2 :=
      Nat.rec rfl fun k _ ↦ congrArg Prod.snd
        (repeat_succ_congr msbStep (a := (t, [])) (b := (leaf t.label, [])) rfl k)
    have e₁ : «Typing.decimalChars» t =
        Const.foldr (fun x2 x3 ↦ Const.add x2 (leaf 48) :: x3) []
          (Nat.repeat msbStep (Nat.repeat countStep (t.label.log2 + 1) (leaf 0, t)).1.label
            (t, [])).2 :=
      ite_eq_right hc
    have e₂ : «Typing.decimalChars» (leaf t.label) =
        Const.foldr (fun x2 x3 ↦ Const.add x2 (leaf 48) :: x3) []
          (Nat.repeat msbStep
            (Nat.repeat countStep (t.label.log2 + 1) (leaf 0, leaf t.label)).1.label
            (leaf t.label, [])).2 :=
      ite_eq_right hc'
    rw [e₁, e₂, hn, hm]

/-- The typing's digits of a leaf are the shortest decimal spelling of its label, each
character the leaf of its code point: the typing defines them as the metalogic's printer
does. -/
theorem decimalChars_leaf (n : ℕ) : «Typing.decimalChars» (leaf n) = charsT (Csexp.decOf n) :=
  decimalChars_eq n

/-- The reader reads the typing's digits of a tree's label as the label. -/
theorem numeral_decimalChars (t : Tree) :
    «Reader.numeral» («Typing.decimalChars» t) = «Prelude.some» (leaf t.label) := by
  rw [decimalChars_label, decimalChars_leaf]
  refine (numeral_eq (Csexp.decOf t.label)).trans ?_
  rw [numeral?_decOf]
  rfl

/-- The expansion of numeral abbreviations fixes a leaf whose label is not an atom's. -/
theorem expandNums_leaf (nums : List Tree) {k : ℕ} (hk : k ≠ 1) :
    «Reader.expandNums» nums (leaf k) = leaf k := by
  have ha : ¬(«Reader.isAtom» (leaf k)).label ≠ 0 := by
    change ¬(ofBool (k == 1)).label ≠ 0
    rw [beq_false_of_ne hk]
    exact fun h ↦ h rfl
  change (if («Reader.isAtom» (leaf k)).label ≠ 0 then _ else leaf k) = leaf k
  rw [ite_eq_right ha]

/-- A character of a label's decimal spelling is not the character of code point one. -/
theorem toNat_ne_one_of_mem_decOf {n : ℕ} {c : Char} (hc : c ∈ Csexp.decOf n) : c.toNat ≠ 1 := by
  have h := Csexp.decOf_all_digits n c hc
  unfold Csexp.charDigit at h
  split at h
  · next hd =>
    have h48 : 48 ≤ c.toNat := of_decide_eq_true (Bool.and_eq_true_iff.mp hd).1
    intro e
    omega
  · exact nomatch h

/-- The expansion of numeral abbreviations fixes each character of a spelling none of whose
characters has the code point one. -/
theorem foldr_expandNums (nums : List Tree) : ∀ cs : List Char, (∀ c ∈ cs, c.toNat ≠ 1) →
    (charsT cs).foldr (fun c a ↦ «Reader.expandNums» nums c :: a) [] = charsT cs :=
  List.rec (fun _ ↦ rfl) fun c cs ih h ↦ by
    change «Reader.expandNums» nums (leaf c.toNat) ::
      (charsT cs).foldr (fun c a ↦ «Reader.expandNums» nums c :: a) [] = leaf c.toNat :: charsT cs
    rw [expandNums_leaf nums (h c List.mem_cons_self),
      ih fun x hx ↦ h x (List.mem_cons_of_mem c hx)]

/-- The expansion of numeral abbreviations fixes the typing's digits of a tree's label, at any
abbreviations. -/
theorem charsFixed_decimalChars (nums : List Tree) (t : Tree) :
    («charsFixed» (fun y ↦ «Reader.expandNums» nums y) («Typing.decimalChars» t)).label ≠ 0 := by
  rw [decimalChars_label, decimalChars_leaf]
  change (Const.equal (Const.node (leaf 0)
    ((charsT (Csexp.decOf t.label)).foldr (fun c a ↦ «Reader.expandNums» nums c :: a) []))
    (Const.node (leaf 0) (charsT (Csexp.decOf t.label)))).label ≠ 0
  rw [foldr_expandNums nums _ fun c hc ↦ toNat_ne_one_of_mem_decOf hc]
  change (ofBool (decide (_ = _))).label ≠ 0
  rw [decide_eq_true rfl]
  exact fun h ↦ nomatch h

end GebTests.Prototypes.FreeTopos.Certified.DatatypeNumerals

end
