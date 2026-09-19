/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NodeExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ChildExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Recognize
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The recognizer of the W-trees of a coded signature as a successor-free expression

The recognizer {name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognize` as an
expression of the logspace subalgebra: the scan over the nodes whose check
at a node is the conjunction of a label check with the scan over the node's
children, each scan the expression of its module, and the label and edge
checks parameters of arity four and six. When the two parameters compute a
coded signature's label and edge conditions, the expression accepts exactly
the words the recognizer accepts, the spellings of the signature's admissible
W-trees. The scans, being simultaneous recursions with a fixed number of
registers each an end segment of the input or a bounded word, are what the
subalgebra's soundness theorem compiles to a logarithmic-space machine.

# Main definitions

* {lit}`checkExpr` — the check at a node: the label check conjoined with the
  scan over the children.
* {lit}`recognizeExpr` — the recognizer.
* {lit}`CodedSig.ComputesLabel`, {lit}`CodedSig.ComputesEdge` — an
  expression computes a signature's label condition, or its edge condition,
  at every location within a word.

# Main statements

* {lit}`nodeScan_congr` — scans whose checks agree within the word agree.
* {lit}`checkB_checkExpr` — the check the expression defines is the
  signature's, at locations within the word.
* {lit}`CodedSig.recognizeExprSem_eq`,
  {lit}`CodedSig.recognizeExprSem_eq_singleton_iff` — the expression's value
  is the recognizer's verdict as a word, and it accepts exactly the words the
  recognizer accepts.
* {lit}`CodedSig.recognizeExprSem_eq_singleton_iff_isW` — the expression
  accepts exactly the spellings of admissible W-trees.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, simultaneous recursion on notation, W-type, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree.Elias.Scanner (scan)

public section

/-- The check at a node: the label check, read as a flag, conjoined with the
scan over the node's children. -/
@[expose] def checkExpr (label : LOf 4) (edge : LOf 6) : LOf 4 :=
  andOkAt (flagOf label) (ChildExpr.childScanExpr edge)

/-- The recognizer: the scan over the nodes with the check. -/
@[expose] def recognizeExpr (label : LOf 4) (edge : LOf 6) : LOf 1 :=
  NodeExpr.nodeScanExpr (checkExpr label edge)

/-- Scans whose checks agree at every location within the word, at every
count within its length, agree. -/
theorem nodeScan_congr (c₁ c₂ : Loc → ℕ → Bool) (w : List Bool)
    (h : ∀ (l : Loc) (k : ℕ), l.pos ≤ w.length → k ≤ w.length → c₁ l k = c₂ l k) :
    nodeScan c₁ w = nodeScan c₂ w := by
  have key : ∀ (p : List Bool) (s : Ext NodeReg), s.pos + p.length ≤ w.length →
      s.extra.k ≤ s.pos →
      p.foldl (extStep (nodeUpd c₁)) s = p.foldl (extStep (nodeUpd c₂)) s ∧
        (p.foldl (extStep (nodeUpd c₁)) s).extra.k ≤ (p.foldl (extStep (nodeUpd c₁)) s).pos :=
    List.rec (fun s _ hk ↦ ⟨rfl, hk⟩) fun b p ih s hp hk ↦ by
      rw [List.length_cons] at hp
      have hstep : extStep (nodeUpd c₁) s b = extStep (nodeUpd c₂) s b := by
        unfold extStep nodeUpd
        cases hpl : (eventS s.state b).payload with
        | none => rfl
        | some L =>
          simp only
          rw [h ⟨s.pos + 1, L⟩ s.extra.k (by dsimp only; omega) (by omega)]
      have hk' : (extStep (nodeUpd c₁) s b).extra.k ≤ (extStep (nodeUpd c₁) s b).pos := by
        unfold extStep nodeUpd
        dsimp only
        split_ifs <;> omega
      rw [List.foldl_cons, List.foldl_cons, ← hstep]
      exact ih _ (by change s.pos + 1 + p.length ≤ w.length; omega) hk'
  exact (key w ⟨(.tree, 1), 0, ⟨0, true⟩⟩ (by simp) (Nat.le_refl 0)).1

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- An expression computes the signature's label condition on a word: at every
location within the word and every count within its length, its value at the
word, the remaining word from the location, the word dropped by one more than
the location's length, and the word dropped by the count, read as a flag, is
the condition on the word at the location with the count. -/
@[expose] def ComputesLabel (label : LOf 4) (y : List Bool) : Prop :=
  ∀ (l : Loc) (k : ℕ), l.pos ≤ y.length → k ≤ y.length →
    isTrueWord (label.sem ![y, y.drop l.pos, y.drop (l.len + 1), y.drop k]) =
      C.labelSpec (labelAt y l) k

/-- An expression computes the signature's edge condition on a word: at every
two locations within the word and every position within its length, its value
at the word, the two locations' remaining words and length counters, and the
word dropped by the position, read as a flag, is the condition on the words at
the locations with the position. -/
@[expose] def ComputesEdge (edge : LOf 6) (y : List Bool) : Prop :=
  ∀ (l l' : Loc) (j : ℕ), l.pos ≤ y.length → l'.pos ≤ y.length → j ≤ y.length →
    isTrueWord (edge.sem ![y, y.drop l.pos, y.drop (l.len + 1), y.drop l'.pos,
      y.drop (l'.len + 1), y.drop j]) = C.edgeSpec (labelAt y l) j (labelAt y l')

/-- The scan over the children with an expression computing the edge condition
is the scan with the condition. -/
theorem childScan_edgeB (edge : LOf 6) (y : List Bool) (he : C.ComputesEdge edge y) (l : Loc)
    (k : ℕ) (hl : l.pos ≤ y.length) :
    childScan l k (ChildExpr.edgeB edge y l) y =
      childScan l k (fun l' j ↦ C.edgeSpec (labelAt y l) j (labelAt y l')) y := by
  have key : ∀ (p : List Bool) (s : Ext ChildReg), s.pos + p.length ≤ y.length →
      s.extra.j ≤ s.pos →
      p.foldl (extStep (childUpd l k (ChildExpr.edgeB edge y l))) s =
        p.foldl (extStep (childUpd l k (fun l' j ↦ C.edgeSpec (labelAt y l) j (labelAt y l')))) s ∧
        (p.foldl (extStep (childUpd l k (ChildExpr.edgeB edge y l))) s).extra.j ≤
          (p.foldl (extStep (childUpd l k (ChildExpr.edgeB edge y l))) s).pos :=
    List.rec (fun s _ hj ↦ ⟨rfl, hj⟩) fun b p ih s hp hj ↦ by
      rw [List.length_cons] at hp
      have hstep : extStep (childUpd l k (ChildExpr.edgeB edge y l)) s b =
          extStep (childUpd l k (fun l' j ↦ C.edgeSpec (labelAt y l) j (labelAt y l'))) s b := by
        unfold extStep childUpd
        rcases s with ⟨σ, pos, ⟨m, fc, lc, j, ok⟩⟩
        simp only at hj hp ⊢
        cases m <;> (try rfl)
        cases hpl : (eventS σ b).payload with
        | none => rfl
        | some L =>
          simp only
          rw [ChildExpr.edgeB, he l ⟨pos + 1, L⟩ j hl (by dsimp only; omega) (by omega)]
      have hj' : (extStep (childUpd l k (ChildExpr.edgeB edge y l)) s b).extra.j ≤
          (extStep (childUpd l k (ChildExpr.edgeB edge y l)) s b).pos := by
        unfold extStep childUpd afterChildren
        rcases s with ⟨σ, pos, ⟨m, fc, lc, j, ok⟩⟩
        simp only at hj ⊢
        cases m <;> dsimp only <;> (try cases (eventS σ b).payload) <;> (try split_ifs) <;>
          (try dsimp only) <;> omega
      rw [List.foldl_cons, List.foldl_cons, ← hstep]
      exact ih _ (by change s.pos + 1 + p.length ≤ y.length; omega) hj'
  exact (key y ⟨(.tree, 1), 0, ⟨.before, 0, 0, 0, true⟩⟩ (by simp) (Nat.le_refl 0)).1

/-- The check the expression defines is the signature's node check, at
locations within the word and counts within its length. -/
theorem checkB_checkExpr (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) (l : Loc) (k : ℕ)
    (hlp : l.pos ≤ y.length) (hk : k ≤ y.length) :
    NodeExpr.checkB (checkExpr label edge) y l k = C.nodeCheck y l k := by
  unfold NodeExpr.checkB checkExpr nodeCheck
  rw [andOkAt, sem_cond4L, sem_flagOf, sem_constL, ChildExpr.childScanExprSem_eq edge y l k hlp hk,
    cond4Sem_boolWord, isTrueWord_boolWord, hl l k hlp hk, C.childScan_edgeB edge y he l k hlp]

/-- The expression's value, when its parameters compute the signature's
conditions on the word: {lit}`[true]` when the recognizer accepts, the empty
word otherwise. -/
theorem recognizeExprSem_eq (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = if C.recognize y then [true] else [] := by
  rw [recognizeExpr, NodeExpr.nodeScanExprSem_eq, recognize,
    Geb.BitTree.Elias.Scanner.validBool,
    nodeScan_congr _ _ y fun l k hlp hk ↦ C.checkB_checkExpr label edge y hl he l k hlp hk]
  by_cases hd : (scan y).1 = .done
  · by_cases ho : (nodeScan (C.nodeCheck y) y).extra.ok = true
    · rw [ite_eq_left ⟨hd, ho⟩, decide_eq_true hd, ho]
      rfl
    · rw [ite_eq_right (fun h ↦ ho h.2), decide_eq_true hd, Bool.eq_false_iff.mpr ho]
      rfl
  · rw [ite_eq_right (fun h ↦ hd h.1), decide_eq_false hd]
    rfl

/-- The expression accepts exactly the words the recognizer accepts, when its
parameters compute the signature's conditions on the word. -/
theorem recognizeExprSem_eq_singleton_iff (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = [true] ↔ C.recognize y = true := by
  rw [C.recognizeExprSem_eq label edge y hl he]
  cases C.recognize y <;> simp

/-- The expression accepts exactly the spellings of admissible W-trees, when
its parameters compute the signature's conditions on the word. -/
theorem recognizeExprSem_eq_singleton_iff_isW (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = [true] ↔ ∃ t, C.P.WValid t ∧ C.spell t = y :=
  (C.recognizeExprSem_eq_singleton_iff label edge y hl he).trans (C.recognize_iff y)

end CodedSig

end

end Geb.SizeBounded.Logspace.WTree
