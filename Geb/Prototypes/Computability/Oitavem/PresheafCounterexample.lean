/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
public import Geb.Mathlib.Data.PFunctor.Presheaf.Arrow
public import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable

set_option doc.verso true in
/-!
# Finiteness does not bound the cost of presheaf restriction

Hereditary naturality can depend on an arbitrary Boolean predicate even over
the walking arrow and with at most three directions at a shape. The predicate
occurs only in direction restriction; the underlying slice signature is fixed.
Each test input is the spelling of an admissible slice tree with one root
and three leaves, and spelling is independent of the predicate.

Diagonalizing against the implemented unary Oitavem expressions gives a total
Lean predicate for which no such expression agrees with the native presheaf
checker, even on these admissible inputs. This refutes recognition from
finiteness alone, without using a machine characterization of the algebra.
It does not refute recognition under additional complexity bounds on the
signature operations.

## Main definitions

* {lit}`syntaxCode` and {lit}`readExpr` encode and decode unary Oitavem expressions.
* {lit}`diagonal` disagrees with each expression on its own encoded test input.
* {lit}`presheaf` puts a Boolean predicate into direction restriction on the walking arrow.
* {lit}`testTree` and {lit}`testWord` give admissible trees and their bitstrings.
* {lit}`nativeCheck` instantiates the repository's hereditary-naturality checker.

## Main statements

* {lit}`card_directions_le` bounds every direction type by three elements.
* {lit}`spell_testTree` proves that test bitstrings do not depend on the predicate.
* {lit}`testTree_natural_iff` and {lit}`nativeCheck_testTree` recover any predicate by checking
  its test trees.
* {lit}`no_oitavem_recognizer` and {lit}`no_oitavem_nativeCheck` refute an Oitavem recognizer
  for the diagonal instance.

## Tags

presheaf, W-type, hereditary naturality, logspace, diagonalization
-/

set_option doc.verso true

namespace Geb.Oitavem.PresheafCounterexample

open CategoryTheory
open Geb.SizeBounded.Logspace.WTree (CodedSig)
open scoped FinEnum

public section

/-- Numerical fields of an initial symbol. -/
@[expose] def initialFields : Initial → List ℕ
  | .zero n => [0, n]
  | .proj n i => [1, n, i]
  | .succ b => [2, b.toNat]
  | .pred => [3]
  | .iterPred => [4]
  | .numericSucc => [5]
  | .numericPred => [6]
  | .numericSub => [7]
  | .length => [8]
  | .last => [9]
  | .cond => [10]
  | .product => [11]

/-- Decode the numerical fields of an initial symbol. -/
@[expose] def readInitial : List ℕ → Option Initial
  | [0, n] => some (.zero n)
  | [1, n, i] => if h : i < n then some (.proj n ⟨i, h⟩) else none
  | [2, 0] => some (.succ false)
  | [2, 1] => some (.succ true)
  | [3] => some .pred
  | [4] => some .iterPred
  | [5] => some .numericSucc
  | [6] => some .numericPred
  | [7] => some .numericSub
  | [8] => some .length
  | [9] => some .last
  | [10] => some .cond
  | [11] => some .product
  | _ => none

/-- Reading the fields recovers an initial symbol. -/
theorem readInitial_initialFields (p : Initial) : readInitial (initialFields p) = some p := by
  cases p with
  | proj n i => simp [initialFields, readInitial, i.isLt]
  | succ b => cases b <;> rfl
  | _ => rfl

/-- Numerical fields of a constructor label. -/
@[expose] def shapeFields : Shape → List ℕ
  | .initial p => 0 :: initialFields p
  | .comp n m b => [1, n, m, b.toNat]
  | .safeRec n => [2, n]
  | .concatRec n => [3, n]
  | .logTransition n => [4, n]

/-- Decode the numerical fields of a constructor label. -/
@[expose] def readShape : List ℕ → Option Shape
  | 0 :: ns => (readInitial ns).map .initial
  | [1, n, m, 0] => some (.comp n m false)
  | [1, n, m, 1] => some (.comp n m true)
  | [2, n] => some (.safeRec n)
  | [3, n] => some (.concatRec n)
  | [4, n] => some (.logTransition n)
  | _ => none

/-- Reading the fields recovers a constructor label. -/
theorem readShape_shapeFields (a : Shape) : readShape (shapeFields a) = some a := by
  cases a with
  | initial p => simp [shapeFields, readShape, readInitial_initialFields]
  | comp n m b => cases b <;> rfl
  | _ => rfl

/-- Store numerical fields as leaf lengths, terminated by an empty leaf.
This unary encoding is used only to enumerate syntax for diagonalization. -/
@[expose] def fieldsTree : List ℕ → Geb.BitTree.Tree :=
  List.foldr (fun n t ↦ Geb.BitTree.fork (Geb.BitTree.leaf (List.replicate n false)) t)
    (Geb.BitTree.leaf [])

/-- Reading the leaf lengths recovers the fields and the terminator. -/
theorem lengths_fieldsTree : ∀ ns, Geb.BitTree.Elias.lengths (fieldsTree ns) = ns ++ [0] :=
  List.rec rfl fun n ns ih ↦ by
    simpa [fieldsTree, Geb.BitTree.Elias.lengths_fork,
      Geb.BitTree.Elias.lengths_leaf] using congrArg (n :: ·) ih

/-- Encode a constructor label using its numerical fields. -/
@[expose] def syntaxShapeCode (a : Shape) : List Bool :=
  Geb.BitTree.Elias.encode (fieldsTree (shapeFields a))

/-- Read a constructor label from its field lengths. -/
@[expose] def readSyntaxShape (w : List Bool) : Option Shape := do
  let t ← Geb.BitTree.Elias.decode w
  readShape (Geb.BitTree.Elias.lengths t).dropLast

/-- The shape decoder inverts the code. -/
theorem readSyntaxShape_code (a : Shape) : readSyntaxShape (syntaxShapeCode a) = some a := by
  simp [readSyntaxShape, syntaxShapeCode, lengths_fieldsTree, readShape_shapeFields]

/-- The Oitavem signature with an invertible bitstring code for its shapes. -/
@[expose] def syntaxCode : CodedSig (ℕ × ℕ) where
  P := sig
  finitary := sigFinitary
  code := syntaxShapeCode
  decode w := (readSyntaxShape w).filter fun a ↦ syntaxShapeCode a == w
  decode_code a := by
    change Shape at a
    exact Option.filter_eq_some_iff.mpr ⟨readSyntaxShape_code a, beq_iff_eq.mpr rfl⟩
  code_of_decode {w a} h := by
    exact beq_iff_eq.mp (Option.filter_eq_some_iff.mp h).2

/-- Decode a bitstring as an Oitavem expression with one normal input and no safe input. -/
@[expose] def readExpr (w : List Bool) : Option (Expr 1 0) := do
  let t ← Geb.BitTree.Elias.decode w
  let raw ← syntaxCode.readW t
  if hv : wellFormed raw = true then
    let e : sig.W := ⟨raw, (wellFormed_eq_true raw).mp hv⟩
    if hi : sig.wIndex e = (1, 0) then some ⟨e, hi⟩ else none
  else none

/-- The expression decoder inverts the spelling of every unary expression. -/
theorem readExpr_spell (e : Expr 1 0) :
    readExpr (syntaxCode.spell e.1.1) = some e := by
  simp only [readExpr, CodedSig.spell, Geb.BitTree.Elias.decode_encode, bind, Option.bind,
    syntaxCode.readW_toTree e.1.1, dite_eq_left ((wellFormed_eq_true _).mpr e.1.2)]
  split
  · rfl
  · exact (‹¬ _› e.2).elim

/-- Negate the verdict of the decoded expression on its encoded test input. -/
@[expose] def diagonal (test : List Bool → List Bool) (w : List Bool) : Bool :=
  match readExpr w with
  | none => false
  | some e => !decide (e.eval ![test w] Fin.elim0 = [true])

/-- No unary Oitavem expression recognizes its own diagonal predicate on the test inputs. -/
theorem not_recognizes_diagonal (test : List Bool → List Bool) (e : Expr 1 0) :
    ¬ (∀ w, e.eval ![test w] Fin.elim0 = [true] ↔ diagonal test w = true) := by
  intro h
  have h := h (syntaxCode.spell e.1.1)
  rw [diagonal, readExpr_spell] at h
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
  have hn := fun hp ↦ h.mp hp hp
  exact hn (h.mpr hn)

/-- Two nullary shapes and one binary shape. -/
@[expose, implicit_reducible] def base : PFunctor where
  A := Option Bool
  B a := Fin (a.elim 2 fun _ ↦ 0)

/-- A dependent root has one dependent direction, sent to the base direction selected
by the predicate. Dependent leaves have no directions. -/
@[expose, implicit_reducible] def family (p : List Bool → Bool) (a : base.A) :
    SliceDomPFunctor (base.B a) where
  A := List Bool
  B _ := Fin (a.elim 1 fun _ ↦ 0)
  r x := match a with
    | none => if p x.1 then (1 : Fin 2) else (0 : Fin 2)
    | some _ => x.2.elim0

/-- A presheaf polynomial on the walking arrow, with the predicate only in direction restriction. -/
@[expose, implicit_reducible] def presheaf (p : List Bool → Bool) :
    PresheafPFunctor (Fin 2) (Fin 2) :=
  base.dependent (family p)

/-- Every direction type is explicitly finite. -/
instance presheafFinitary (p : List Bool → Bool) : (presheaf p).toPFunctor.Finitary
  | .inl none => inferInstanceAs (FinEnum (Fin 2))
  | .inl (some _) => inferInstanceAs (FinEnum (Fin 0))
  | .inr ⟨none, _⟩ => inferInstanceAs (FinEnum (Fin 1 ⊕ Fin 2))
  | .inr ⟨some _, _⟩ => inferInstanceAs (FinEnum (Fin 0 ⊕ Fin 0))

/-- There are at most three directions at any shape. -/
theorem card_directions_le (p : List Bool → Bool) (a : (presheaf p).A) :
    @FinEnum.card _ (presheafFinitary p a) ≤ 3 := by
  match a with
  | .inl none => exact Nat.le_succ 2
  | .inl (some _) => exact Nat.zero_le 3
  | .inr ⟨none, _⟩ => exact Nat.le_refl 3
  | .inr ⟨some _, _⟩ => exact Nat.zero_le 3

/-- A base leaf, indexed at zero. -/
@[expose] def baseLeaf (p : List Bool → Bool) (b : Bool) : (presheaf p).toSlicePFunctor.W :=
  ⟨PFunctor.Dependent.ofBase base (family p) (WType.mk (some b) Fin.elim0),
    PFunctor.Dependent.wValid_ofBase base (family p) _⟩

/-- A dependent leaf, indexed at one, whose restriction is the true base leaf. -/
@[expose] def dependentLeaf (p : List Bool → Bool) : (presheaf p).toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.inr ⟨some true, []⟩, Sum.elim Fin.elim0 Fin.elim0⟩,
      funext fun b ↦ match b with | .inl d | .inr d => d.elim0⟩

/-- An admissible tree with the predicate's input at its root and three fixed leaves. -/
@[expose] def testTree (p : List Bool → Bool) (w : List Bool) :
    (presheaf p).toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.inr ⟨none, w⟩, Sum.elim (fun _ ↦ dependentLeaf p)
      (fun i : Fin 2 ↦ baseLeaf p (decide (i = 1)))⟩,
      funext fun b ↦ match b with | .inl _ | .inr _ => rfl⟩

/-- Every base leaf is hereditarily natural. -/
theorem baseLeaf_natural (p : List Bool → Bool) (b : Bool) :
    (presheaf p).IsHereditarilyNatural (baseLeaf p b) :=
  PFunctor.Dependent.isHereditarilyNatural_ofBase base (family p) _

/-- Every dependent leaf is hereditarily natural. -/
theorem dependentLeaf_natural (p : List Bool → Bool) :
    (presheaf p).IsHereditarilyNatural (dependentLeaf p) := by
  apply ((presheaf p).isHereditarilyNatural_mk_iff_arrow
    (SlicePFunctor.W.dest (dependentLeaf p))).mpr
  constructor
  · intro b
    rcases b with ⟨d, _⟩
    cases d with | inl d | inr d => exact d.elim0
  · intro b
    cases b with | inl b | inr b => exact b.elim0

/-- Restricting the dependent leaf gives the true base leaf. -/
theorem restrict_dependentLeaf (p : List Bool → Bool) :
    (presheaf p).wRestrTree PresheafPFunctor.arrow (dependentLeaf p) rfl =
      baseLeaf p true := by
  apply Subtype.ext
  refine ((presheaf p).wRestrTree_val PresheafPFunctor.arrow (dependentLeaf p) rfl).trans ?_
  apply congrArg (WType.mk (β := (presheaf p).toPFunctor.B) (.inl (some true)))
  funext b
  exact (show Fin 0 from b).elim0

/-- Naturality of an admissible test tree is exactly the chosen Boolean predicate. -/
theorem testTree_natural_iff (p : List Bool → Bool) (w : List Bool) :
    (presheaf p).IsHereditarilyNatural (testTree p w) ↔ p w = true := by
  change (presheaf p).IsHereditarilyNatural
    (SlicePFunctor.W.mk (SlicePFunctor.W.dest (testTree p w))) ↔ _
  rw [(presheaf p).isHereditarilyNatural_mk_iff_arrow]
  constructor
  · intro h
    have h := h.1 ⟨Sum.inl (0 : Fin 1), rfl⟩
    have hh := congrArg (fun z : (presheaf p).toSlicePFunctor.W ↦ PFunctor.W.head z.1)
      (h.trans (restrict_dependentLeaf p))
    change Sum.inl (some (decide ((if p w then (1 : Fin 2) else (0 : Fin 2)) = 1))) =
      (Sum.inl (some true) : (presheaf p).A) at hh
    cases hp : p w <;> simp [hp] at hh ⊢
  · intro h
    constructor
    · intro b
      rcases b with ⟨d, hd⟩
      cases d with
      | inl d =>
        change baseLeaf p (decide ((if p w then (1 : Fin 2) else (0 : Fin 2)) = 1)) =
          (presheaf p).wRestrTree PresheafPFunctor.arrow (dependentLeaf p) _
        simp only [h, ite_true, decide_true]
        exact (restrict_dependentLeaf p).symm
      | inr d => exact absurd hd (by decide : (0 : Fin 2) ≠ 1)
    · intro b
      cases b with
      | inl _ => exact dependentLeaf_natural p
      | inr _ => exact baseLeaf_natural p _

/-- A bitstring code with constructor tags, independent of the predicate. -/
@[expose] def shapeCode (p : List Bool → Bool) : (presheaf p).A → List Bool
  | .inl none => [false, false]
  | .inl (some b) => [false, true, b]
  | .inr ⟨none, w⟩ => true :: false :: w
  | .inr ⟨some b, w⟩ => true :: true :: b :: w

/-- Decode the shape tags and their payload. -/
@[expose] def shapeDecode (p : List Bool → Bool) : List Bool → Option (presheaf p).A
  | [false, false] => some (.inl none)
  | [false, true, b] => some (.inl (some b))
  | true :: false :: w => some (.inr ⟨none, w⟩)
  | true :: true :: b :: w => some (.inr ⟨some b, w⟩)
  | _ => none

/-- The finitary slice signature with its bitstring representation. -/
@[expose] def coded (p : List Bool → Bool) : CodedSig (Fin 2) where
  P := (presheaf p).toSlicePFunctor
  finitary := presheafFinitary p
  code := shapeCode p
  decode := shapeDecode p
  decode_code a := by
    match a with
    | .inl none | .inl (some _) | .inr ⟨none, _⟩ | .inr ⟨some _, _⟩ => rfl
  code_of_decode {w a} h := by
    match w, h with
    | [false, false], h => cases h; rfl
    | [false, true, b], h => cases h; rfl
    | true :: false :: w, h => cases h; rfl
    | true :: true :: b :: w, h => cases h; rfl

/-- The test tree's bitstring, computed without evaluating the predicate. -/
@[expose] def testWord (w : List Bool) : List Bool :=
  (coded (fun _ ↦ false)).spell (testTree (fun _ ↦ false) w).1

/-- Every predicate gives the same bitstring for a test tree. -/
theorem spell_testTree (p : List Bool → Bool) (w : List Bool) :
    (coded p).spell (testTree p w).1 = testWord w := by
  rfl

/-- The predicate selecting a direction in the counterexample. -/
@[expose] def predicate : List Bool → Bool := diagonal testWord

/-- No Oitavem expression decides hereditary naturality, even restricted to the
spellings of these admissible slice trees. -/
theorem no_oitavem_recognizer (e : Expr 1 0) :
    ¬ (∀ w, e.eval ![(coded predicate).spell (testTree predicate w).1] Fin.elim0 = [true] ↔
      (presheaf predicate).IsHereditarilyNatural (testTree predicate w)) := by
  intro h
  apply not_recognizes_diagonal testWord e
  intro w
  simpa only [spell_testTree, testTree_natural_iff, predicate] using h w

/-- A hom-set of the walking arrow has one element or is empty. -/
@[expose, instance_reducible] def homEnum (i i' : Fin 2) : FinEnum (i' ⟶ i) :=
  if h : i' ≤ i then
    { card := 1
      equiv :=
        { toFun := fun _ ↦ 0
          invFun := fun _ ↦ homOfLE h
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j }
      decEq := fun _ _ ↦ isTrue (Subsingleton.elim _ _) }
  else
    { card := 0
      equiv :=
        { toFun := fun f ↦ absurd (leOfHom f) h
          invFun := Fin.elim0
          left_inv := fun f ↦ absurd (leOfHom f) h
          right_inv := fun j ↦ j.elim0 }
      decEq := fun f _ ↦ absurd (leOfHom f) h }

/-- Shape equality is decidable despite the unbounded bitstring payloads. -/
@[expose] def shapeDecidableEq (p : List Bool → Bool) : DecidableEq (presheaf p).A :=
  inferInstanceAs (DecidableEq (Option Bool ⊕ (Σ _ : Option Bool, List Bool)))

/-- Raw tree equality using the shape equality and finite direction enumerations. -/
@[expose] def treeDecidableEq (p : List Bool → Bool) : DecidableEq (presheaf p).toPFunctor.W :=
  @WType.instDecidableEq _ _ (shapeDecidableEq p) (presheafFinitary p)

/-- The repository's native checker, instantiated with explicit finite-category data. -/
@[expose] def nativeCheck (p : List Bool → Bool) : (presheaf p).toPFunctor.W → Bool :=
  (presheaf p).isHereditarilyNaturalBoolCore
    (inferInstanceAs (DecidableEq (Fin 2))) (inferInstanceAs (FinEnum (Fin 2)))
    homEnum (presheafFinitary p) (treeDecidableEq p)

/-- The native checker computes precisely the predicate on the admissible test trees. -/
theorem nativeCheck_testTree (p : List Bool → Bool) (w : List Bool) :
    nativeCheck p (testTree p w).1 = p w := by
  rw [Bool.eq_iff_iff]
  exact ((presheaf p).isHereditarilyNaturalBoolCore_eq_true_iff
    (inferInstanceAs (DecidableEq (Fin 2))) (inferInstanceAs (FinEnum (Fin 2)))
    homEnum (presheafFinitary p) (treeDecidableEq p) (testTree p w)).trans
      (testTree_natural_iff p w)

/-- No unary Oitavem expression agrees with the native checker on these valid slice-tree codes. -/
theorem no_oitavem_nativeCheck (e : Expr 1 0) :
    ¬ (∀ w, e.eval ![testWord w] Fin.elim0 = [true] ↔
      nativeCheck predicate (testTree predicate w).1 = true) := by
  simpa only [nativeCheck_testTree, predicate] using not_recognizes_diagonal testWord e

end

end Geb.Oitavem.PresheafCounterexample
