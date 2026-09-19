/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Typechecker.Coproducts
import Geb.Prototypes.Typechecker.Coequalizers
import Geb.Prototypes.Typechecker.Exponentials
import Geb.Prototypes.Typechecker.Terminal -- shake: keep
import Mathlib.Data.Tree.Basic

set_option doc.verso true in
/-!
# Tests for typechecker categories

The examples check composition order, identification outside the source fiber,
empty source fibers, and separation of different actions on accepted elements.
Checkers have two outputs while reductions may return other base elements.
Singleton checkers on the natural numbers demonstrate terminal objects beyond
two-element bases, and a restricted submonoid shows why accessibility matters.
The submonoid containing only the Boolean identity supplies an initial object with nonempty
accepted fiber, showing that admissibility of constant false is not necessary.
Binary trees supply a product coding with a proper range: the leaf is rejected
as a pair code even when both decoded components pass.
Tagged pairs test coproduct injections, branch selection, and rejection of a third tag.
Boolean equalizers test agreement filtering independently of product coding, including
rejection outside the source and independence from morphism representatives.
A coequalizer collapses a chain of three trees while preserving an unrelated tree.
Singleton arguments give exponential codes equal to their output values. A
fixed-point-free tree function rules out coding the full endomorphism space.

## Tags

typechecker, category, quotient
-/
set_option doc.verso true

set_option linter.privateModule false

open CategoryTheory GebProto.EndomorphismCategory
open GebProto.EndomorphismCategory.DecisionProblem

namespace GebTests.Typechecker

/-- All Boolean endomorphisms are admissible. -/
theorem closed : CompositionallyClosed (fun _ : Bool → Bool ↦ True) :=
  ⟨True.intro, fun _ _ _ _ ↦ True.intro⟩

/-- The submonoid containing all Boolean endomorphisms. -/
abbrev admissible := closed.toSubmonoid

/-- Every Boolean endomorphism has the required two-value range. -/
theorem bool_twoValued (p : Bool → Bool) : TwoValued false true p :=
  ⟨Bool.noConfusion, fun x ↦ Bool.casesOn (p x) (Or.inl rfl) (Or.inr rfl)⟩

/-- The typechecker accepting only false. -/
def onlyFalse : DecisionProblem admissible false true :=
  ⟨⟨id, True.intro⟩, bool_twoValued id⟩

/-- The typechecker accepting every Boolean. -/
def all : DecisionProblem admissible false true :=
  ⟨⟨fun _ ↦ false, True.intro⟩, bool_twoValued _⟩

/-- The typechecker accepting no Boolean. -/
def none : DecisionProblem admissible false true :=
  ⟨⟨fun _ ↦ true, True.intro⟩, bool_twoValued _⟩

/-- Identity as a map from the singleton fiber to the full fiber. -/
def includeFalse : Representative onlyFalse all := ⟨⟨id, True.intro⟩, fun _ _ ↦ rfl⟩

/-- Constant false as a map from the singleton fiber to the full fiber. -/
def constantFalse : Representative onlyFalse all :=
  ⟨⟨fun _ ↦ false, True.intro⟩, fun _ _ ↦ rfl⟩

example : includeFalse.val.val ≠ constantFalse.val.val := by
  intro h
  exact Bool.noConfusion (congrFun h true)

example : includeFalse.toHom = constantFalse.toHom :=
  (Representative.toHom_eq_iff _ _).2 fun _ hx ↦ hx

example (f g : Representative none all) : f.toHom = g.toHom :=
  (Representative.toHom_eq_iff _ _).2 fun _ hx ↦ Bool.noConfusion hx

/-- Boolean negation preserves the full fiber. -/
def negate : Representative all all := ⟨⟨Bool.not, True.intro⟩, fun _ _ ↦ rfl⟩

/-- Constant false preserves the full fiber. -/
def reset : Representative all all :=
  ⟨⟨fun _ ↦ false, True.intro⟩, fun _ _ ↦ rfl⟩

example : negate.toHom ≠ reset.toHom := by
  intro h
  exact Bool.noConfusion ((Representative.toHom_eq_iff _ _).1 h false rfl)

example : ((interpretation admissible false true).map
    (negate.toHom ≫ reset.toHom) ⟨false, rfl⟩).val = false := rfl

example : ((interpretation admissible false true).map
    (reset.toHom ≫ negate.toHom) ⟨false, rfl⟩).val = true := rfl

example : ((interpretation admissible false true).map (𝟙 all) ⟨true, rfl⟩).val = true := rfl

example : let star : OneObject admissible := SingleObj.star admissible
    let f : star ⟶ star := ⟨Bool.not, True.intro⟩
    let g : star ⟶ star := ⟨fun _ ↦ false, True.intro⟩
    (f ≫ g).val false = false := rfl

example {B : Type 1} {P : (B → B) → Prop} (h : CompositionallyClosed P) (t f : B) :
    DecisionProblem h.toSubmonoid t f ⥤ Type 1 := interpretation h.toSubmonoid t f

/-- A natural-number checker accepting exactly one designated input. -/
def pointChecker (a n : ℕ) : ℕ := if n = a then 1 else 0

/-- A singleton checker uses only one and zero as outputs. -/
theorem pointChecker_twoValued (a : ℕ) : TwoValued 1 0 (pointChecker a) :=
  ⟨by decide, fun n ↦ by
    by_cases hn : n = a
    · exact Or.inl (ite_eq_left hn)
    · exact Or.inr (ite_eq_right hn)⟩

/-- The checker accepts exactly its designated input. -/
theorem pointChecker_pass_iff (a n : ℕ) : pointChecker a n = 1 ↔ n = a := by
  by_cases hn : n = a <;> simp only [pointChecker, hn, reduceIte, Nat.zero_ne_one]

/-- The natural-number decision problem accepting exactly zero. -/
def zeroDecision : DecisionProblem (⊤ : Submonoid (Function.End ℕ)) 1 0 :=
  ⟨⟨pointChecker 0, True.intro⟩, pointChecker_twoValued 0⟩

/-- Doubling preserves being zero, without having only two output values. -/
def doubleReduction : Representative zeroDecision zeroDecision :=
  ⟨⟨fun n ↦ n + n, True.intro⟩, fun n hn ↦ by
    change pointChecker 0 (n + n) = 1
    exact (pointChecker_pass_iff 0 _).mpr
      (Nat.add_eq_zero_iff.mpr ⟨(pointChecker_pass_iff 0 n).mp hn,
        (pointChecker_pass_iff 0 n).mp hn⟩)⟩

example : (doubleReduction.comp doubleReduction).val.val 2 = 8 := rfl

example : ¬TwoValued (1 : ℕ) 0 doubleReduction.val.val := by
  intro h
  exact (by decide : ¬((4 : ℕ) = 1 ∨ 4 = 0)) (h.2 2)

/-- A checker whose accepted fiber is the singleton true value. -/
def oneDecision : DecisionProblem (⊤ : Submonoid (Function.End ℕ)) 1 0 :=
  ⟨⟨pointChecker 1, True.intro⟩, pointChecker_twoValued 1⟩

example (X : DecisionProblem (⊤ : Submonoid (Function.End ℕ)) 1 0) :
    Unique (X ⟶ oneDecision) :=
  uniqueToTrueSingleton oneDecision (pointChecker_pass_iff 1) X

/-- Endomorphisms that are either the identity or use only the two truth values. -/
def identityOrTwoValued : Submonoid (Function.End ℕ) where
  carrier := {p | p = id ∨ TwoValued 1 0 p}
  one_mem' := Or.inl rfl
  mul_mem' {p q} hp hq := by
    rcases hp with rfl | hp
    · exact hq
    · exact Or.inr (hp.comp_right q)

/-- A singleton checker whose accepted element lies outside the truth values. -/
def inaccessibleSingleton : DecisionProblem identityOrTwoValued 1 0 :=
  ⟨⟨pointChecker 2, Or.inr (pointChecker_twoValued 2)⟩, pointChecker_twoValued 2⟩

example : ¬Nonempty (∀ X : DecisionProblem identityOrTwoValued 1 0,
    Unique (X ⟶ inaccessibleSingleton)) := by
  intro h
  have ha := (unique_to_singleton_iff_constant_mem inaccessibleSingleton 2
    (pointChecker_pass_iff 2) (Or.inr ⟨by decide, fun _ ↦ Or.inl rfl⟩)).mp h
  rcases ha with ha | ha
  · exact (by decide : (2 : ℕ) ≠ 0) (congrFun ha 0)
  · exact (by decide : ¬((2 : ℕ) = 1 ∨ 2 = 0)) (ha.2 0)

example (X : DecisionProblem admissible false true) : Unique (none ⟶ X) :=
  uniqueFromEmpty none (fun _ ↦ Bool.noConfusion) X

/-- The identity checker when the only admissible endomorphism is identity. -/
def onlyIdentity : DecisionProblem (⊥ : Submonoid (Function.End Bool)) false true :=
  ⟨1, bool_twoValued id⟩

/-- The identity-only algebra makes its Boolean checker initial despite its nonempty fiber. -/
@[instance_reducible]
def uniqueFromOnlyIdentity (X : DecisionProblem (⊥ : Submonoid (Function.End Bool)) false true) :
    Unique (onlyIdentity ⟶ X) where
  default := Representative.toHom
    ⟨1, fun x hx ↦
      (congrFun ((Submonoid.mem_bot (M := Function.End Bool)).mp X.checker.property) x).trans hx⟩
  uniq r := Quotient.inductionOn r fun r ↦
    (Representative.toHom_eq_iff _ _).mpr fun x _ ↦
      congrFun ((Submonoid.mem_bot (M := Function.End Bool)).mp r.val.property) x

example : ¬HasFalseChecker (⊥ : Submonoid (Function.End Bool)) false true := by
  intro h
  exact Bool.noConfusion
    (congrFun ((Submonoid.mem_bot (M := Function.End Bool)).mp h.2) false)

/-- A fixed non-leaf tree serves as true; the leaf serves as false. -/
def treeTrue : BinaryTree Unit := .node () .nil .nil

/-- A decidable predicate as a tree-valued checker, with all endomorphisms admissible. -/
def treeDecision (p : BinaryTree Unit → Prop) [DecidablePred p] :
    DecisionProblem (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil :=
  ⟨⟨fun x ↦ if p x then treeTrue else .nil, True.intro⟩,
    ⟨by decide, fun x ↦ by
      by_cases hx : p x
      · exact Or.inl (ite_eq_left hx)
      · exact Or.inr (ite_eq_right hx)⟩⟩

/-- The tree checker accepts exactly the predicate used to construct it. -/
theorem treeDecision_pass_iff (p : BinaryTree Unit → Prop) [DecidablePred p]
    (x : BinaryTree Unit) : (treeDecision p).checker.val x = treeTrue ↔ p x := by
  by_cases hx : p x <;> simp [treeDecision, treeTrue, hx]

/-- Internal nodes encode pairs, and the leaf is outside the encoding's range. -/
def treeProductCoding :
    ProductCoding (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil where
  encode := BinaryTree.node ()
  left := ⟨BinaryTree.left, True.intro⟩
  right := ⟨BinaryTree.right, True.intro⟩
  left_encode _ _ := rfl
  right_encode _ _ := rfl
  pair_mem _ _ := True.intro
  codes := treeDecision (· ≠ .nil)
  codes_pass_iff x := by
    rw [treeDecision_pass_iff]
    cases x <;> simp [BinaryTree.left, BinaryTree.right]
  conjunction X Y := @treeDecision
    (fun x ↦ X.checker.val x = treeTrue ∧ Y.checker.val x = treeTrue) (fun _ ↦ inferInstance)
  conjunction_pass_iff X Y x := @treeDecision_pass_iff _ (fun _ ↦ inferInstance) x

example : (treeProductCoding.product (treeDecision (· = .nil))
    (treeDecision (· = .nil))).checker.val treeTrue = treeTrue := rfl

example : (treeProductCoding.product (treeDecision (· = .nil))
    (treeDecision (· = .nil))).checker.val .nil = .nil := rfl

/-- All tree endomorphisms are closed under decidable conditionals. -/
def treeConditionals :
    DecisionConditionals (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil where
  choose p r s := ⟨fun x ↦ if p.checker.val x = treeTrue then r.val x else s.val x,
    True.intro⟩
  choose_true _ _ _ _ hx := ite_eq_left hx
  choose_false p _ _ _ hx := ite_eq_right fun ht ↦ p.twoValued.1 (ht.symm.trans hx)

/-- The two fixed tree tags turn the product coding into a coproduct coding. -/
def treeCoproductCoding :
    CoproductCoding (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil :=
  .ofProducts treeProductCoding treeConditionals
    (treeDecision (· = treeTrue)) (treeDecision (· = .nil))
    (treeDecision_pass_iff _) (treeDecision_pass_iff _) True.intro True.intro

example : (treeCoproductCoding.coproduct (treeDecision (· = .nil))
    (treeDecision (· = treeTrue))).checker.val (.node () treeTrue .nil) = treeTrue := rfl

example : (treeCoproductCoding.coproduct (treeDecision (· = .nil))
    (treeDecision (· = treeTrue))).checker.val (.node () .nil treeTrue) = treeTrue := rfl

example : (treeCoproductCoding.coproduct (treeDecision (· = .nil))
    (treeDecision (· = treeTrue))).checker.val (.node () .nil .nil) = .nil := rfl

example : (treeCoproductCoding.coproduct (treeDecision (fun _ ↦ True))
    (treeDecision (fun _ ↦ True))).checker.val .nil = .nil := rfl

example : (treeCoproductCoding.coproduct (treeDecision (fun _ ↦ True))
    (treeDecision (fun _ ↦ True))).checker.val
      (.node () (.node () treeTrue treeTrue) .nil) = .nil := rfl

example : (treeCoproductCoding.merge ⟨fun _ ↦ treeTrue, True.intro⟩
    ⟨fun _ ↦ .nil, True.intro⟩).val (.node () treeTrue .nil) = treeTrue := rfl

example : (treeCoproductCoding.merge ⟨fun _ ↦ treeTrue, True.intro⟩
    ⟨fun _ ↦ .nil, True.intro⟩).val (.node () .nil .nil) = .nil := rfl

/-- Boolean checkers can filter their accepted inputs by equality of admissible outputs. -/
def boolEqualizerCheckers : EqualizerCheckers admissible false true where
  filter X r s :=
    ⟨⟨fun x ↦ if X.checker.val x = false ∧ r.val x = s.val x then false else true, True.intro⟩,
      bool_twoValued _⟩
  filter_pass_iff X r s x := by
    change (if X.checker.val x = false ∧ r.val x = s.val x then false else true) = false ↔ _
    by_cases hx : X.checker.val x = false ∧ r.val x = s.val x <;> simp [hx]

example : (boolEqualizerCheckers.equalizer negate.toHom reset.toHom).checker.val true = false := rfl

example : (boolEqualizerCheckers.equalizer negate.toHom reset.toHom).checker.val false = true := rfl

example : (boolEqualizerCheckers.equalizer includeFalse.toHom includeFalse.toHom).checker.val
    true = true := rfl

example : boolEqualizerCheckers.equalizer includeFalse.toHom constantFalse.toHom = onlyFalse := by
  have h : includeFalse.toHom = constantFalse.toHom :=
    (Representative.toHom_eq_iff _ _).mpr fun _ hx ↦ hx
  rw [h, boolEqualizerCheckers.equalizer_self]

/-- A tree equality test supplies agreement filtering from the existing product coding. -/
def treeEqualizerCheckers :
    EqualizerCheckers (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil :=
  .ofProducts treeProductCoding
    (@treeDecision (fun z ↦ z.left = z.right) (fun _ ↦ inferInstance))
    (fun x y ↦ @treeDecision_pass_iff _ (fun _ ↦ inferInstance) (.node () x y))

example : (treeEqualizerCheckers.filter (treeDecision (fun _ ↦ True))
    ⟨BinaryTree.left, True.intro⟩ ⟨BinaryTree.right, True.intro⟩).checker.val
      (.node () treeTrue treeTrue) = treeTrue := rfl

example : (treeEqualizerCheckers.filter (treeDecision (fun _ ↦ True))
    ⟨BinaryTree.left, True.intro⟩ ⟨BinaryTree.right, True.intro⟩).checker.val
      (.node () treeTrue .nil) = .nil := rfl

/-- The third vertex in the chain identified by the coequalizer test. -/
def chainEnd : BinaryTree Unit := .node () treeTrue .nil

/-- Two source inputs generate the two edges of a three-vertex chain. -/
def chainSource := treeDecision (fun x ↦ x = .nil ∨ x = treeTrue)

/-- Every tree is accepted in the target of the chain diagram. -/
def chainTarget := treeDecision (fun _ ↦ True)

/-- The left endpoints of the chain edges are the two source values themselves. -/
def chainLeft : Representative chainSource chainTarget := ⟨1, fun _ _ ↦ rfl⟩

/-- The right endpoints advance from the leaf to true and from true to the third vertex. -/
def chainRight : Representative chainSource chainTarget :=
  ⟨⟨fun x ↦ if x = .nil then treeTrue else chainEnd, True.intro⟩, fun _ _ ↦ rfl⟩

/-- Collapse the three-vertex chain to the leaf and leave every other tree fixed. -/
def chainNormalizer : ClassNormalizer chainLeft.toHom chainRight.toHom where
  normalize := ⟨⟨fun x ↦ if x = treeTrue ∨ x = chainEnd then .nil else x, True.intro⟩,
    fun _ _ ↦ rfl⟩
  related y := by
    have h01 : CoequalizerRel chainLeft.toHom chainRight.toHom
        ⟨.nil, rfl⟩ ⟨treeTrue, rfl⟩ := .rel _ _ ⟨⟨.nil, rfl⟩, rfl, rfl⟩
    have h12 : CoequalizerRel chainLeft.toHom chainRight.toHom
        ⟨treeTrue, rfl⟩ ⟨chainEnd, rfl⟩ := .rel _ _ ⟨⟨treeTrue, rfl⟩, rfl, rfl⟩
    obtain ⟨y, hy⟩ := y
    by_cases h1 : y = treeTrue
    · subst y
      exact .symm _ _ h01
    · by_cases h2 : y = chainEnd
      · subst y
        exact .trans _ _ _ (.symm _ _ h12) (.symm _ _ h01)
      · change CoequalizerRel _ _ ⟨y, hy⟩
          ⟨if y = treeTrue ∨ y = chainEnd then .nil else y, _⟩
        simp only [h1, h2, or_self, reduceIte]
        exact .refl _
  identifies x := by
    obtain ⟨x, hx⟩ := x
    rcases (treeDecision_pass_iff _ x).mp hx with rfl | rfl <;> rfl

example : (chainNormalizer.coequalizer treeEqualizerCheckers).checker.val .nil = treeTrue := rfl

example : (chainNormalizer.coequalizer treeEqualizerCheckers).checker.val treeTrue = .nil := rfl

example : (chainNormalizer.coequalizer treeEqualizerCheckers).checker.val chainEnd = .nil := rfl

example : (chainNormalizer.coequalizer treeEqualizerCheckers).checker.val
    (.node () .nil treeTrue) = treeTrue := rfl

example : chainNormalizer.π treeEqualizerCheckers ≫
    chainNormalizer.desc treeEqualizerCheckers chainNormalizer.normalize.toHom =
      chainNormalizer.normalize.toHom :=
  chainNormalizer.π_desc treeEqualizerCheckers _ chainNormalizer.normalizes

/-- Functions from the leaf singleton are coded by their output values. -/
def leafExponentialCoding (Y :
    DecisionProblem (⊤ : Submonoid (Function.End (BinaryTree Unit))) treeTrue .nil) :
    ExponentialCoding treeProductCoding (treeDecision (· = .nil)) Y :=
  singletonExponentialCoding treeProductCoding _ Y .nil
    (treeDecision_pass_iff _) True.intro

example : (leafExponentialCoding chainTarget).eval.val.val
    (treeProductCoding.encode .nil chainEnd) = chainEnd := rfl

example : ((leafExponentialCoding chainTarget).curryRep
    (treeProductCoding.sndRep _ chainTarget)).val.val chainEnd = chainEnd := rfl

example (h : treeProductCoding.product (treeDecision (· = .nil)) chainTarget ⟶ chainTarget) :
    (leafExponentialCoding chainTarget).uncurry
      ((leafExponentialCoding chainTarget).curry h) = h :=
  (leafExponentialCoding chainTarget).uncurry_curry h

example : ¬Nonempty (ExponentialCoding treeProductCoding chainTarget chainTarget) := by
  apply not_nonempty_exponentialCoding_self treeProductCoding chainTarget (fun _ ↦ rfl)
    ⟨fun x ↦ if x = .nil then treeTrue else .nil, True.intro⟩
  intro x
  by_cases hx : x = .nil
  · subst x
    decide
  · simpa only [ite_eq_right hx] using Ne.symm hx

end GebTests.Typechecker
