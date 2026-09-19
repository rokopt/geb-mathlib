/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Typechecker.Terminal -- shake: keep

set_option doc.verso true in
/-!
# Tests for typechecker categories

The examples check composition order, identification outside the source fiber,
empty source fibers, and separation of different actions on accepted elements.
Checkers have two outputs while reductions may return other base elements.
Singleton checkers on the natural numbers demonstrate terminal objects beyond
two-element bases, and a restricted submonoid shows why accessibility matters.

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

end GebTests.Typechecker
