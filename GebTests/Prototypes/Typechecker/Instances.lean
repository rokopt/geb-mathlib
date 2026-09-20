/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Typechecker.Instances
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Inv

set_option doc.verso true in
/-!
# Tests for decision-problem limit and colimit instances

The terminal condition resolves the existence instance. The chosen cone is also
accepted by the constructor for the cartesian structure used by
{lit}`ElementaryTopos`, with binary product cones supplied as parameters.
The constant-false condition resolves initial-object existence and supplies a
cocone over the empty diagram in the universe used by its initial-object field.
Pair coding supplies binary-product instances and, with a singleton checker, the
cartesian structure. Tagged-union coding supplies the binary-coproduct cocone and instances.
A Boolean base demonstrates the finite-cardinality obstructions to products and coproducts.
Agreement checkers supply equalizer instances and a chosen cone over each parallel pair.
Class normalizers additionally supply coequalizer instances and chosen cocones.
Extensional function coding supplies the closed field over the chosen cartesian structure;
an admissible function without fixed points obstructs closure of the full base object.
Finite Boolean search constructs a classifier, including its image inverses, independently
of products. The combined sufficient conditions have the elementary-topos interface.

## Tags

decision problem, terminal object, initial object, instance, elementary topos
-/
set_option doc.verso true

set_option linter.privateModule false

open CategoryTheory Limits GebProto.EndomorphismCategory
open GebProto.EndomorphismCategory.DecisionProblem

universe u

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

example [Fact (HasTrueSingletonChecker S t f)] : HasTerminal (DecisionProblem S t f) :=
  inferInstance

example (T : DecisionProblem S t f) (hT : ∀ x : B, T.checker.val x = t ↔ x = t)
    (products : ∀ X Y : DecisionProblem S t f, LimitCone (pair X Y)) :
    CartesianMonoidalCategory (DecisionProblem S t f) :=
  .ofChosenFiniteProducts (terminalCone T hT) products

example [Fact (HasFalseChecker S t f)] : HasInitial (DecisionProblem S t f) := inferInstance

example (h : HasFalseChecker S t f) :
    ColimitCocone (Functor.empty.{0} (DecisionProblem S t f)) := initialCocone h

example [Nonempty (ProductCoding S t f)] : HasBinaryProducts (DecisionProblem S t f) :=
  inferInstance

example [Nonempty (ProductCoding S t f)] (X Y : DecisionProblem S t f) :
    HasLimit (pair X Y) := inferInstance

example (T : DecisionProblem S t f) (hT : ∀ x, T.checker.val x = t ↔ x = t)
    (d : ProductCoding S t f) : CartesianMonoidalCategory (DecisionProblem S t f) :=
  cartesianMonoidalCategory T hT d

example (U : DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false)
    (hU : ∀ x, U.checker.val x = true) : ¬HasLimit (pair U U) :=
  not_hasLimit_pair_self (fun _ hr ↦ Finite.surjective_of_injective hr) U hU

example [Nonempty (CoproductCoding S t f)] : HasBinaryCoproducts (DecisionProblem S t f) :=
  inferInstance

example [Nonempty (CoproductCoding S t f)] (X Y : DecisionProblem S t f) :
    HasColimit (pair X Y) := inferInstance

example (d : CoproductCoding S t f) (X Y : DecisionProblem S t f) :
    ColimitCocone (pair X Y) := binaryCoproductCocone d X Y

example (U : DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false)
    (hU : ∀ x, U.checker.val x = true) : ¬HasColimit (pair U U) :=
  not_hasColimit_pair_self (fun _ hr ↦ Finite.surjective_of_injective hr) U hU

example [Nonempty (EqualizerCheckers S t f)] : HasEqualizers (DecisionProblem S t f) :=
  inferInstance

example [Nonempty (EqualizerCheckers S t f)] {X Y : DecisionProblem S t f} (r s : X ⟶ Y) :
    HasLimit (parallelPair r s) := inferInstance

example (d : EqualizerCheckers S t f) {X Y : DecisionProblem S t f} (r s : X ⟶ Y) :
    LimitCone (parallelPair r s) := equalizerCone d r s

example [Nonempty (EqualizerCheckers S t f)] [Nonempty (CoequalizerNormalForms S t f)] :
    HasCoequalizers (DecisionProblem S t f) := inferInstance

example [Nonempty (EqualizerCheckers S t f)] [Nonempty (CoequalizerNormalForms S t f)]
    {X Y : DecisionProblem S t f} (r s : X ⟶ Y) : HasColimit (parallelPair r s) := inferInstance

example (d : EqualizerCheckers S t f) (n : CoequalizerNormalForms S t f) :
    ∀ {X Y : DecisionProblem S t f} (r s : X ⟶ Y), ColimitCocone (parallelPair r s) :=
  fun r s ↦ coequalizerCocone d (n r s)

example (T : DecisionProblem S t f) (hT : ∀ x, T.checker.val x = t ↔ x = t)
    (p : ProductCoding S t f) (X : DecisionProblem S t f)
    (d : ∀ Y, ExponentialCoding p X Y) :
    letI := cartesianMonoidalCategory T hT p
    Closed X := closedOfCoding T hT p X d

example (T : DecisionProblem S t f) (hT : ∀ x, T.checker.val x = t ↔ x = t)
    (p : ProductCoding S t f) (d : ∀ X Y, ExponentialCoding p X Y) :
    @MonoidalClosed (DecisionProblem S t f) _
      (cartesianMonoidalCategory T hT p).toMonoidalCategory := monoidalClosed T hT p d

example (T : DecisionProblem S t f) (hT : ∀ x, T.checker.val x = t ↔ x = t)
    (p : ProductCoding S t f) (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t)
    (a : S) (ha : ∀ y, a.val y ≠ y) :
    letI := cartesianMonoidalCategory T hT p
    ¬Nonempty (Closed U) := not_closed T hT p U hU a ha

example [Nonempty (ClassifierData S t f)] :
    HasSubobjectClassifier (DecisionProblem S t f) := inferInstance

example (d : ClassifierData S t f) (p : ProductCoding S t f) :
    letI := cartesianMonoidalCategory d.terminal d.terminal_pass_iff p
    ¬Nonempty (MonoidalClosed (DecisionProblem S t f)) :=
  not_monoidalClosed_of_classifierData d p

example (d : ClassifierData S t f) (p : ProductCoding S t f)
    (c : CoproductCoding S t f) (e : EqualizerCheckers S t f)
    (n : CoequalizerNormalForms S t f) (h : ∀ X Y, ExponentialCoding p X Y) :
    ElementaryTopos (DecisionProblem S t f) := elementaryTopos d p c e n h

namespace BooleanClassifier

/-- Boolean predicates as decision problems over all Boolean functions. -/
def problem (p : Bool → Prop) [DecidablePred p] :
    DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false :=
  ⟨⟨fun x ↦ if p x then true else false, True.intro⟩,
    ⟨by decide, fun x ↦ by dsimp; split <;> simp⟩⟩

variable {X Y : DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false}

local instance (X : DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false) :
    Fintype (Fiber X) :=
  @Subtype.fintype Bool (fun x ↦ X.checker.val x = true) (fun _ ↦ inferInstance) inferInstance

/-- Finite search computes the unique accepted preimage of an image point. -/
def preimage (m : X ⟶ Y) [Mono m] (y : Bool)
    (h : ∃ x : Fiber X, (m.restrict x).val = y) :
    { x : Fiber X // (m.restrict x).val = y } :=
  Fintype.chooseX _ (by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, hx, fun z hz ↦ ?_⟩
    exact (DecisionProblem.mono_iff_injective
      (S := (⊤ : Submonoid (Function.End Bool))) (fun _ ↦ True.intro) m).mp inferInstance
      (Subtype.ext (hz.trans hx.symm)))

/-- Exhaustive Boolean search supplies image tests and inverse functions, including empty images. -/
def monoImage (m : X ⟶ Y) [Mono m] : MonoImage m where
  image := problem (fun y ↦ ∃ x : Fiber X, (m.restrict x).val = y)
  pass_iff y := by simp [problem]
  inverse := ⟨⟨fun y ↦ if h : ∃ x : Fiber X, (m.restrict x).val = y
    then (preimage m y h).val.val else false, True.intro⟩, fun y hy ↦ by
      have h : ∃ x : Fiber X, (m.restrict x).val = y := by simpa [problem] using hy
      simpa only [dite_eq_left h, acceptedFiber, Set.mem_ofPred_eq] using
        (preimage m y h).val.property⟩
  inverse_spec y := by
    have h : ∃ x : Fiber X, (m.restrict x).val = y.val := by
      simpa [problem, acceptedFiber] using y.property
    change (m.restrict ⟨(if h : ∃ x : Fiber X, (m.restrict x).val = y.val
      then (preimage m y.val h).val.val else false), _⟩).val = y.val
    simp only [dite_eq_left h]
    exact (preimage m y.val h).property

/-- A concrete classifier exists on a Boolean base, although that category lacks binary products. -/
def data : ClassifierData (⊤ : Submonoid (Function.End Bool)) true false where
  constants _ := True.intro
  terminal := problem (· = true)
  terminal_pass_iff _ := by simp [problem]
  omega := problem (fun _ ↦ True)
  omega_pass_iff x := by cases x <;> simp [problem]
  monoImage m _ := monoImage m

example : Subobject.Classifier
    (DecisionProblem (⊤ : Submonoid (Function.End Bool)) true false) := data.classifier

example (m : X ⟶ Y) [Mono m] :
    IsPullback m (data.toTerminal X) (data.chi m) data.truth := data.isPullback m

end BooleanClassifier
