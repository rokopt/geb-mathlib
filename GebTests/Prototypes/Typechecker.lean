/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Typechecker

set_option doc.verso true in
/-!
# Tests for typechecker categories

The examples check composition order, identification outside the source fiber,
empty source fibers, and separation of different actions on accepted elements.
Reflecting morphisms additionally preserve failing inputs while retaining their
actions there; their images in the quotient can coincide.

## Tags

typechecker, category, quotient
-/
set_option doc.verso true

set_option linter.privateModule false

open CategoryTheory GebProto.EndomorphismCategory
open GebProto.EndomorphismCategory.Typechecker

namespace GebTests.Typechecker

/-- All Boolean endomorphisms are admissible. -/
theorem closed : CompositionallyClosed (fun _ : Bool → Bool ↦ True) :=
  ⟨True.intro, fun _ _ _ _ ↦ True.intro⟩

/-- The submonoid containing all Boolean endomorphisms. -/
abbrev admissible := closed.toSubmonoid

/-- The typechecker accepting only false. -/
def onlyFalse : Typechecker admissible false := ⟨⟨id, True.intro⟩⟩

/-- The typechecker accepting every Boolean. -/
def all : Typechecker admissible false := ⟨⟨fun _ ↦ false, True.intro⟩⟩

/-- The typechecker accepting no Boolean. -/
def none : Typechecker admissible false := ⟨⟨fun _ ↦ true, True.intro⟩⟩

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

example : ((interpretation admissible false).map
    (negate.toHom ≫ reset.toHom) ⟨false, rfl⟩).val = false := rfl

example : ((interpretation admissible false).map
    (reset.toHom ≫ negate.toHom) ⟨false, rfl⟩).val = true := rfl

example : ((interpretation admissible false).map (𝟙 all) ⟨true, rfl⟩).val = true := rfl

example : let star : OneObject admissible := SingleObj.star admissible
    let f : star ⟶ star := ⟨Bool.not, True.intro⟩
    let g : star ⟶ star := ⟨fun _ ↦ false, True.intro⟩
    (f ≫ g).val false = false := rfl

example {B : Type 1} {P : (B → B) → Prop} (h : CompositionallyClosed P) (b : B) :
    Typechecker h.toSubmonoid b ⥤ Type 1 := interpretation h.toSubmonoid b

/-- Negation as a reflecting morphism of the full fiber. -/
def reflectingNegate : (⟨all⟩ : ReflectingTypechecker admissible false) ⟶ ⟨all⟩ :=
  ⟨negate, fun _ _ ↦ rfl⟩

/-- Constant false as a reflecting morphism of the full fiber. -/
def reflectingReset : (⟨all⟩ : ReflectingTypechecker admissible false) ⟶ ⟨all⟩ :=
  ⟨reset, fun _ _ ↦ rfl⟩

example : (ReflectingTypechecker.toQuotient admissible false).obj ⟨all⟩ = all := rfl

example : (ReflectingTypechecker.toQuotient admissible false).map reflectingNegate =
    negate.toHom := rfl

example : (reflectingNegate ≫ reflectingReset).val.val.val false = false := rfl

example : (reflectingReset ≫ reflectingNegate).val.val.val false = true := rfl

example : (ReflectingTypechecker.toQuotient admissible false).map
    (reflectingNegate ≫ reflectingReset) = negate.toHom ≫ reset.toHom := rfl

/-- Negation preserves and reflects passing for the empty fiber. -/
def emptyNegate : (⟨none⟩ : ReflectingTypechecker admissible false) ⟶ ⟨none⟩ :=
  ⟨⟨⟨Bool.not, True.intro⟩, fun _ hx ↦ hx⟩, fun _ hx ↦ hx⟩

example : emptyNegate ≠ 𝟙 (⟨none⟩ : ReflectingTypechecker admissible false) := by
  intro h
  exact Bool.noConfusion (congrArg (fun f ↦ f.val.val.val false) h)

example : (ReflectingTypechecker.toQuotient admissible false).map emptyNegate = 𝟙 none :=
  (Representative.toHom_eq_iff _ _).2 fun _ hx ↦ Bool.noConfusion hx

example (f : (⟨onlyFalse⟩ : ReflectingTypechecker admissible false) ⟶ ⟨onlyFalse⟩) :
    f.val.val.val true ≠ false :=
  (ReflectingTypechecker.map_fail_iff f true).2 Bool.noConfusion

example {B : Type 1} {P : (B → B) → Prop} (h : CompositionallyClosed P) (b : B) :
    ReflectingTypechecker h.toSubmonoid b ⥤ Typechecker h.toSubmonoid b :=
  ReflectingTypechecker.toQuotient h.toSubmonoid b

end GebTests.Typechecker
