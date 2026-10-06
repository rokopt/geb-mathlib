/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Kmett

set_option doc.verso true in
/-!
# The derived coalgebra category for Kmett's signature

The coalgebra counterpart uses {lit}`K(X, Y) = X → P(X, Y)`. Its diagonal elements
are mixed-variance coalgebras. Two two-state examples have the same application loop
and abstraction loop but different interactions between them.

## Main definitions

* {lit}`pointCoalgebra` is a one-state application or abstraction loop.
* {lit}`twoCoalgebra` combines these loops with a choice of their interaction.

## Main statements

* {lit}`no_terminal_coalgebra` excludes a terminal object for the derived coalgebra
  profunctor, using the incompatible interactions in the two-state examples.

## Tags

profunctor coalgebra, terminality, PHOAS
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.Kmett

open PFunctor PProfunctor

universe u v w z

/-- The abstraction projection commutes with both parameter maps. -/
theorem unlam_dimap {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
    (f : X' → X) (g : Y → Y') (t : signature.Obj X Y) :
    unlam (signature.dimap f g t) = g ∘ unlam t ∘ f := by
  obtain ⟨a, k⟩ := t
  cases a
  · funext x
    change g (k (.mk false (f ∘ PEmpty.elim))) = g (k (.mk false PEmpty.elim))
    have h : f ∘ (PEmpty.elim : PEmpty → X') = PEmpty.elim := funext fun e ↦ e.elim
    exact congrArg (fun env ↦ g (k (.mk false env))) h
  · rfl

/-- A one-state loop, with an application or abstraction operation. -/
def pointCoalgebra (tag : Bool) : signature.Coalgebra.{0, 0, 0, u} :=
  ⟨PUnit, fun _ ↦ cond tag (lamObj (fun _ ↦ PUnit.unit)) (appObj PUnit.unit PUnit.unit)⟩

/-- An application loop and an abstraction loop; the abstraction applied to the
application state returns the state selected by {lit}`cross`. -/
def twoCoalgebra (cross : Bool) : signature.Coalgebra.{0, 0, 0, u} :=
  ⟨ULift Bool, fun x ↦ cond x.down
    (lamObj (fun y ↦ ULift.up (cond y.down true cross)))
    (appObj (ULift.up false) (ULift.up false))⟩

/-- Either one-state loop embeds into both choices of interaction. -/
def pointInclusion (cross tag : Bool) :
    Coalgebra.Hom (pointCoalgebra.{u} tag) (twoCoalgebra.{u} cross) :=
  ⟨fun _ ↦ ULift.up tag, by
    funext x
    cases tag
    · apply congrArg (PFunctor.Obj.mk (P := signature.apply PUnit) false)
      funext d
      change (ULift.up false : ULift Bool) = cond d.fst (ULift.up false) (ULift.up false)
      cases d.fst <;> rfl
    · rfl⟩

/-- A morphism preserves the interaction between the two states. -/
theorem cross_eq {t : signature.Coalgebra.{0, 0, 0, u}} (cross : Bool)
    (f : Coalgebra.Hom (twoCoalgebra.{u} cross) t) :
    f.val (ULift.up cross) = unlam (t.2 (f.val (ULift.up true))) (f.val (ULift.up false)) := by
  have h := congrFun (congrArg unlam (congrFun f.property (ULift.up true))) (ULift.up false)
  simpa only [coalgebraDimap, Function.comp_apply, unlam_dimap, twoCoalgebra,
    Bool.cond_true, Bool.cond_false, unlam_lamObj, id_eq] using h

/-- No coalgebra is terminal for the derived profunctor. Uniqueness on the one-state
loops would identify both two-state maps, whose incompatible interactions then identify
an application state with an abstraction state. -/
theorem no_terminal_coalgebra (t : signature.Coalgebra.{0, 0, 0, u}) :
    ¬(∀ s : signature.Coalgebra.{0, 0, 0, u}, Nonempty (Unique (Coalgebra.Hom s t))) := by
  intro h
  obtain ⟨hf⟩ := h (twoCoalgebra false)
  obtain ⟨hg⟩ := h (twoCoalgebra true)
  let f := hf.default
  let g := hg.default
  have he (tag : Bool) : f.val (ULift.up tag) = g.val (ULift.up tag) := by
    obtain ⟨hp⟩ := h (pointCoalgebra tag)
    have hm : (pointInclusion false tag).comp f = (pointInclusion true tag).comp g :=
      (hp.uniq _).trans (hp.uniq _).symm
    exact congrArg (fun m ↦ m.val PUnit.unit) hm
  have hi : f.val (ULift.up false) = g.val (ULift.up true) :=
    (cross_eq false f).trans
      ((congr (congrArg (fun x ↦ unlam (t.2 x)) (he true)) (he false)).trans
        (cross_eq true g).symm)
  exact Bool.false_ne_true ((f.position_eq (ULift.up false)).trans
    ((congrArg (fun x ↦ (t.2 x).fst) hi).trans (g.position_eq (ULift.up true)).symm))

end Geb.PHOAS.Kmett
