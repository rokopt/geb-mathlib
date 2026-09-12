/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Arrow

/-!
# Tests for the walking-arrow presheaf polynomial functor

The natural numbers as a W-type, with the finite-set family over them as the
dependent part, exercise the base equivalence and the computation rule of the
fiber family: the fiber over zero is empty, and the fiber over a successor has
a zero element and a successor element for each element of the fiber below.

## Tags

polynomial functor, presheaf, walking arrow, W-type, dependent type
-/

set_option linter.privateModule false

open CategoryTheory PFunctor.Dependent

/-- The polynomial functor of the natural numbers: the shape `true` (successor)
with one direction, the shape `false` (zero) with none. -/
def natPFunctor : PFunctor := ⟨Bool, fun b ↦ cond b PUnit PEmpty⟩

/-- The dependent part of the finite-set family: over a successor, the shape
`false` (the new zero) with no direction and the shape `true` (the successor of
an element below) with one direction, lying over the one direction of the base;
over zero, no shape. -/
def natFam : ∀ b : Bool, SliceDomPFunctor.{0, 0, 0} (natPFunctor.B b)
  | true => ⟨⟨Bool, fun a ↦ cond a PUnit PEmpty⟩, fun _ ↦ PUnit.unit⟩
  | false => ⟨⟨PEmpty, fun e ↦ e.elim⟩, fun x ↦ x.1.elim⟩

/-- Zero as a tree. -/
def zero : natPFunctor.W := WType.mk false PEmpty.elim

/-- Successor on trees. -/
def succ (n : natPFunctor.W) : natPFunctor.W := WType.mk true fun _ ↦ n

/-- The finite-set family over the natural numbers, as the fiber family of the
walking-arrow endofunctor's W-type. -/
abbrev finFam : natPFunctor.W → Type := Fiber natPFunctor natFam

-- The fiber over `0` of the W-type is the natural numbers: the carried tree of
-- a successor has the base shape `true` at its root, and its base tree is the
-- successor again.
example : PFunctor.W.head ((baseEquiv natPFunctor natFam).symm (succ zero)).down.1.1 =
    Sum.inl true :=
  rfl
example : baseEquiv natPFunctor natFam ((baseEquiv natPFunctor natFam).symm (succ zero)) =
    succ zero :=
  (baseEquiv natPFunctor natFam).apply_symm_apply _

-- The fiber over zero is empty: the computation rule lands in a value of the
-- shapeless functor.
example : finFam zero → False :=
  fun u ↦ (fiberMkEquiv natPFunctor natFam false PEmpty.elim u).1.1.elim

/-- The zero element of the fiber over a successor: the shape `false`, with no
children. -/
def fz (n : natPFunctor.W) : finFam (succ n) :=
  (fiberMkEquiv natPFunctor natFam true fun _ ↦ n).symm
    ⟨⟨false, fun d ↦ d.elim⟩, funext fun d ↦ d.elim⟩

/-- The successor element of the fiber over a successor: the shape `true`, with
the given element of the fiber below as its one child. -/
def fs (n : natPFunctor.W) (i : finFam n) : finFam (succ n) :=
  (fiberMkEquiv natPFunctor natFam true fun _ ↦ n).symm ⟨⟨true, fun _ ↦ ⟨PUnit.unit, i⟩⟩, rfl⟩

-- A fiber element lies over its index: the restriction of `fz n` along the
-- arrow is the carried `succ n`.
example (n : natPFunctor.W) :
    baseEquiv natPFunctor natFam
      (((PFunctor.dependent natPFunctor natFam).W).map PresheafPFunctor.arrow.op (fz n).1) =
      succ n := by
  rw [(fz n).2]
  exact (baseEquiv natPFunctor natFam).apply_symm_apply _

-- The computation rule recovers a successor element's shape and child.
example (n : natPFunctor.W) (i : finFam n) :
    fiberMkEquiv natPFunctor natFam true (fun _ ↦ n) (fs n i) =
      ⟨⟨true, fun _ ↦ ⟨PUnit.unit, i⟩⟩, rfl⟩ :=
  (fiberMkEquiv natPFunctor natFam true fun _ ↦ n).apply_symm_apply _
