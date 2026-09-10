/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.WalkingArrow
import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures

/-!
# Walking-arrow families over ordinary W-types

A recursive fixture has one nullary and one unary constructor at the base.
Its total-space successor has a base child and a total-space child, related by
naturality. Tests compute base trees and indices through multiple constructors.
The shared fixture also tests a family with both inhabited and empty fibres.

## Tags

presheaf, walking arrow, W-type, dependent type
-/

set_option linter.privateModule false

open CategoryTheory PresheafPFunctor PresheafPFunctor.WalkingArrow

namespace WalkingArrowTests

/-- Shapes record the level and whether the constructor is a successor. -/
@[reducible] def natData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Fin 2 × Bool
  B a := { i : Fin 2 // i ≤ a.1 ∧ a.2 = true }
  q := Prod.fst
  r d := d.2.1
  directionRestr := fun _a {_i i'} g b ↦
    ⟨⟨i', (g.down.down.trans (b.2 ▸ b.1.2.1)), b.1.2.2⟩, rfl⟩
  shapeRestr := fun {_j j'} _g a ↦ ⟨(j', a.1.2), rfl⟩
  reindex := fun {_j _j'} g a {_i} b ↦
    ⟨⟨b.1.1, (b.1.2.1.trans g.down.down).trans_eq a.2.symm, b.1.2.2⟩, b.2⟩

/-- Each arity has at most one direction at each level. -/
instance directionSubsingleton (a : natData.A) (i : Fin 2) :
    Subsingleton (natData.Direction a i) :=
  ⟨fun x y ↦ Subtype.ext (Subtype.ext (x.2.trans y.2.symm))⟩

/-- Naturality identifies the base child with the index of the total-space child. -/
@[reducible] def natPRA : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := natData
  isFunctorial :=
    { directionRestr_id := by intro a i; funext b; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext b; exact Subsingleton.elim _ _
      shapeRestr_id := by
        intro j; funext a
        exact Subtype.ext (Prod.ext a.2.symm rfl)
      shapeRestr_comp := by intro j j' j'' g h; rfl
      reindex_naturality := by intro j j' g a i i' f; funext b; exact Subsingleton.elim _ _
      reindex_id := by intro j a i b; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i b; exact Subsingleton.elim _ _ }

/-- A base constructor has only base directions. -/
theorem nat_independent : BaseIndependent natPRA := by
  intro a b
  have hb := b.2.1
  have ha := a.2
  change a.1.1 = 0 at ha
  change b.1 = 0
  have hb0 := hb.trans_eq ha
  apply Fin.ext
  change b.1.val = 0
  omega

/-- Zero in the ordinary polynomial W-type. -/
def zero : (basePFunctor natPRA).W :=
  WType.mk ⟨(0, false), rfl⟩ (fun b ↦ Bool.noConfusion b.2.2)

/-- Successor in the ordinary polynomial W-type. -/
def succ (n : (basePFunctor natPRA).W) : (basePFunctor natPRA).W :=
  WType.mk ⟨(0, true), rfl⟩ (fun _ ↦ n)

example : baseWEquiv nat_independent (ofBaseW nat_independent (succ (succ zero))) =
    succ (succ zero) := (baseWEquiv nat_independent).apply_symm_apply _

/-- The total-space leaf node. -/
def totalZeroNode : (natPRA.objPresheaf natPRA.W).obj ⟨1⟩ :=
  ⟨⟨⟨⟨(1, false), fun b ↦ Bool.noConfusion b.2.2⟩,
      funext fun b ↦ Bool.noConfusion b.2.2⟩,
    fun _ _ _ b ↦ Bool.noConfusion b.1.2.2⟩, rfl⟩

/-- The total-space leaf. -/
def totalZero : natPRA.W.obj ⟨1⟩ := W.mk totalZeroNode

/-- Children of a total-space successor, obtained by restricting its recursive child. -/
def totalSuccNode (n : natPRA.W.obj ⟨1⟩) :
    (natPRA.objPresheaf natPRA.W).obj ⟨1⟩ :=
  ⟨⟨⟨⟨(1, true), fun b ↦
      ⟨b.1, natPRA.W.map (homOfLE b.2.1).op n⟩⟩, rfl⟩, by
    intro i i' g b
    obtain ⟨⟨i, hi, hb⟩, rfl⟩ := b
    change natPRA.W.map _ n = natPRA.W.map g.op (natPRA.W.map _ n)
    exact (natPRA.W.map_comp_apply (homOfLE hi).op g.op n)⟩, rfl⟩

/-- The total-space successor. -/
def totalSucc (n : natPRA.W.obj ⟨1⟩) : natPRA.W.obj ⟨1⟩ := W.mk (totalSuccNode n)

/-- Restriction reads the ordinary zero constructor. -/
theorem index_zero : index nat_independent totalZero = zero := by
  change WType.mk _ _ = WType.mk _ _
  congr 1
  funext b
  exact Bool.noConfusion b.2.2

/-- Restriction reads an ordinary successor. -/
theorem index_succ (n : natPRA.W.obj ⟨1⟩) :
    index nat_independent (totalSucc n) = succ (index nat_independent n) := by
  change WType.mk _ _ = WType.mk _ _
  congr 1
  funext b
  have hb : b.1 = 0 := nat_independent ⟨(0, true), rfl⟩ b
  obtain ⟨i, hi⟩ := b
  change i = 0 at hb
  subst i
  rfl

example : index nat_independent (totalSucc (totalSucc totalZero)) = succ (succ zero) := by
  rw [index_succ, index_succ, index_zero]

/-- A dependent element whose type uses the ordinary W constructor. -/
def dependentTwo : DependentW nat_independent (succ (succ zero)) :=
  ⟨totalSucc (totalSucc totalZero), by rw [index_succ, index_succ, index_zero]⟩

example : (totalEquiv nat_independent) ⟨succ (succ zero), dependentTwo⟩ =
    totalSucc (totalSucc totalZero) := by rfl

/-- A constant target presheaf for computing the length of a tree. -/
@[reducible] def natTarget : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := ℕ
  map _ := 𝟙 _

/-- The algebra counts successors, reading the base child at either level. -/
def countAlg : NatTrans (natPRA.objPresheaf natTarget) natTarget where
  app _ := ↾ fun x ↦ if h : x.1.shape.2 = true then
    natPRA.value x.1.1 ⟨⟨0, by change 0 ≤ x.1.shape.1.val; omega, h⟩, rfl⟩ + 1 else 0
  naturality _ _ _ := by ext x; rfl

example : (W.elim natPRA natTarget countAlg).app ⟨1⟩
    (totalSucc (totalSucc totalZero)) = 2 := by decide

open PresheafFixture

/-- The shared fixture has no recursive fields at its base leaves. -/
theorem fixture_independent : BaseIndependent wFixture := by
  rintro ⟨a, ha⟩ b
  cases a with
  | R => exact False.elim ((by decide : (1 : Fin 2) ≠ 0) ha)
  | L1 => exact False.elim ((by decide : (1 : Fin 2) ≠ 0) ha)
  | L0a => exact b.elim0
  | L0b => exact b.elim0

/-- The ordinary W-tree at the base leaf reached by restriction. -/
def baseLeaf : (basePFunctor wFixture).W :=
  WType.mk ⟨.L0a, rfl⟩ (fun b ↦ b.elim0)

/-- An inhabited fibre, supplied by a hereditarily natural branching tree. -/
def inhabitedFibre : DependentW fixture_independent baseLeaf :=
  ⟨ULift.up ⟨goodTree, rfl, by let : wFixture.Finitary := finitaryWFixture; decide⟩, by
    change WType.mk _ _ = WType.mk _ _
    congr 1
    funext b
    exact b.elim0⟩

/-- The other base leaf is not the restriction of any total-space tree. -/
theorem empty_fibre (t : DependentW fixture_independent
    (WType.mk (β := (basePFunctor wFixture).B) ⟨.L0b, rfl⟩ (fun b ↦ b.elim0))) : False := by
  have ht := congrArg PFunctor.W.head t.2
  obtain ⟨⟨⟨⟨w, hw⟩, hq, hn⟩⟩, he⟩ := t
  cases w with
  | mk a f =>
    cases a with
    | R => exact Shp.noConfusion (congrArg Subtype.val ht)
    | L1 => exact Shp.noConfusion (congrArg Subtype.val ht)
    | L0a => exact (by decide : (0 : Fin 2) ≠ 1) hq
    | L0b => exact (by decide : (0 : Fin 2) ≠ 1) hq

end WalkingArrowTests
