/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream -- shake: keep
public import Geb.Prototypes.Definition.Basic -- shake: keep

public meta import Geb.Prototypes.BitStream -- shake: keep
public meta import Geb.Prototypes.Definition.Basic -- shake: keep

set_option doc.verso true in
/-!
# Examples of definitions and structural references

An export tree supplies typed directions to an equation block. Linking, derived operations,
rose-tree encoding, and a finitely presented infinite stream are executable examples.
An unguarded alias equation admits every interpretation, demonstrating why a block's
syntax alone does not assert uniqueness.

## Main definitions

* {lit}`layout` supplies two export directions.
* {lit}`equations` imports a value and exports it alongside its double.
* {lit}`alternating` is a finite coalgebra presenting an infinite bitstream.

## Main statements

* {lit}`values_solution` verifies the interpretation of the example block.
* {lit}`alias_not_unique` shows that an alias equation permits every interpretation.

## Tags

definition, substitution, structural direction, bitstream, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Tests

open PFunctor
open scoped FinEnum

/-- A binary branching interface, independent of the program's operation signature. -/
abbrev layoutSig : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Fin 2⟩

/-- An interface with two variable leaves. -/
def layout : layoutSig.FreeM Unit := .liftBind () fun _ ↦ .pure ()

/-- The first structural direction. -/
def first : Direction layout := ⟨0, ()⟩

/-- The second structural direction. -/
def second : Direction layout := ⟨1, ()⟩

/-- A deeper interface exhibits dependent sequences of directions. -/
def nestedLayout : layoutSig.FreeM Unit := .liftBind () fun _ ↦ layout

/-- Select the second child, then the first child, then its variable leaf. -/
def nestedDirection : Direction nestedLayout := ⟨1, ⟨0, ()⟩⟩

/-- Zero and addition, with no general-recursion operator. -/
abbrev arithmetic : PFunctor.{0, 0} := ⟨Bool, fun b ↦ Fin (cond b 2 0)⟩

/-- A binary addition term. -/
def add {X : Type} (x y : arithmetic.FreeM X) : arithmetic.FreeM X :=
  .liftBind true fun i ↦ Fin.cases x (fun _ ↦ y) i

/-- The natural-number interpretation of zero and addition. -/
def arithmeticAlg (x : arithmetic.Obj ℕ) : ℕ :=
  match x with
  | ⟨false, _⟩ => 0
  | ⟨true, f⟩ => f (0 : Fin 2) + f (1 : Fin 2)

/-- The first export imports a value; the second uses the first export twice. -/
def equations : Block arithmetic Unit (Direction layout) := fun i ↦
  Fin.cases (.pure (.inl ()))
    (fun _ ↦ add (.pure (.inr first)) (.pure (.inr first))) i.1

/-- The definition selected at the second export, with its local dependency retained. -/
def doubled : Presented arithmetic layoutSig Unit := ⟨layout, equations, second⟩

/-- The interpretation satisfying the equations for an import of seven. -/
def values (i : Direction layout) : ℕ := Fin.cases 7 (fun _ ↦ 14) i.1

/-- The example environment solves the block. -/
theorem values_solution : IsSolution arithmeticAlg (fun _ ↦ 7) equations values := by
  intro ⟨i, ()⟩
  refine Fin.cases rfl (fun j ↦ ?_) i
  have hj : j = 0 := Fin.eq_zero j
  subst j
  rfl

/-- A unary operation defined by duplicating its argument. -/
def double : Derived arithmetic ⟨Unit, fun _ ↦ Fin 1⟩ :=
  fun _ ↦ add (.pure 0) (.pure 0)

/-- The equation consisting only of a local reference imposes no constraint. -/
theorem alias_not_unique (alg : arithmetic.Obj ℕ → ℕ) (v : Unit → ℕ) :
    IsSolution alg Empty.elim (fun _ ↦ .pure (.inr ())) v := fun _ ↦ rfl

/-- A two-state bitstream coalgebra emits the state and switches it. -/
def alternating (b : Bool) : BitStream.sig.Obj Bool := .mk (some b) fun _ ↦ !b

-- References retain their direction structure rather than a computed natural-number axis.
#guard nestedDirection.1.val = 1
#guard nestedDirection.2.1.val = 0
#guard eval arithmeticAlg (Sum.elim (fun _ ↦ 7) (fun _ ↦ 0))
  (unfoldEntry doubled 1) = 14
#guard eval arithmeticAlg (fun _ : Unit ↦ 8)
  (expandOps double (.liftBind () fun _ ↦ .pure ())) = 16
#guard BitTree.Elias.validBool (RoseTree.wire
  (encode (fun b ↦ cond b 1 0) (fun _ : Unit ↦ 0) (add (.pure ()) (.pure ())))) = true
#guard (BitStream.seqEquiv (M.corec alternating false)).take 6 =
  [false, true, false, true, false, true]

end Geb.Definition.Tests

end
