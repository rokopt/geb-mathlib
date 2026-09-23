/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Init
public import Geb.Cslib.Foundations.Data.PFunctor.Free -- shake: keep

public meta import Geb.Cslib.Foundations.Data.PFunctor.Free -- shake: keep

/-!
# Tests for the executable recursor of the free monad

A function defined by `PFunctor.FreeM.rec` whose result type depends on the term, the variable
at a leaf of a term, is evaluated.

## Tags

free monad, recursor, code generation
-/

@[expose] public section

namespace FreeMRecTests

open PFunctor

/-- Binary branching. -/
abbrev binary : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Bool⟩

/-- The variable leaves of a term: at a variable, one leaf; at an operation, a direction
followed by a leaf of that child. -/
def Leaf {α : Type} (t : binary.FreeM α) : Type :=
  FreeM.rec (fun _ ↦ Unit) (fun _ _ ls ↦ (b : Bool) × ls b) t

/-- The variable at a leaf. -/
def Leaf.var {α : Type} : (t : binary.FreeM α) → Leaf t → α :=
  FreeM.rec (motive := fun t ↦ Leaf t → α) (fun x _ ↦ x) fun _ _ var l ↦ var l.1 l.2

/-- A node over the variables one and two. -/
def pair : binary.FreeM ℕ := .liftBind () fun b ↦ Bool.rec (.pure 1) (.pure 2) b

#guard Leaf.var pair ⟨false, ()⟩ = 1
#guard Leaf.var pair ⟨true, ()⟩ = 2

end FreeMRecTests

end
