/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Kmett
public meta import Geb.Prototypes.PHOAS.Kmett -- shake: keep
public import Mathlib.CategoryTheory.Category.Init

set_option doc.verso true in
/-!
# PHOAS examples and scoped unfolding

Executable folds of the closed identity and Kmett's nested abstraction, and execution of
the scoped destructor through its dependent child extraction.

## Tags

PHOAS, free monad, scoped syntax
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.PHOAS

open Geb.PHOAS Geb.PHOAS.PProfunctor

#guard End.iter Kmett.countAlgebra Kmett.identity = 1
#guard End.iter Kmett.countAlgebra Kmett.exampleTerm = 3

#guard match Kmett.closedUnfold Kmett.exampleTerm with
  | .inl _ => false
  | .inr body => Free.fold id Kmett.countAlgebra (body.val ℕ (fun _ ↦ 0)) == 2

#guard match Kmett.closedUnfold Kmett.exampleTerm with
  | .inl _ => false
  | .inr body => match Scoped.unfold Kmett.signature PUnit body with
    | .inr ⟨true, k⟩ =>
      Free.fold id Kmett.countAlgebra
        ((k PUnit.unit).val ℕ (Sum.elim (fun _ ↦ 4) (fun _ ↦ 5))) == 10
    | _ => false

/-- The obstruction specializes to a small concrete carrier. -/
theorem no_bool_fixed_point : ¬Nonempty (Kmett.signature.Obj Bool Bool ≃ Bool) :=
  Kmett.no_fixed_point Bool

end GebTests.PHOAS
