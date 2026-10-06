/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Kmett
public meta import Geb.Prototypes.PHOAS.Kmett -- shake: keep
public import Geb.Prototypes.PHOAS.Initial
public meta import Geb.Prototypes.PHOAS.Initial -- shake: keep
public import Mathlib.CategoryTheory.Category.Init

set_option doc.verso true in
/-!
# PHOAS examples and scoped unfolding

Executable folds of the closed identity and Kmett's nested abstraction, and execution of
the scoped destructor through its dependent child extraction. The initial-algebra fold
counts nodes and extracts free variables while removing each binder's fresh variable.

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

/-- Count operation nodes by the scoped initial-algebra fold. -/
def scopedCount {Γ : Type} (t : Kmett.signature.Scoped.{0, 0, 0, 0, 0} Γ) : ℕ :=
  Scoped.fold (P := Kmett.signature) (fun _ _ ↦ 0) (fun _ a ↦ match a with
    | false => fun k ↦ k false + k true + 1
    | true => fun k ↦ k PUnit.unit + 1) t

/-- Extract free-variable occurrences, discarding the variables introduced by each binder. -/
def freeVars {Γ : Type} (t : Kmett.signature.Scoped.{0, 0, 0, 0, 0} Γ) : List Γ :=
  Scoped.fold (P := Kmett.signature) (M := List) (fun _ x ↦ [x]) (fun _ a ↦ match a with
    | false => fun k ↦
      (k false).map (Sum.elim id PEmpty.elim) ++ (k true).map (Sum.elim id PEmpty.elim)
    | true => fun k ↦ (k PUnit.unit).filterMap (Sum.elim some (fun _ ↦ none))) t

#guard scopedCount (Scoped.emptyEquivEnd.symm Kmett.identity) == 1
#guard scopedCount (Scoped.emptyEquivEnd.symm Kmett.exampleTerm) == 3
#guard (freeVars (Scoped.emptyEquivEnd.symm Kmett.exampleTerm)).isEmpty

#guard match Kmett.closedUnfold Kmett.exampleTerm with
  | .inl _ => false
  | .inr body => freeVars (Scoped.rename (fun _ ↦ 7) body) == [7]

end GebTests.PHOAS
