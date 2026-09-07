/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.RelSeparation

/-!
# Tests for what separating a proof-relevant relation costs

An instance where the family of witnesses the dependent-product relation asks
for is constructible, so that the direction the choice principle supplies is
seen to be the only obstruction and not an artifact of the statement.

## Tags

prototype, parametricity, relation, separation, proof relevance
-/

open GebProto.RelSeparation

/-! ## A relation whose witnesses are computed rather than chosen -/

/-- The indices are related when equal. -/
def diagRel (a a' : Bool) : Type := PLift (a = a')

/-- The values are related when equal. -/
def valRel (a a' : Bool) (_ : diagRel a a') (n n' : Nat) : Type := PLift (n = n')

/-- A family over the indices. -/
def flag : Bool → Nat := fun b ↦ cond b 1 0

/-- The family of witnesses, built from the index witness rather than chosen, so
the dependent-product relation is inhabited outright. -/
def flagWitness : PiRel diagRel valRel flag flag :=
  fun _ _ r ↦ ⟨congrArg flag r.down⟩

example : PiSep diagRel valRel flag flag :=
  sep_piRel diagRel valRel flag flag ⟨flagWitness⟩

/-! ## The dependent-sum former commutes -/

example (p p' : Σ _ : Bool, Nat) :
    Sep (SigmaRel diagRel valRel) p p' ↔
      ∃ r : diagRel p.1 p'.1, Sep (valRel p.1 p'.1 r) p.2 p'.2 :=
  sep_sigmaRel_iff diagRel valRel p p'
