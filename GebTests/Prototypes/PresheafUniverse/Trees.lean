/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.W
import Geb.Prototypes.PresheafUniverse.Trees

/-!
# Tests for the codes and terms of the prototype universe

Concrete codes and terms of the universe endofunctor on presheaves over the
walking arrow, with their fiber membership decided by
`FinitePresheafPFunctor.memWBool` and their types computed by the presheaf
restriction. The tests exhibit the correspondence the prototype is for:
membership of a term tree in the carrier presheaf's fiber is well-typedness,
and the presheaf restriction along the walking arrow's non-identity morphism is
the typing map.

## Tags

prototype, presheaf, universe, W-type, walking arrow, reduction test
-/

set_option linter.privateModule false

open CategoryTheory GebProto.PresheafUniverse

/-! ## Codes and terms -/

/-- The base type's code. -/
def natCode : Tree := baseCode

/-- The `sigma` code of the base type with itself. -/
def baseSqCode : Tree := sigmaCode baseCode baseCode rfl rfl

/-- The `pi` code of the base type with itself. -/
def baseFunCode : Tree := piCode baseCode baseCode rfl rfl

/-- The base type's two terms. -/
def trueTerm : Tree := litTerm true

/-- The base type's other term. -/
def falseTerm : Tree := litTerm false

/-- A pair of two base-type terms. -/
def pairTT : Tree := pairTerm trueTerm falseTerm rfl rfl

/-- A pair whose first component is itself a pair. -/
def pairNested : Tree := pairTerm pairTT trueTerm rfl rfl

/-- A pair node whose code directions do not carry its components' types: the
first code direction is the `sigma` code where the base code is required. -/
def pairIllTyped : Tree :=
  node .pair
    (fun d ↦ match d with
      | .tm false => trueTerm
      | .tm true => falseTerm
      | .ty false => baseSqCode
      | .ty true => baseCode)
    (fun d ↦ match d with
      | .tm false => rfl
      | .tm true => rfl
      | .ty false => rfl
      | .ty true => rfl)

/-! ## Fiber membership

Membership in the carrier presheaf's fiber conjoins admissibility, the index
test, and hereditary naturality; for a term tree the last is well-typedness. -/

/-- The base code lies in the fiber over the code object. -/
def memBaseCode : Bool := finiteUniverse.memWBool 0 natCode.1

/-- The `sigma` code lies in the fiber over the code object. -/
def memBaseSqCode : Bool := finiteUniverse.memWBool 0 baseSqCode.1

/-- The `pi` code lies in the fiber over the code object. -/
def memBaseFunCode : Bool := finiteUniverse.memWBool 0 baseFunCode.1

/-- A literal lies in the fiber over the term object. -/
def memTrueTerm : Bool := finiteUniverse.memWBool 1 trueTerm.1

/-- A well-typed pair lies in the fiber over the term object. -/
def memPairTT : Bool := finiteUniverse.memWBool 1 pairTT.1

/-- A well-typed nested pair lies in the fiber over the term object. -/
def memPairNested : Bool := finiteUniverse.memWBool 1 pairNested.1

/-- A term tree does not lie in the fiber over the code object. -/
def memPairTTAtCode : Bool := finiteUniverse.memWBool 0 pairTT.1

/-- The ill-typed pair is admissible and indexed at the term object, but fails
hereditary naturality. -/
def memPairIllTyped : Bool := finiteUniverse.memWBool 1 pairIllTyped.1

example : memBaseCode = true := by decide
example : memBaseSqCode = true := by decide
example : memBaseFunCode = true := by decide
example : memTrueTerm = true := by decide
example : memPairTT = true := by decide
set_option maxHeartbeats 2000000 in
-- The naturality fold compares a root-restriction with a sibling subtree at
-- every node, direction, and hom of the base category, so its cost compounds
-- with the depth of the tree; the nested pair exceeds the default limit.
example : memPairNested = true := by decide
example : memPairTTAtCode = false := by decide
example : memPairIllTyped = false := by decide

/-! ## The typing map

The presheaf restriction of a term tree along the walking arrow's non-identity
morphism is its type. -/

/-- The type of a literal is the base code. -/
def typeTrueTermIsBase : Bool :=
  @decide _ (finiteUniverse.decidableEqW (typeOf trueTerm rfl).1 natCode.1)

/-- The type of a pair of base-type terms is the `sigma` code of the base type
with itself. -/
def typePairTT : Bool :=
  @decide _ (finiteUniverse.decidableEqW (typeOf pairTT rfl).1 baseSqCode.1)

/-- The type of the nested pair is the `sigma` code of the inner pair's type
with the base code. -/
def typePairNested : Bool :=
  @decide _ (finiteUniverse.decidableEqW (typeOf pairNested rfl).1
    (sigmaCode baseSqCode baseCode rfl rfl).1)

/-- The type of a pair is not the base code: the typing map is not constant. -/
def typePairTTNotBase : Bool :=
  @decide _ (finiteUniverse.decidableEqW (typeOf pairTT rfl).1 natCode.1)

example : typeTrueTermIsBase = true := by decide
example : typePairTT = true := by decide
example : typePairNested = true := by decide
example : typePairTTNotBase = false := by decide

/-! ## The carrier presheaf

The same computation read off the carrier presheaf `PresheafPFunctor.W`, whose
restriction map is the typing map on the fibers. -/

/-- The well-typed pair is hereditarily natural. -/
theorem isHereditarilyNatural_pairTT : universeFunctor.IsHereditarilyNatural pairTT :=
  @of_decide_eq_true _
    (FinitePresheafPFunctor.decidableIsHereditarilyNatural finiteUniverse pairTT) rfl

/-- The pair as an element of the carrier presheaf's fiber over the term
object. -/
def pairTTElt : (universeFunctor.W).obj ⟨(1 : Fin 2)⟩ :=
  ULift.up ⟨pairTT, rfl, isHereditarilyNatural_pairTT⟩

/-- The carrier presheaf's restriction map sends the pair to the `sigma` code of
its components' types. -/
def restrPairTTElt : Bool :=
  @decide _ (finiteUniverse.decidableEqW
    (((universeFunctor.W).map arrowHom.op pairTTElt).down.1.1) baseSqCode.1)

example : restrPairTTElt = true := by decide
