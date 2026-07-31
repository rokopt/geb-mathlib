/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Basic

/-!
# Tests for `FinCat`

Four specifications, each discharging its associativity field by `rfl`:
the terminal category, the two-element monoid on an idempotent, the
walking arrow, and the walking isomorphism. The last of these is the
one whose client composition returns a value outside the client's own
index range. A fifth, non-associative, specification exhibits the
check rejecting.

The counts and the identity laws are asserted at named object indices:
a projection is not a numeral, so `Fin` indices of a specification are
not written as literals.

## Tags

category, finite category, decidable, constructive
-/

@[expose] public section

/-- The terminal category: one object, no non-identity morphisms. -/
def terminalCat : FinCat where
  objCount := 1
  nonIdCount := fun _ _ ↦ 0
  comp := fun _ _ _ f _ ↦ f.elim0
  assoc := rfl

/-- The two-element monoid on an idempotent: one object, one
non-identity morphism composing with itself to itself. -/
def idemMonoid : FinCat where
  objCount := 1
  nonIdCount := fun _ _ ↦ 1
  comp := fun _ _ _ _ _ ↦ ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)⟩
  assoc := rfl

/-- The non-identity count of the walking arrow. -/
def arrowCount (i j : Fin 2) : Nat := if i.val < j.val then 1 else 0

/-- Composition in the walking arrow. No pair of client morphisms is
composable, so every branch eliminates whichever argument inhabits
`Fin 0`; the index triples are enumerated because the conditional in
`arrowCount` does not reduce at a variable index. -/
def arrowComp : (i j k : Fin 2) → Fin (arrowCount i j) → Fin (arrowCount j k) →
    Fin (FinCat.homCountOf 2 arrowCount i k)
  | 0, 0, _, f, _ => f.elim0
  | 0, 1, 0, _, g => g.elim0
  | 0, 1, 1, _, g => g.elim0
  | 1, 0, _, f, _ => f.elim0
  | 1, 1, _, f, _ => f.elim0

/-- The walking arrow: two objects, one non-identity morphism. -/
def walkingArrow : FinCat where
  objCount := 2
  nonIdCount := arrowCount
  comp := arrowComp
  assoc := rfl

/-- The non-identity count of the walking isomorphism. -/
def isoCount (i j : Fin 2) : Nat := if i.val = j.val then 0 else 1

/-- Composition in the walking isomorphism. Each composable pair
returns the reserved identity of its common endpoint, at index
`isoCount i i = 0`. -/
def isoComp : (i j k : Fin 2) → Fin (isoCount i j) → Fin (isoCount j k) →
    Fin (FinCat.homCountOf 2 isoCount i k)
  | 0, 0, _, f, _ => f.elim0
  | 0, 1, 0, _, _ => ⟨0, by decide⟩
  | 0, 1, 1, _, g => g.elim0
  | 1, 0, 0, _, g => g.elim0
  | 1, 0, 1, _, _ => ⟨0, by decide⟩
  | 1, 1, _, f, _ => f.elim0

/-- The walking isomorphism: two objects, one non-identity morphism
each way, each composite an identity. This is the regression test for a
client-supplied composition returning a value outside the client's own
index range. -/
def walkingIso : FinCat where
  objCount := 2
  nonIdCount := isoCount
  comp := isoComp
  assoc := rfl

/-- The non-identity count of the non-associative specification: one
morphism at every index pair. -/
def badCount : Fin 2 → Fin 2 → Nat := fun _ _ ↦ 1

/-- A composition that is not associative: each pair composes to the
reserved identity exactly when its endpoints agree. -/
def badComp : (i j k : Fin 2) → Fin (badCount i j) → Fin (badCount j k) →
    Fin (FinCat.homCountOf 2 badCount i k)
  | 0, _, 0, _, _ => ⟨1, by decide⟩
  | 0, _, 1, _, _ => ⟨0, by decide⟩
  | 1, _, 0, _, _ => ⟨0, by decide⟩
  | 1, _, 1, _, _ => ⟨1, by decide⟩

/-- The checker rejects as well as accepts. The witness is `f : 0 ⟶ 0`,
`g : 0 ⟶ 1`, `h : 1 ⟶ 0`, where the left association is the reserved
identity of `0` and the right association is `f`. -/
theorem badComp_assocCheck_eq_false :
    FinCat.assocCheckOf 2 badCount badComp = false := rfl

/-- The source index of `walkingArrow`. -/
def arrowSrc : Fin walkingArrow.objCount := ⟨0, by decide⟩

/-- The target index of `walkingArrow`. -/
def arrowTgt : Fin walkingArrow.objCount := ⟨1, by decide⟩

/-- Off the diagonal the hom-count is the client's count. -/
theorem arrow_homCount_offDiag : walkingArrow.homCount arrowSrc arrowTgt = 1 := rfl

/-- The reverse hom-set is empty: the walking arrow has one arrow. -/
theorem arrow_homCount_rev : walkingArrow.homCount arrowTgt arrowSrc = 0 := rfl

/-- On the diagonal the client's count is zero. -/
theorem arrow_nonIdCount_diag : walkingArrow.nonIdCount arrowSrc arrowSrc = 0 := rfl

/-- On the diagonal the hom-count exceeds it by the reserved
identity. -/
theorem arrow_homCount_diag : walkingArrow.homCount arrowSrc arrowSrc = 1 := rfl

/-- `walkingArrow`'s one non-identity morphism. -/
def arrowMor : walkingArrow.Mor arrowSrc arrowTgt := ⟨0, by decide⟩

/-- The first object index of `walkingIso`. -/
def isoSrcIdx : Fin walkingIso.objCount := ⟨0, by decide⟩

/-- The second. -/
def isoTgtIdx : Fin walkingIso.objCount := ⟨1, by decide⟩

/-- The forward non-identity morphism of `walkingIso`. -/
def isoFwdMor : walkingIso.Mor isoSrcIdx isoTgtIdx := ⟨0, by decide⟩

/-- The backward one. -/
def isoBwdMor : walkingIso.Mor isoTgtIdx isoSrcIdx := ⟨0, by decide⟩

/-- The unique object of `terminalCat`. -/
def termObj : Fin terminalCat.objCount := ⟨0, by decide⟩

/-- The unique object of `idemMonoid`. -/
def idemObj : Fin idemMonoid.objCount := ⟨0, by decide⟩

/-- The idempotent, at the client index. -/
def idemMor : idemMonoid.Mor idemObj idemObj := ⟨0, by decide⟩

/-- The reserved identity of `idemMonoid`, one past the client's
range. -/
def idemIdMor : idemMonoid.Mor idemObj idemObj := ⟨1, by decide⟩

/-- The bundled checker agrees with the field. -/
theorem walkingIso_assocCheck : walkingIso.assocCheck = true := rfl

/-- The two non-identity morphisms compose to the reserved identity:
the case where a client composite leaves the client's index range. -/
theorem iso_fwd_comp_bwd :
    walkingIso.compTotal isoFwdMor isoBwdMor = walkingIso.id isoSrcIdx := rfl

/-- The idempotent composes with itself to itself, inside the client
range. -/
theorem idem_mor_comp_self : idemMonoid.compTotal idemMor idemMor = idemMor := rfl

/-- The reserved identity is not the idempotent. -/
theorem idem_mor_ne_id : idemMor ≠ idemIdMor := by decide

/-- The reserved identities compose away on either side of a
morphism. -/
theorem iso_id_comp_fwd_comp_id :
    walkingIso.compTotal (walkingIso.id isoSrcIdx)
        (walkingIso.compTotal isoFwdMor (walkingIso.id isoTgtIdx)) = isoFwdMor := by
  rw [walkingIso.comp_id, walkingIso.id_comp]
