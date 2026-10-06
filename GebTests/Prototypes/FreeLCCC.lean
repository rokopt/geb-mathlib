/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeLCCC -- shake: keep
public meta import Geb.Prototypes.FreeLCCC -- shake: keep

set_option doc.verso true in
/-!
# Experiments with the locally cartesian closed presentation

The NNO uniqueness equation becomes equality of quotient arrows. Substitution in the
dependent-product beta rule is checked at a composite indexing arrow. An application of the
dependent-product formation rule with an incorrect domain equation is rejected.

## Main definitions

* {lit}`compositeBeta` — beta with a composite indexing arrow.

## Tags

locally cartesian closed category, proof certificate, quotient, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeLCCC

open Geb.PartialHorn Geb.FreeLCCC Geb.FreeTopos.Sorts
open Geb.FreeLCCC.Examples

-- Every hypothesis, as well as every conclusion, equates terms of one sort.
#guard axioms.all fun a ↦ a.Scoped && (a.concl :: a.hyps).all fun q ↦
  (sortOf sig a.ctx q.lhs).isSome && (sortOf sig a.ctx q.lhs == sortOf sig a.ctx q.rhs)

example : ofTerm (s := arr) (idt nat) (by decide) nat_id_rec.left =
    ofTerm (natRec zeroN succ) (by decide) nat_id_rec.right :=
  (ofTerm_eq_iff _ _ _ _).mpr nat_id_rec

-- A defined dependent product is an arrow, whose domain is an object.
#guard sortOf sig [] productAlongZero = some arr
#guard sortOf sig [] (dom productAlongZero) = some obj

/-- Beta at a composite indexing arrow, with its composability and lambda formation assumed. -/
def compositeBeta : Tree :=
  Cert.ax (finiteAxioms.length + natAxioms.length + 17)
    [comp (x 0) (x 1), x 2, x 3, x 4]
    [Cert.ax 4 [x 0, x 1] [Cert.refl 0, Cert.refl 1] [Cert.hyp 0],
      Cert.refl 2, Cert.refl 3, Cert.refl 4]
    [Cert.hyp 1]

#guard check theory #[] compositeBeta [arr, arr, arr, arr, arr]
    [⟨cod (x 1), dom (x 0)⟩, dfd (piLam (comp (x 0) (x 1)) (x 2) (x 3) (x 4))] =
  some ⟨comp (piEval (comp (x 0) (x 1)) (x 2))
    (baseChangeMap (comp (x 0) (x 1)) (x 3) (pi (comp (x 0) (x 1)) (x 2))
      (piLam (comp (x 0) (x 1)) (x 2) (x 3) (x 4))), x 4⟩

-- The codomain of the second argument must equal the domain of the indexing arrow.
#guard check theory #[]
    (Cert.ax (finiteAxioms.length + natAxioms.length) [x 0, x 1]
      [Cert.refl 0, Cert.refl 1] [Cert.hyp 0]) [arr, arr]
    [⟨cod (x 1), cod (x 0)⟩] = none

-- An object cannot be used as the indexing arrow, even with a stated domain equation.
#guard check theory #[]
    (Cert.ax (finiteAxioms.length + natAxioms.length) [x 0, x 1]
      [Cert.refl 0, Cert.refl 1] [Cert.hyp 0]) [obj, arr]
    [⟨cod (x 1), dom (x 0)⟩] = none

end GebTests.Prototypes.FreeLCCC

end
