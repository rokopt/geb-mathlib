/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep

set_option doc.verso true in
/-!
# The prover for the theory of an elementary topos

The axioms give every operation a rule of definedness, and every operation whose result is an
arrow rules for its domain and codomain. The library's development, whose derived equations the
prover proves, checks. A projection after a pairing normalizes to its component, with a
certificate the checker accepts.

## Main definitions

* {lit}`fstPair` — a projection after a pairing, and its normalization.

## Tags

elementary topos, prover, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Prover

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts

-- every operation has a rule of definedness
#guard (List.range sig.length).all fun k ↦ (dfdRules[k]?).join.isSome

-- every operation whose result is an arrow has rules for its domain and codomain
#guard (List.range sig.length).all fun k ↦
  sig[k]?.map Prod.snd != some arr || ((domRules[k]?).join.isSome && (codRules[k]?).join.isSome)

-- the library's development checks
#guard library.any fun (_, d) ↦ checkDevelopment theory d

/-- The first projection after the pairing of two arrows of one domain, the second arrow the
first projection of a product. -/
def fstPair : Seq :=
  ⟨[arr, obj, obj], [⟨dom (x 0), prod (x 1) (x 2)⟩],
    ⟨comp (fst (cod (x 0)) (x 1)) (pair (x 0) (fst (x 1) (x 2))), x 0⟩⟩

-- a projection after a pairing normalizes to its component, and the development checks
#guard library.any fun (i, d) ↦
  ((proveSeq fstPair (byNorm (rules i) fstPair.concl)).run d).any fun (_, d) ↦
    checkDevelopment theory d

end GebTests.Prototypes.FreeTopos.Prover

end
