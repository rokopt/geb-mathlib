/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Internal -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Internal -- shake: keep

set_option doc.verso true in
/-!
# The computational core's theorems, derived in the internal language

The theorems of {lit}`bootstrap/proofs/prelude.geb` and {lit}`bootstrap/proofs/nat.geb` about
appending and addition, defined in the internal language, proved by derivations of the language
that its own checker checks: by unfolding the definitions and normalizing, by induction on a list
or a number with the step of its recursion, and by rewriting with an earlier theorem.

## Main definitions

* {lit}`theorems` — the theorems, each with its proof.
* {lit}`development` — the development of their derivations.

## Tags

internal language, derivation, benchmark, lists, natural numbers
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalDerivation

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv NormRule Rule byNorm byNatInd byListInd checkThms)

/-- The language's equations the normalizer applies: β, the components of pairs, and the
computation of the folds of the natural numbers and of lists, at the primitives zero, the
successor, the empty list and construction. -/
def eqns : List NormRule := [.rule .beta, .rule .fstPair, .rule .sndPair, .rule (.natZero 2),
  .rule (.natSucc 3), .rule (.listNil 0), .rule (.listCons 1)]

/-- The construction of the element before the recursion's value, the step of the list
inductions. -/
def consStep : Term := consT (Term.var 1) (Term.var 0)

/-- The theorems, each with the proof of its equation from the theorems before it. -/
def theorems : List (Thm × (Array Thm → Option Deriv)) := [
  (⟨1, [L], appendT nilT (Term.var 0), Term.var 0⟩,
    fun E ↦ byNorm G E 1 (eqns ++ [.delta 0]) 64 [L] (appendT nilT (Term.var 0)) (Term.var 0)),
  (⟨1, [L], appendT (Term.var 0) nilT, Term.var 0⟩,
    fun E ↦ byListInd G E 1 0 1 consStep (eqns ++ [.delta 0]) 64 [L]
      (appendT (Term.var 0) nilT) (Term.var 0)),
  (⟨1, [L, L, L], appendT (appendT (Term.var 0) (Term.var 1)) (Term.var 2),
      appendT (Term.var 0) (appendT (Term.var 1) (Term.var 2))⟩,
    fun E ↦ byListInd G E 1 0 1 consStep (eqns ++ [.delta 0]) 64 [L, L, L]
      (appendT (appendT (Term.var 0) (Term.var 1)) (Term.var 2))
      (appendT (Term.var 0) (appendT (Term.var 1) (Term.var 2)))),
  (⟨1, [L], appendT (appendT (Term.var 0) nilT) nilT, Term.var 0⟩,
    fun E ↦ byNorm G E 1 (eqns ++ [.thm 1 [A]]) 64 [L]
      (appendT (appendT (Term.var 0) nilT) nilT) (Term.var 0)),
  (⟨0, [nat], addT (Term.var 0) zeroT, Term.var 0⟩,
    fun E ↦ byNorm G E 0 (eqns ++ [.delta 1]) 64 [nat] (addT (Term.var 0) zeroT) (Term.var 0)),
  (⟨0, [nat, nat], addT (Term.var 1) (succT (Term.var 0)),
      succT (addT (Term.var 1) (Term.var 0))⟩,
    fun E ↦ byNorm G E 0 (eqns ++ [.delta 1]) 64 [nat, nat]
      (addT (Term.var 1) (succT (Term.var 0))) (succT (addT (Term.var 1) (Term.var 0)))),
  (⟨0, [nat], addT zeroT (Term.var 0), Term.var 0⟩,
    fun E ↦ byNatInd G E 0 2 3 (succT (Term.var 0)) (eqns ++ [.delta 1]) 64 [nat]
      (addT zeroT (Term.var 0)) (Term.var 0))]

/-- The development: each theorem with the derivation the prover computes from those before
it. -/
def development : Option (List (Thm × Deriv)) :=
  (theorems.foldl (fun acc (a, p) ↦ acc.bind fun (E, ds) ↦
    (p E).map fun d ↦ (E.push a, ds ++ [(a, d)])) (some (#[], []))).map Prod.snd

-- every theorem is proved, and the development checks
#guard development.any fun ds ↦ ds.length == 7 && checkThms G ds #[]

end GebTests.Prototypes.FreeTopos.InternalDerivation

end
