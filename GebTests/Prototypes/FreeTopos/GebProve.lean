/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Encode
public import GebTests.Prototypes.FreeTopos.GebCheckInternal
public meta import GebTests.Prototypes.FreeTopos.GebCheckInternal -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalLogic
public meta import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep

set_option doc.verso true in
/-!
# The prover written in Geb, compared with Lean's

The prover of the internal language written in the datatype language,
{lit}`bootstrap/free-topos/prove.geb`, is read by the stage-0 compiler's front end with the
metalogic's checker and loaded by the kernel, and compared with the Lean prover it transcribes
({name}`Geb.FreeTopos.Internal.byNorm` and the provers beside it) at the proofs of the test
modules of the internal language's derivations and logic, each in the state of the development
before it. Inputs are encoded as the Geb program represents them, by the encodings of
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Encode`.

## Main definitions

* {lit}`proverProgram` — the metalogic's checker with the prover.
* {lit}`plain` — rules of the normalizer, each unprepared.

## Tags

internal language, prover, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebProve

open Geb Geb.PartialHorn Geb.FreeTopos GebTests.Prototypes.FreeTopos.GebCheck
  GebTests.Prototypes.FreeTopos.Agreement.Encode
open Internal (Term Entry NormRule)

/-- The prover. -/
def proveGeb : String := include_str "../../../bootstrap/free-topos/prove.geb"

/-- The program: the metalogic's checker and the prover. -/
def proverProgram : String := GebCheckInternal.internalProgram ++ proveGeb ++ "\n"

/-- The type of a matching of a pattern. -/
abbrev tyMt : Tree := arrow tyT (arrow tyT (arrow tyTs tyT))

/-- The type of lists of rules of the normalizer with their matchings. -/
abbrev tyNRs : Tree := Kernel.tList (Kernel.tProd tyT tyMt)

/-- Rules of the normalizer, each unprepared, with no matching. -/
def plain (rs : List NormRule) : List (Tree × (Tree → Tree → List Tree → Tree)) :=
  rs.map fun r ↦ (encRule r, fun _ _ _ ↦ Kernel.leaf 0)

/-- The entries of the first {lit}`k` theorems of a list. -/
def entries {α : Type} (ts : List (Internal.Thm × α)) (k : ℕ) : Array Entry :=
  ((ts.take k).map fun (a, _) ↦ Entry.language a).toArray

/-- A proof of an equation in a context under hypotheses by one of the provers, with the
prover's arguments. -/
inductive Call where
  /-- By normalization, innermost first or reached through weak head normal forms. -/
  | norm (weak : Bool) (n : ℕ) (rs : List NormRule) (fuel : ℕ)
  /-- By induction on a natural number variable with a step. -/
  | natInd (n kz ks : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ)
  /-- By induction on a list variable with a step. -/
  | listInd (n kn kc : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ)
  /-- By induction on a natural number variable with the induction hypothesis. -/
  | natIndHyp (n kz ks : ℕ) (rs : List NormRule) (fuel : ℕ)
  /-- By induction on a list variable with the induction hypothesis. -/
  | listIndHyp (n kn kc : ℕ) (rs : List NormRule) (fuel : ℕ)

/-- The Lean prover's proof. -/
def Call.lean (G : Internal.Globals) (E : Array Entry) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Call → Option Internal.Deriv
  | .norm w n rs fuel => (if w then Internal.byNormW else Internal.byNorm) G E n rs fuel Γ Φ t u
  | .natInd n kz ks s rs fuel => Internal.byNatInd G E n kz ks s rs fuel Γ Φ t u
  | .listInd n kn kc s rs fuel => Internal.byListInd G E n kn kc s rs fuel Γ Φ t u
  | .natIndHyp n kz ks rs fuel => Internal.byNatIndHyp G E n kz ks rs fuel Γ Φ t u
  | .listIndHyp n kn kc rs fuel => Internal.byListIndHyp G E n kn kc rs fuel Γ Φ t u

/-- The type of a proof by normalization written in Geb. -/
abbrev tyNorm : Tree :=
  arrow tyT (arrow tyTs (arrow tyT (arrow tyNRs (arrow tyT (arrow tyTs (arrow tyTs
    (arrow tyT (arrow tyT tyT))))))))

/-- The type of a proof by induction with a step written in Geb. -/
abbrev tyInd : Tree :=
  arrow tyT (arrow tyTs (arrow tyT (arrow tyT (arrow tyT (arrow tyT (arrow tyNRs (arrow tyT
    (arrow tyTs (arrow tyTs (arrow tyT (arrow tyT tyT)))))))))))

/-- The type of a proof by induction with the induction hypothesis written in Geb. -/
abbrev tyIndHyp : Tree :=
  arrow tyT (arrow tyTs (arrow tyT (arrow tyT (arrow tyT (arrow tyNRs (arrow tyT
    (arrow tyTs (arrow tyTs (arrow tyT (arrow tyT tyT))))))))))

/-- The loaded prover's proof, where the program loads the prover's definitions, each found by
its name as {lit}`nm` spells it. -/
def Call.geb (P : List (List Char × Kernel.Glob)) (nm : String → List Char) (G : Internal.Globals)
    (E : Array Entry) (Γ : List Tree) (Φ : List Term) (t u : Term) : Call → Option Tree
  | .norm w n rs fuel => do
    let f ← fn P (nm (if w then "Prover.byNormW" else "Prover.byNorm")) tyNorm
    pure (f (encGlobals G) (E.toList.map encEntry) (Kernel.leaf n) (plain rs) (Kernel.leaf fuel) Γ
      (Φ.map encTerm) (encTerm t) (encTerm u))
  | .natInd n kz ks s rs fuel => do
    let f ← fn P (nm "Prover.byNatInd") tyInd
    pure (f (encGlobals G) (E.toList.map encEntry) (Kernel.leaf n) (Kernel.leaf kz)
      (Kernel.leaf ks) (encTerm s) (plain rs) (Kernel.leaf fuel) Γ (Φ.map encTerm) (encTerm t)
      (encTerm u))
  | .listInd n kn kc s rs fuel => do
    let f ← fn P (nm "Prover.byListInd") tyInd
    pure (f (encGlobals G) (E.toList.map encEntry) (Kernel.leaf n) (Kernel.leaf kn)
      (Kernel.leaf kc) (encTerm s) (plain rs) (Kernel.leaf fuel) Γ (Φ.map encTerm) (encTerm t)
      (encTerm u))
  | .natIndHyp n kz ks rs fuel => do
    let f ← fn P (nm "Prover.byNatIndHyp") tyIndHyp
    pure (f (encGlobals G) (E.toList.map encEntry) (Kernel.leaf n) (Kernel.leaf kz)
      (Kernel.leaf ks) (plain rs) (Kernel.leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u))
  | .listIndHyp n kn kc rs fuel => do
    let f ← fn P (nm "Prover.byListIndHyp") tyIndHyp
    pure (f (encGlobals G) (E.toList.map encEntry) (Kernel.leaf n) (Kernel.leaf kn)
      (Kernel.leaf kc) (plain rs) (Kernel.leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u))

/-- The theorems of a test module, each with its proof from the theorems before it. -/
abbrev Theorems : Type := List (Internal.Thm × (Array Entry → Option Internal.Deriv))

/-- The proofs of the test modules of the internal language's derivations and logic: each
theorem's constants, the theorems it is among, its index there, and the call proving it. -/
def calls : List (Internal.Globals × Theorems × ℕ × Call) :=
  let D := InternalDerivation.theorems
  let eqns := InternalDerivation.eqns
  let Lg := InternalLogic.theorems
  [(Internal.G, D, 0, .norm false 1 (eqns ++ [.delta 0]) 64),
   (Internal.G, D, 1, .listInd 1 0 1 InternalDerivation.consStep (eqns ++ [.delta 0]) 64),
   (Internal.G, D, 2, .listInd 1 0 1 InternalDerivation.consStep (eqns ++ [.delta 0]) 64),
   (Internal.G, D, 3, .norm false 1 (eqns ++ [.thm 1 [Internal.A]]) 64),
   (Internal.G, D, 4, .norm false 0 (eqns ++ [.delta 1]) 64),
   (Internal.G, D, 5, .norm false 0 (eqns ++ [.delta 1]) 64),
   (Internal.G, D, 6, .natInd 0 2 3 (Internal.succT (Term.var 0)) (eqns ++ [.delta 1]) 64),
   (Internal.G, D, 4, .norm true 0 (eqns ++ [.delta 1]) 64),
   (InternalLogic.GL, Lg, Lg.length - 2, .natIndHyp 0 2 3 (eqns ++ [.delta 1]) 64),
   (InternalLogic.GL, Lg, Lg.length - 1, .listIndHyp 1 0 1 (eqns ++ [.delta 0]) 64)]

-- the prover written in Geb proves each theorem as the Lean prover does
#guard ((loaded GoedelT.ProofTests.bundler.toList proverProgram.toList).map fun P ↦
  calls.all fun (G, ts, k, c) ↦ match ts[k]?, ts[k]?.bind (Internal.eqParts ·.1.concl) with
    | some (a, _), some (t, u) =>
      let E := entries ts k
      (c.lean G E a.ctx a.hyps t u).isSome &&
        c.geb P String.toList G E a.ctx a.hyps t u ==
          some (encOpt ((c.lean G E a.ctx a.hyps t u).map encDeriv))
    | _, _ => false).getD false

end GebTests.Prototypes.FreeTopos.GebProve

end
