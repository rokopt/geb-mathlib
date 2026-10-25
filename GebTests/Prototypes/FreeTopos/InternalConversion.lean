/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep

set_option doc.verso true in
/-!
# The conversion checker at the theorems of Gödel's T

The theorems of {lit}`GebTests.Prototypes.FreeTopos.InternalDerivation` proved by certificates of
the checker with a step of conversion ({name}`Geb.FreeTopos.Internal.convCheck`): an equation by
two steps of conversion, the innermost normalization or the reduction to the normal form, in
place of the two rewriting derivations the prover computes, each step one node; and a formula by
an earlier theorem at the instance that matches it. A step whose rules do not reach a common
normal form, and a theorem whose conclusion does not match, are rejected.

## Main definitions

* {lit}`entries` — the theorems, as the entries of the development.
* {lit}`byConv` — the certificate of an equation by two steps of conversion.
* {lit}`proves` — whether a certificate proves a theorem.

## Tags

internal language, conversion, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalConversion

open Geb Geb.PartialHorn Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Internal
open GebTests.Prototypes.FreeTopos.InternalDerivation (theorems development)
open Geb.FreeTopos.Internal (Term Thm Entry ConvRule ConvDeriv Depth NormRule)

/-- The theorems, as the entries of the development. -/
def entries : Array Entry := (theorems.map fun (a, _) ↦ Entry.language a).toArray

/-- The certificate of an equation by two steps of conversion, one at each side. -/
def byConv (step : ConvRule) : ConvDeriv :=
  RoseTree.node (.base .join) [RoseTree.node step [], RoseTree.node step []]

/-- The equations the normalizer applies, and the unfolding of the definition of index {lit}`k`. -/
def rules (k : ℕ) : List NormRule := InternalDerivation.eqns ++ [.delta k]

/-- The steps of conversion under the equations and the unfolding of a definition: the innermost
normalization and the reduction to the normal form. -/
def steps (k : ℕ) : List ConvRule := [.norm (rules k) 64, .eval (rules k) 64 .full]

/-- The nodes of a tree. -/
def nodes {α : Type} : RoseTree α → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- Whether the theorem of an index the certificate proves, with no earlier entries. -/
def proves (i : ℕ) (d : ConvDeriv) : Bool := (theorems[i]?.map (·.1)).any (·.convChecks G #[] d)

-- the theorems an equation's normalization proves, by either step
#guard steps 0 |>.all fun s ↦ proves 0 (byConv s)
#guard steps 1 |>.all fun s ↦ proves 4 (byConv s) && proves 5 (byConv s)

-- a step without the unfolding of the definition reaches no common normal form
#guard !proves 0 (byConv (.norm InternalDerivation.eqns 64))
#guard !proves 0 (byConv (.eval InternalDerivation.eqns 64 .full))

-- the step of conversion is a fraction of the base checker's derivation
#guard development.any fun ds ↦ match ds[4]? with
  | some (Internal.Decl.language _ d) => nodes (byConv (.eval (rules 1) 64 .full)) < nodes d
  | _ => false

/-- An instance of the second theorem, that appending the empty list is the identity, at a list
itself appended to the empty list. -/
def instanceThm : Thm :=
  ⟨1, [L], [], Term.eq (appendT (appendT (Term.var 0) nilT) nilT) (appendT (Term.var 0) nilT)⟩

-- the instance matches the second theorem's conclusion, and not the first's
#guard instanceThm.convChecks G entries (RoseTree.node (.applyMatch 1 [A]) [])
#guard !instanceThm.convChecks G entries (RoseTree.node (.applyMatch 0 [A]) [])

end GebTests.Prototypes.FreeTopos.InternalConversion

end
