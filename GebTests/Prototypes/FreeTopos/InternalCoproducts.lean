/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep

set_option doc.verso true in
/-!
# Coproducts and the initial object in the internal language

The injections into a coproduct, its case analysis and the arrow from the initial object, placed
after the primitive arrows of the natural numbers and lists, confirmed by the checker's inference,
and the rules of the case analysis checked: its computation at each injection, its η by case
analysis on a variable of a coproduct type, and a formula in a context with a variable of the
initial type.

## Main definitions

* {lit}`GC` — the constants, the injections, the case analysis and the arrow from the initial
  object among them.
* {lit}`theorems` — the computations, the η and the formula, each with its proof.

## Tags

internal language, coproduct, initial object, case analysis, derivation
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalCoproducts

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv checkThms compileDefs inlPrim inrPrim casePrim)
open Geb.FreeTopos.Internal.Logic (nd)

/-- The constants: the primitive arrows of the natural numbers and lists, the injections, the
case analysis and the arrow from the initial object, and the definitions of appending, addition
and the connectives. -/
def GC : Internal.Globals :=
  ⟨prims ++ [inlPrim, inrPrim, casePrim, ⟨1, absurd (x 0), zero, x 0⟩],
    defs ++ Internal.Logic.defs 2, sig.length⟩

/-- The left injection into the coproduct of {lit}`a` and {lit}`b`. -/
def inlT (a b : Tree) (t : Term) : Term := Term.arr 4 [a, b] t

/-- The right injection into the coproduct of {lit}`a` and {lit}`b`. -/
def inrT (a b : Tree) (t : Term) : Term := Term.arr 5 [a, b] t

/-- The case analysis of a term of the coproduct of {lit}`a` and {lit}`b` by two functions into
{lit}`c`. -/
def caseT (a b c : Tree) (f g t : Term) : Term := Term.app (Term.arr 6 [a, b, c] (Term.pair f g)) t

-- the constants are well formed, the primitive arrows of the types they name
#guard (compileDefs GC).any fun cs ↦ GC.ok (ExtEnv.ofDefs cs)

/-- The theorems, each with its proof: the case analysis at each injection, its η, and a
formula in a context with a variable of the initial type. -/
def theorems : List (Thm × Deriv) := [
  (⟨3, [x 0, exp (x 1) (x 2), exp (x 0) (x 2)], [],
    Term.eq (caseT (x 0) (x 1) (x 2) (Term.var 2) (Term.var 1) (inlT (x 0) (x 1) (Term.var 0)))
      (Term.app (Term.var 2) (Term.var 0))⟩,
    nd .join [nd (.caseInl 6 4), nd .refl]),
  (⟨3, [x 1, exp (x 1) (x 2), exp (x 0) (x 2)], [],
    Term.eq (caseT (x 0) (x 1) (x 2) (Term.var 2) (Term.var 1) (inrT (x 0) (x 1) (Term.var 0)))
      (Term.app (Term.var 1) (Term.var 0))⟩,
    nd .join [nd (.caseInr 6 5), nd .refl]),
  (⟨2, [coprod (x 0) (x 1)], [],
    Term.eq (caseT (x 0) (x 1) (coprod (x 0) (x 1)) (Term.lam (x 0) (inlT (x 0) (x 1) (Term.var 0)))
      (Term.lam (x 1) (inrT (x 0) (x 1) (Term.var 0))) (Term.var 0)) (Term.var 0)⟩,
    nd (.coprodInd 4 5) [
      nd .join [nd .trans [nd (.caseInl 6 4), nd .beta], nd .refl],
      nd .join [nd .trans [nd (.caseInr 6 5), nd .beta], nd .refl]]),
  (⟨1, [zero, x 0], [], Term.eq (Term.arr 7 [x 0] (Term.var 0)) (Term.var 1)⟩,
    nd (.zeroInd 0))]

-- the development checks
#guard checkThms GC theorems #[]

end GebTests.Prototypes.FreeTopos.InternalCoproducts

end
