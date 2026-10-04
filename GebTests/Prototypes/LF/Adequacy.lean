/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Adequacy

/-!
# Tests for the adequacy of the representation of the internal language

Addition, the fold of its second argument from the first by the successor, is a fold with a
parameter: its start is a variable around it. In the internal language it is the application of
the fold with parameters; its encoding is the signature's fold whose start is that variable, which
checks against the family of terms of the natural numbers, and decodes to it.

## Tags

prototype, logical framework, LF, adequacy
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Term Globals zeroPrim succPrim iterDefn)

/-- Zero, the successor and the fold with parameters, of indices {lit}`0`, {lit}`1` and
{lit}`0`. -/
def addGlobals : Globals := ⟨[zeroPrim, succPrim], [.language iterDefn], 0⟩

/-- The environment of two natural numbers {lit}`m` and {lit}`n`, the innermost first. -/
def addEnv : MEnv := FreeTopos.Internal.stdEnv [FreeTopos.nat, FreeTopos.nat]

/-- {lit}`m + n`: the fold with parameters, at the natural numbers, of {lit}`n` from {lit}`m` by
the successor. -/
def addTerm : MTerm :=
  Term.defn 0 [FreeTopos.nat] [Term.var 0, Term.pair (Term.var 1)
    (Term.lam FreeTopos.nat (Term.arr 1 [] (Term.var 0)))]

/-- {lit}`natRec nat m (λ x. succ x) n`. -/
def addLF : Expr := natRec nat (v 1) (Expr.lam (succ (v 0))) (v 0)

/-- The encoding of addition is the signature's fold from the variable {lit}`m`. -/
theorem enc_addTerm :
    enc addGlobals 0 1 0 addTerm (FreeTopos.Internal.ctxObj [FreeTopos.nat, FreeTopos.nat])
      addEnv = some addLF := by
  decide +kernel

/-- The fold from a variable decodes to the application of the fold with parameters. -/
theorem dec_addLF : dec 0 1 0 addLF = some addTerm := rfl

/-- The fold from a variable checks against the family of terms of the natural numbers. -/
theorem addLF_checks : Checks sig [tm nat, tm nat] addLF (tm nat) = true := by decide +kernel

end Geb.LF.Topos.Tests

end
