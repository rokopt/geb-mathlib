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
parameter: its start is a variable around it. Its encoding is the signature's fold whose start is
that variable, which checks against the family of terms of the natural numbers, and decodes to
it. The length of a list, the fold of the list from zero by the successor, encodes to the
signature's fold of lists, and the number of a rose tree's root's children, the fold of the tree
whose step is the length of the list of the children's values, to the signature's fold of rose
trees with a fold of lists in its step; each checks and decodes alike.

## Tags

prototype, logical framework, LF, adequacy
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Term Globals zeroPrim succPrim nilPrim consPrim nodePrim)

/-- Zero, the successor, the empty list, the construction of a list and the construction of a rose
tree, of indices {lit}`0` to {lit}`4`. -/
def addGlobals : Globals := ⟨[zeroPrim, succPrim, nilPrim, consPrim, nodePrim], [], 0⟩

/-- The indices of the primitive arrows of {name}`addGlobals`. -/
def addIdx : PrimIdx := ⟨0, 1, 2, 3, 4⟩

/-- The environment of two natural numbers {lit}`m` and {lit}`n`, the innermost first. -/
def addEnv : MEnv := FreeTopos.Internal.stdEnv [FreeTopos.nat, FreeTopos.nat]

/-- {lit}`m + n`: the fold of {lit}`n` from {lit}`m` by the successor. -/
def addTerm : MTerm := Term.natRec (Term.var 1) (Term.arr 1 [] (Term.var 0)) (Term.var 0)

/-- {lit}`natRec nat m (λ x. succ x) n`. -/
def addLF : Expr := natRec nat (v 1) (Expr.lam (succ (v 0))) (v 0)

/-- The encoding of addition is the signature's fold from the variable {lit}`m`. -/
theorem enc_addTerm :
    enc addGlobals addIdx addTerm (FreeTopos.Internal.ctxObj [FreeTopos.nat, FreeTopos.nat])
      addEnv = some addLF := by
  decide +kernel

/-- The fold from a variable decodes to the language's fold from the variable. -/
theorem dec_addLF : dec addIdx addLF = some addTerm := rfl

/-- The fold from a variable checks against the family of terms of the natural numbers. -/
theorem addLF_checks : Checks sig [tm nat, tm nat] addLF (tm nat) = true := by decide +kernel

/-- The environment of a list {lit}`l` of natural numbers. -/
def lenEnv : MEnv := FreeTopos.Internal.stdEnv [FreeTopos.list FreeTopos.nat]

/-- The length of {lit}`l`: the fold of the list from zero by the successor of the value. -/
def lenTerm : MTerm :=
  Term.listRec (Term.arr 0 [] Term.star) (Term.arr 1 [] (Term.var 0)) (Term.var 0)

/-- {lit}`listRec nat nat zero (λ h r. succ r) l`. -/
def lenLF : Expr := listRec nat nat zero (Expr.lam (Expr.lam (succ (v 0)))) (v 0)

/-- The encoding of the length is the signature's fold of lists. -/
theorem enc_lenTerm :
    enc addGlobals addIdx lenTerm (FreeTopos.Internal.ctxObj [FreeTopos.list FreeTopos.nat])
      lenEnv = some lenLF := by
  decide +kernel

/-- The fold of a list decodes to the language's fold of lists. -/
theorem dec_lenLF : dec addIdx lenLF = some lenTerm := rfl

/-- The fold of a list checks against the family of terms of the natural numbers. -/
theorem lenLF_checks : Checks sig [tm (list nat)] lenLF (tm nat) = true := by decide +kernel

/-- The environment of a rose tree {lit}`t`. -/
def roseEnv : MEnv := FreeTopos.Internal.stdEnv [FreeTopos.rose]

/-- The number of the children of the root of {lit}`t`: the fold of the tree whose step is the
length of the list of the children's values. -/
def degTerm : MTerm := Term.roseRec FreeTopos.nat
  (Term.listRec (Term.arr 0 [] Term.star) (Term.arr 1 [] (Term.var 0)) (Term.snd (Term.var 0)))
  (Term.var 0)

/-- {lit}`roseRec nat (λ p. listRec nat nat zero (λ h r. succ r) (snd nat (list nat) p)) t`. -/
def degLF : Expr := roseRec nat
  (Expr.lam (listRec nat nat zero (Expr.lam (Expr.lam (succ (v 0)))) (snd nat (list nat) (v 0))))
  (v 0)

/-- The encoding of the number of the root's children is the signature's fold of rose trees. -/
theorem enc_degTerm :
    enc addGlobals addIdx degTerm (FreeTopos.Internal.ctxObj [FreeTopos.rose]) roseEnv =
      some degLF := by
  decide +kernel

/-- The fold of a rose tree decodes to the language's fold of rose trees. -/
theorem dec_degLF : dec addIdx degLF = some degTerm := rfl

/-- The fold of a rose tree checks against the family of terms of the natural numbers. -/
theorem degLF_checks : Checks sig [tm rose] degLF (tm nat) = true := by decide +kernel

end Geb.LF.Topos.Tests

end
