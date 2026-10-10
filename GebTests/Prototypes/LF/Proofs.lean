/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Proofs
public meta import Geb.Prototypes.LF.Topos.Proofs -- shake: keep

/-!
# Tests for the decoding of proofs

The proofs that the type inhabitation solver Canonical finds of three equations of addition in
pure LF decode to derivations of the internal language that its checker accepts: a computation
of the fold at zero, one at a successor, and an induction whose step substitutes equals. So do a
substitution of equals into a motive whose fold's step mentions the motive's variable, the
computations of the fold of a list, and the proof by induction on lists that the right fold by
construction from the empty list is the identity.

## Tags

prototype, logical framework, LF, proof, derivation
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Globals Thm zeroPrim succPrim nilPrim consPrim)

/-- Zero, the successor, the empty list and the construction of a list, of indices {lit}`0` to
{lit}`3`. -/
def pfGlobals : Globals := ⟨[zeroPrim, succPrim, nilPrim, consPrim], [], 0⟩

/-- The indices of the primitive arrows of {name}`pfGlobals`. -/
def pfIdx : PrimIdx := ⟨0, 1, 2, 3⟩

/-- The successor as an LF abstraction. -/
def succLam : Expr := Expr.lam (succ (v 0))

/-- Whether a proof, in an LF context of term variables of the types of {lit}`Γ`, decodes to a
derivation that proves the decoding of an equation in the internal context {lit}`Γ`. -/
def proves (Γ : List PartialHorn.Tree) (M F : Expr) : Bool :=
  match decPf pfIdx M (Γ.map fun _ ↦ none) 0, dec pfIdx F with
    | some D, some φ => Thm.checks pfGlobals #[] ⟨0, Γ, [], φ⟩ D
    | _, _ => false

/-- Whether a proof, in an LF context of term variables of the natural numbers, decodes to a
derivation that proves the decoding of an equation in the internal context of as many natural
numbers. -/
def provesNat (k : ℕ) (M F : Expr) : Bool := proves (List.replicate k FreeTopos.nat) M F

-- `n + 0 = n` by the computation of the fold at zero.
#guard provesNat 1 (Expr.const 25 [nat, v 0, succLam])
  (eq nat (natRec nat (v 0) succLam zero) (v 0))

-- `m + succ n = succ (m + n)` by the computation of the fold at a successor.
#guard provesNat 2 (Expr.const 26 [nat, v 1, succLam, v 0])
  (eq nat (natRec nat (v 1) succLam (succ (v 0))) (succ (natRec nat (v 1) succLam (v 0))))

/-- The step of the induction for {lit}`0 + n = n`: the substitution of equals at the motive
{lit}`λ x. 0 + succ n = succ x`, from the hypothesis {lit}`0 + n = n` and the computation of the
fold at the successor. -/
def zeroAddStep : Expr :=
  Expr.lam (Expr.lam (Expr.const 19 [nat,
    Expr.lam (eq nat (natRec nat zero succLam (succ (v 2))) (succ (v 0))),
    natRec nat zero succLam (v 1), v 1, v 0, Expr.const 26 [nat, zero, succLam, v 1]]))

-- `0 + n = n` by induction.
#guard provesNat 1 (Expr.const 29 [Expr.lam (eq nat (natRec nat zero succLam (v 0)) (v 0)),
    Expr.const 25 [nat, zero, succLam], zeroAddStep, v 0])
  (eq nat (natRec nat zero succLam (v 0)) (v 0))

/-- {lit}`n + 0`, the fold whose computation at zero proves it equal to {lit}`n`. -/
def addZero : Expr := natRec nat (v 0) succLam zero

-- `natRec 0 (λ a. n) 1 = n`: the motive `λ x. natRec 0 (λ a. x) 1 = x`, whose fold's step
-- mentions its variable, holds at `n + 0` by the computation of the fold at a successor, and
-- `n + 0 = n` by its computation at zero.
#guard provesNat 1 (Expr.const 19 [nat,
    Expr.lam (eq nat (natRec nat zero (Expr.lam (v 1)) (succ zero)) (v 0)), addZero, v 0,
    Expr.const 25 [nat, v 0, succLam],
    Expr.const 26 [nat, zero, Expr.lam (addZero.rename Nat.succ), zero]])
  (eq nat (natRec nat zero (Expr.lam (v 1)) (succ zero)) (v 0))

/-- The construction of a list of natural numbers as a step of a fold:
{lit}`λ h r. cons nat (pair h r)`. -/
def consLam : Expr := Expr.lam (Expr.lam (cons nat (pair nat (list nat) (v 1) (v 0))))

/-- The right fold of a list of natural numbers by construction from the empty list. -/
def foldCons (x : Expr) : Expr := listRec nat (list nat) (nil nat) consLam x

-- `foldCons nil = nil` by the computation of the fold at the empty list.
#guard proves [] (Expr.const 34 [nat, list nat, nil nat, consLam])
  (eq (list nat) (foldCons (nil nat)) (nil nat))

-- `foldCons (cons h t) = cons h (foldCons t)` by the computation of the fold at a construction.
#guard proves [FreeTopos.list FreeTopos.nat, FreeTopos.nat]
  (Expr.const 35 [nat, list nat, nil nat, consLam, v 1, v 0])
  (eq (list nat) (foldCons (cons nat (pair nat (list nat) (v 1) (v 0))))
    (cons nat (pair nat (list nat) (v 1) (foldCons (v 0)))))

/-- The step of the induction for {lit}`foldCons l = l`: the substitution of equals at the motive
{lit}`λ y. foldCons (cons h t) = cons h y`, from the hypothesis {lit}`foldCons t = t` and the
computation of the fold at the construction. -/
def foldConsStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 19 [list nat,
    Expr.lam (eq (list nat) (foldCons (cons nat (pair nat (list nat) (v 3) (v 2))))
      (cons nat (pair nat (list nat) (v 3) (v 0)))),
    foldCons (v 1), v 1, v 0, Expr.const 35 [nat, list nat, nil nat, consLam, v 2, v 1]])))

-- `foldCons l = l` by induction on lists.
#guard proves [FreeTopos.list FreeTopos.nat]
  (Expr.const 36 [nat, Expr.lam (eq (list nat) (foldCons (v 0)) (v 0)),
    Expr.const 34 [nat, list nat, nil nat, consLam], foldConsStep, v 0])
  (eq (list nat) (foldCons (v 0)) (v 0))

end Geb.LF.Topos.Tests

end
