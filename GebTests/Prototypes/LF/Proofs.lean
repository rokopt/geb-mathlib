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
of the fold at zero, one at a successor, and an induction whose step substitutes equals.

## Tags

prototype, logical framework, LF, proof, derivation
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Globals Thm zeroPrim succPrim iterDefn)

/-- Zero, the successor and the fold with parameters, of indices {lit}`0`, {lit}`1` and
{lit}`0`. -/
def pfGlobals : Globals := ⟨[zeroPrim, succPrim], [.language iterDefn], 0⟩

/-- The successor as an LF abstraction. -/
def succLam : Expr := Expr.lam (succ (v 0))

/-- Whether a proof, in an LF context of term variables of the natural numbers, decodes to a
derivation that proves the decoding of an equation in the internal context of as many natural
numbers. -/
def provesNat (k : ℕ) (M F : Expr) : Bool :=
  match decPf 0 1 0 M (List.replicate k none) 0, dec 0 1 0 F with
    | some D, some φ => Thm.checks pfGlobals #[] ⟨0, List.replicate k FreeTopos.nat, [], φ⟩ D
    | _, _ => false

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

end Geb.LF.Topos.Tests

end
