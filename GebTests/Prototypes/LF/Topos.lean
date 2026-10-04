/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Rules

/-!
# Tests for the internal language of a topos as an LF signature

The signature is well formed: each declaration is a kind or a type in the scope of those before
it. Symmetry of equality is derived from the substitution of equals and reflexivity, at the
predicate {lit}`λ x. eq A x t`; the same term does not prove the equation it starts from. The
rewrite rules are well typed, and a rule whose sides differ in type is not; modulo the rules,
reflexivity proves an equation that holds by computation of the fold, which it does not prove
without them.

## Tags

prototype, logical framework, LF, Mitchell–Bénabou language
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

/-- The declarations of the types and terms are well formed. -/
theorem objSig_ok : objSig.ok = true := by decide

/-- The whole signature is well formed. -/
theorem sig_ok : sig.ok = true := by decide +kernel

/-- The context {lit}`A : tp, t u : tm A, h : pf (eq A t u)`, the innermost first. -/
def symCtx : Ctx := [pf (eq (v 2) (v 1) (v 0)), tm (v 1), tm (v 0), tp]

/-- {lit}`leib A (λ x. eq A x t) t u h (refl A t)`. -/
def symProof : Expr :=
  Expr.const 19 [v 3, Expr.lam (eq (v 4) (v 0) (v 3)), v 2, v 1, v 0, Expr.const 18 [v 3, v 2]]

/-- The derivation proves {lit}`pf (eq A u t)`. -/
theorem symProof_checks : Checks sig symCtx symProof (pf (eq (v 3) (v 1) (v 2))) = true := by
  decide +kernel

/-- It does not prove {lit}`pf (eq A t u)`. -/
theorem symProof_not_refl : Checks sig symCtx symProof (pf (eq (v 3) (v 2) (v 1))) = false := by
  decide +kernel

/-- Each rewrite rule is well typed in the signature. -/
theorem sig_okMod : sig.okMod rules = true := by decide +kernel

/-- A rule rewriting the first component of a pair to the second component is not well typed. -/
theorem fstPair_to_snd_not_ok : Rule.ok sig { fstPairRule with rhs := v 0 } = false := by
  decide +kernel

/-- The context {lit}`C : tp, z : tm C, s : tm C → tm C`, the innermost first. -/
def recCtx : Ctx := [Expr.arrow (tm (v 1)) (tm (v 1)), tm (v 0), tp]

/-- The equation {lit}`natRec C z (λ x. s x) (succ zero) = s z`. -/
def recOne : Expr :=
  pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) (succ zero)) (Expr.var 0 [v 1]))

/-- Modulo the rules, reflexivity proves it. -/
theorem refl_recOne_mod : ChecksMod rules 20 sig recCtx (Expr.const 18 [v 2, Expr.var 0 [v 1]])
    recOne = true := by
  decide +kernel

/-- Without them it does not. -/
theorem refl_recOne_pure : Checks sig recCtx (Expr.const 18 [v 2, Expr.var 0 [v 1]]) recOne =
    false := by
  decide +kernel

end Geb.LF.Topos.Tests

end
