/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Rewrite
public import Geb.Prototypes.LF.Topos.Signature
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The computation rules of the internal language as rewrite rules

The computation rules of the fragment of the Mitchell–Bénabou language represented by
{name}`Geb.LF.Topos.sig`, as rewrite rules on its constants ({cite}`CousineauDowek2007`): the β
rule of abstraction, the two computation rules of pairs, and the two of the fold of the natural
numbers. Modulo these rules a term and the term it computes to are terms of the same types, so
that an equation that holds by computation is proved by reflexivity alone, the regime in which
{cite}`NormanAvigad2025` searches with recursors' reduction rules. The η rules of pairs and of the
terminal type, whose left sides are not applications of a constant, stay derivation rules of the
signature, as do the computation rules themselves, which are redundant modulo the rules.

## Main definitions

* {lit}`betaRule`, {lit}`fstPairRule`, {lit}`sndPairRule`, {lit}`natZeroRule`,
  {lit}`natSuccRule` — the rules.
* {lit}`rules` — the list of them.

## References

* {cite}`CousineauDowek2007`
* {cite}`NormanAvigad2025`, Section 3.1.

## Tags

logical framework, LF, rewriting, β-reduction, recursor
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open Expr (arrow)

/-- {lit}`app A B (lam A B F) a ↦ F a`, in {lit}`A B : tp, F : tm A → tm B, a : tm A`. -/
def betaRule : Rule where
  vars := [tm (v 2), arrow (tm (v 1)) (tm (v 0)), tp, tp]
  lhs := app (v 3) (v 2) (lam (v 3) (v 2) (v 1)) (v 0)
  rhs := Expr.var 1 [v 0]

/-- {lit}`fst A B (pair A B a b) ↦ a`, in {lit}`A B : tp, a : tm A, b : tm B`. -/
def fstPairRule : Rule where
  vars := [tm (v 1), tm (v 1), tp, tp]
  lhs := fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))
  rhs := v 1

/-- {lit}`snd A B (pair A B a b) ↦ b`, in {lit}`A B : tp, a : tm A, b : tm B`. -/
def sndPairRule : Rule where
  vars := [tm (v 1), tm (v 1), tp, tp]
  lhs := snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))
  rhs := v 0

/-- {lit}`natRec C z s (zeroAt t) ↦ z`, in {lit}`C : tp, z : tm C, s : tm C → tm C, t : tm 1`:
zero at any element of the terminal object, all of which are its element by the η rule of the
terminal type. -/
def natZeroRule : Rule where
  vars := [tm one, arrow (tm (v 1)) (tm (v 1)), tm (v 0), tp]
  lhs := natRec (v 3) (v 2) (v 1) (zeroAt (v 0))
  rhs := v 2

/-- {lit}`natRec C z s (succ n) ↦ s (natRec C z (λ x. s x) n)`, in
{lit}`C : tp, z : tm C, s : tm C → tm C, n : tm N`. -/
def natSuccRule : Rule where
  vars := [tm nat, arrow (tm (v 1)) (tm (v 1)), tm (v 0), tp]
  lhs := natRec (v 3) (v 2) (v 1) (succ (v 0))
  rhs := Expr.var 1 [natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (v 0)]

/-- The rules. -/
def rules : List Rule := [betaRule, fstPairRule, sndPairRule, natZeroRule, natSuccRule]

end Geb.LF.Topos

end
