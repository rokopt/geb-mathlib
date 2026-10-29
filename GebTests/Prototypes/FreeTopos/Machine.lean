/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Literals -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Literals -- shake: keep

set_option doc.verso true in
/-!
# The environment machine at the library's arithmetic

Equations of the library's arithmetic at numerals proved by a step of the environment machine
({name}`Geb.FreeTopos.Internal.machineReduce`) at each side, every definition unfolded, in the
development of {lit}`GebTests.Prototypes.FreeTopos.Literals`: the machine's normal forms of the
two sides are one term exactly when the conversion checker accepts the join of the two steps.
Abstractions are equal by the reduction of their bodies.

## Main definitions

* {lit}`byMachine` — the certificate of an equation by a step of the machine at each side.
* {lit}`proves` — whether it proves an equation of closed terms.

## Tags

internal language, abstract machine, conversion, arithmetic, numeral, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Machine

open Geb Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Literals (G entries bin lit)
open Geb.FreeTopos.Literals (Sym bitsT)
open Geb.FreeTopos.Translation (lib trueT bnilT eqO gtO bitsTy)
open Internal (Term Thm ConvDeriv)

/-- The certificate of an equation by a step of the machine at each side, every definition of the
library unfolded, the rose-tree folds' lists built by the translation's primitives. -/
def byMachine : ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.machine 4096 lib.length [] 0 1) [],
      RoseTree.node (.machine 4096 lib.length [] 0 1) []]

/-- Whether a step of the machine at each side proves an equation of closed terms. -/
def proves (t u : Term) : Bool :=
  (⟨0, [], [], Term.eq t u⟩ : Thm).convChecks G entries byMachine

-- arithmetic, comparison and their compositions
#guard proves (bin .add 7 9) (lit 16)
#guard proves (bin .mul 1000 1000) (lit 1000000)
#guard proves (bin .sub 50 8) (lit 42)
#guard proves (bin .sub 3 5) (lit 0)
#guard proves (bin .ltB 3 5) trueT && proves (bin .ltB 5 3) bnilT
#guard proves (bin .cmp 4 4) eqO && proves (bin .cmp 9 4) gtO
#guard proves (Sym.eqB.call [bin .add 2 3, lit 5]) trueT
#guard proves (Sym.pred.call [Sym.dbl.call [Sym.succ.call [lit 20]]]) (lit 41)
#guard proves (bin .mul 123456 654321) (lit (123456 * 654321))

-- a false equation is not proved
#guard !proves (bin .add 2 2) (lit 5)

-- abstractions equal by the reduction of their bodies
#guard proves (Term.lam bitsTy (bin .add 2 3)) (Term.lam bitsTy (lit 5))
#guard proves (Term.lam bitsTy (Term.fst (Term.pair (Term.var 0) (lit 1))))
  (Term.lam bitsTy (Term.var 0))
#guard proves (Term.lam bitsTy (Term.lam bitsTy (Term.app
    (Term.lam bitsTy (Term.var 2)) (bin .mul 6 7))))
  (Term.lam bitsTy (Term.lam bitsTy (Term.var 1)))
#guard !proves (Term.lam bitsTy (Term.var 0)) (Term.lam bitsTy (lit 0))

/-- Whether, at the numerals of numbers below a bound, a step of the machine at each side proves
each definition of two arguments equal to the numeral of its value. -/
def agrees (bound : ℕ) : Bool :=
  [Sym.add, .mul, .eqB, .cmp, .ltB, .sub].all fun s ↦
    (List.range bound).all fun a ↦ (List.range bound).all fun b ↦
      match Geb.FreeTopos.Literals.eval (bin s a b) with
      | some v => proves (bin s a b) v.term
      | none => false

#guard agrees 9

end GebTests.Prototypes.FreeTopos.Machine

end
