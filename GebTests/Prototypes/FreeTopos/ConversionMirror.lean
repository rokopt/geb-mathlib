/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Machine -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Machine -- shake: keep
public import GebTests.Prototypes.FreeTopos.Agreement.Conversion -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Agreement.Conversion -- shake: keep
public meta import GebMirror.Metalogic -- shake: keep

set_option doc.verso true in
/-!
# The conversion checker written in Geb at the library's arithmetic

The evaluation at literals and the environment machine written in Geb
({lit}`bootstrap/free-topos/literals.geb`, {lit}`bootstrap/free-topos/machine.geb`), in the Lean
the bootstrap compiler emits, at the development of
{lit}`GebTests.Prototypes.FreeTopos.Literals`: the evaluation's terms and its test of readiness
are those of {name}`Geb.FreeTopos.Literals.eval` and {name}`Geb.FreeTopos.Literals.ready`, and the
conversion checker written in Geb accepts the certificates of steps of the machine that
{name}`Geb.FreeTopos.Internal.convCheck` accepts.

## Main definitions

* {lit}`provesGeb` — whether the checker written in Geb accepts a step of the machine at each side
  of an equation of closed terms.
* {lit}`litGeb`, {lit}`litLean` — the encoded term of a term's value by the evaluation written in
  Geb, and by the evaluation in Lean.

## Tags

internal language, abstract machine, conversion, arithmetic, numeral, mirror, test
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.ConversionMirror

open Geb Geb.Kernel Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Conversion
open GebTests.Prototypes.FreeTopos.Literals (G entries bin lit)
open GebTests.Prototypes.FreeTopos.Machine (byMachine proves)
open Geb.FreeTopos.Literals (Sym)
open Geb.FreeTopos.Translation (trueT bnilT eqO gtO bitsTy)
open Internal (Term)

/-- Whether the checker written in Geb accepts a step of the machine at each side of an equation
of closed terms. -/
def provesGeb (t u : Term) : Bool :=
  («Conversion.thmConvChecks» (encGlobals G) (entries.toList.map encEntry) []
    (encThm ⟨0, [], [], Term.eq t u⟩) (encConv byMachine)).label != 0

/-- The encoded term of a term's value by the evaluation written in Geb. -/
def litGeb (t : Term) : Tree := «Literals.litEval» (encTerm t)

/-- The encoded term of a term's value by the evaluation in Lean. -/
def litLean (t : Term) : Tree :=
  encOpt ((Geb.FreeTopos.Literals.eval t).map fun v ↦ encTerm v.term)

-- the evaluations agree at the definitions of two arguments and of one
#guard (List.range 6).all fun a ↦ (List.range 6).all fun b ↦
  [Sym.add, .mul, .eqB, .cmp, .ltB, .sub, .subE, .divMod].all fun s ↦
    litGeb (bin s a b) == litLean (bin s a b)
#guard [Sym.succ, .dbl, .pred, .log2, .isNil, .b0, .b1].all fun s ↦ (List.range 20).all fun a ↦
  litGeb (s.call [lit a]) == litLean (s.call [lit a])
#guard litGeb (Sym.condB.call [lit 0, lit 3, lit 4]) ==
  litLean (Sym.condB.call [lit 0, lit 3, lit 4])
#guard litGeb (Sym.condO.call [lit 2, eqO, gtO]) == litLean (Sym.condO.call [lit 2, eqO, gtO])
#guard litGeb (Term.fst (bin .divMod 17 5)) == litLean (Term.fst (bin .divMod 17 5))
#guard litGeb (Term.snd (bin .divMod 17 0)) == litLean (Term.snd (bin .divMod 17 0))
#guard litGeb (Term.var 0) == litLean (Term.var 0)

-- the tests of readiness agree at each index
#guard (List.range 40).all fun j ↦
  ((«Literals.ready» (encGlobals G) (entries.toList.map encEntry) (leaf j)).label != 0) ==
    Geb.FreeTopos.Literals.ready G entries j

-- the checker written in Geb accepts the steps of the machine the checker in Lean accepts
#guard provesGeb (bin .add 7 9) (lit 16)
#guard provesGeb (bin .sub 50 8) (lit 42)
#guard provesGeb (bin .cmp 4 4) eqO && provesGeb (bin .cmp 9 4) gtO
#guard !provesGeb (bin .add 2 2) (lit 5)
#guard provesGeb (Term.lam bitsTy (bin .add 2 3)) (Term.lam bitsTy (lit 5))
#guard provesGeb (Term.lam bitsTy (Term.fst (Term.pair (Term.var 0) (lit 1))))
  (Term.lam bitsTy (Term.var 0))

end GebTests.Prototypes.FreeTopos.ConversionMirror

end
