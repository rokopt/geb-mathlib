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
are those of {name}`Geb.FreeTopos.Literals.eval` and {name}`Geb.FreeTopos.Literals.ready`, the
conversion checker written in Geb accepts the certificates of steps of the machine that
{name}`Geb.FreeTopos.Internal.convCheck` accepts, the machine written in Geb reduces as the
machine in Lean within each depth of recursion, and the check of a development's declarations
written in Geb ({lit}`bootstrap/free-topos/conversion.geb`) gives the state that
{name}`Geb.FreeTopos.Internal.checkConvDev` gives.

## Main definitions

* {lit}`provesGeb` — whether the checker written in Geb accepts a step of the machine at each side
  of an equation of closed terms.
* {lit}`reduceGeb`, {lit}`reduceLean`, {lit}`reductions` — the encoded reduction of a term in a
  context by the machine written in Geb within a depth of recursion, and by the machine in Lean,
  and the two at each depth below a bound.
* {lit}`byMachineHyp`, {lit}`checksAlike` — a certificate whose step of the machine rewrites by a
  hypothesis, and whether the two checkers decide alike that a certificate proves a theorem.
* {lit}`certified`, {lit}`devGeb`, {lit}`devLean` — a development with certificates, and the
  encoded state after it by the check written in Geb and by the check in Lean.
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
open GebTests.Prototypes.FreeTopos.Literals (G entries bin lit first recorded byLit)
open GebTests.Prototypes.FreeTopos.Machine (byMachine proves hypThm)
open Geb.FreeTopos.Literals (Sym)
open Geb.FreeTopos.Translation (lib trueT bnilT eqO gtO bitsTy)
open Internal (Term Thm ConvDeriv ConvDecl)

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

/-- The encoded reduction of a term in a context by the machine written in Geb within a depth of
recursion, every definition of the library unfolded and no rewriting at the roots. -/
def reduceGeb (fuel : ℕ) (Γ : List Tree) (t : Term) : Tree :=
  «Machine.machineReduce» (encGlobals G) (leaf 0) (fun j ↦ ofBool (decide (j.label < lib.length)))
    (leaf 0) (leaf 1) (fun _ _ _ ↦ «Prelude.none») (leaf fuel) Γ (encTerm t)

/-- The encoded reduction of a term in a context by the machine in Lean within a depth of
recursion, every definition of the library unfolded and no rewriting at the roots. -/
def reduceLean (fuel : ℕ) (Γ : List Tree) (t : Term) : Tree :=
  encOpt ((Internal.machineReduce G 0 (fun j ↦ decide (j < lib.length)) 0 1 (fun _ _ _ ↦ none)
    fuel Γ t).map encTerm)

/-- The two machines' encoded reductions of a term in a context within each depth of recursion
below a bound. -/
def reductions (bound : ℕ) (Γ : List Tree) (t : Term) : List (Tree × Tree) :=
  (List.range bound).map fun fuel ↦ (reduceGeb fuel Γ t, reduceLean fuel Γ t)

-- the machines agree within each depth of recursion, where the depth is exhausted and where the
-- reduction reaches its normal form: at arithmetic, at components, at abstractions and at folds
#guard (reductions 40 [] (bin .add 2 3)).all fun p ↦ p.1 == p.2
#guard (reductions 40 [] (bin .cmp 2 1)).all fun p ↦ p.1 == p.2
#guard (reductions 24 [] (Term.fst (bin .divMod 5 2))).all fun p ↦ p.1 == p.2
#guard (reductions 24 [] (Sym.pred.call [Sym.dbl.call [Sym.succ.call [lit 2]]])).all
  fun p ↦ p.1 == p.2
#guard (reductions 12 [] (Term.lam bitsTy (Term.fst (Term.pair (Term.var 0) (lit 1))))).all
  fun p ↦ p.1 == p.2
#guard (reductions 12 [bitsTy, bitsTy] (Term.pair (Term.var 1) (Term.snd (Term.pair Term.star
  (Term.var 0))))).all fun p ↦ p.1 == p.2
#guard (reductions 12 [] (Term.lam nat (Term.natRec Term.star
  (Term.fst (Term.pair (Term.var 0) Term.star)) (Term.var 0)))).all fun p ↦ p.1 == p.2
#guard (reductions 12 [] (Term.lam bitsTy (Term.lam bitsTy (Term.app
  (Term.lam bitsTy (Term.var 2)) (bin .mul 2 3))))).all fun p ↦ p.1 == p.2
-- the depths compared include those that are exhausted and those that reach a normal form
#guard reduceLean 29 [] (bin .add 2 3) == encOpt none
#guard (reduceLean 30 [] (bin .add 2 3)).label == 1
#guard (reduceLean 4 [] (Term.lam bitsTy (Term.fst (Term.pair (Term.var 0) (lit 1))))).label == 1

/-- A certificate of an equation by a step of the machine at each side, the first rewriting its
normal form by the first hypothesis. -/
def byMachineHyp : ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.machine 64 lib.length [] 0 1 [.hyp 0]) [],
      RoseTree.node (.machine 64 lib.length [] 0 1 []) []]

/-- Whether the checker written in Geb and the checker in Lean decide alike that a certificate
proves a theorem. -/
def checksAlike (a : Thm) (d : ConvDeriv) : Bool :=
  ((«Conversion.thmConvChecks» (encGlobals G) (entries.toList.map encEntry) [] (encThm a)
    (encConv d)).label != 0) == a.convChecks G entries [] d

-- a step of the machine rewriting by a hypothesis is accepted by both checkers, and without the
-- hypothesis by neither
#guard (hypThm 0 1).convChecks G entries [] byMachineHyp
#guard checksAlike (hypThm 0 1) byMachineHyp
#guard !(hypThm 0 1).convChecks G entries [] byMachine
#guard checksAlike (hypThm 0 1) byMachine

/-- The development of the library's arithmetic, the record that the evaluation at literals is
ready at an index, and two theorems with certificates: a sum by a step of evaluation at literals
from the first equation, and an equation by a step of the machine at each side. -/
def certified (j : ℕ) (t u : Term) : List ConvDecl :=
  recorded j ++ [.conv ⟨0, [], [], Term.eq (bin .add 7 9) (lit 16)⟩ (byLit first),
    .conv ⟨0, [], [], Term.eq t u⟩ byMachine]

/-- The encoded state after a development by the check written in Geb. -/
def devGeb (ds : List ConvDecl) : Tree :=
  «Conversion.checkConvDev» (encGlobals G) [] (ds.map encConvDecl)

/-- The encoded state after a development by the check in Lean. -/
def devLean (ds : List ConvDecl) : Tree :=
  encOpt ((Internal.checkConvDev G #[] ds).map encConvState)

-- the checks give one state at a development both accept, whose declarations are those of the
-- base checker, the record of readiness and theorems with certificates
#guard (devLean (certified first (bin .add 2 3) (lit 5))).label == 1
#guard devGeb (certified first (bin .add 2 3) (lit 5)) ==
  devLean (certified first (bin .add 2 3) (lit 5))
-- and both reject a record at an index where the evaluation is not ready, and a certificate that
-- does not prove its theorem
#guard devGeb (recorded 0) == encOpt none && devLean (recorded 0) == encOpt none
#guard devGeb (certified first (bin .add 2 2) (lit 5)) == encOpt none
#guard devLean (certified first (bin .add 2 2) (lit 5)) == encOpt none

end GebTests.Prototypes.FreeTopos.ConversionMirror

end
