/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Literals -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Literals -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.ByMachine -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.ByMachine -- shake: keep
public import GebTests.Prototypes.FreeTopos.Stored -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Stored -- shake: keep

set_option doc.verso true in
/-!
# The environment machine at the library's arithmetic

Equations of the library's arithmetic at numerals proved by a step of the environment machine
({name}`Geb.FreeTopos.Internal.machineReduce`) at each side, every definition unfolded, in the
development of {lit}`GebTests.Prototypes.FreeTopos.Literals`: the machine's normal forms of the
two sides are one term exactly when the conversion checker accepts the join of the two steps.
Abstractions and folds are equal by the reduction of their bodies and steps. Reading back a delayed
value does not compute it, and normalizing a closure or a fold does not read back its environment.
A join rewriting by a hypothesis is translated by steps of the machine rewriting by it, and the
store reads back the rules of a step.

## Main definitions

* {lit}`byMachine` — the certificate of an equation by a step of the machine at each side.
* {lit}`proves` — whether it proves an equation of closed terms.
* {lit}`infeasible` — a delayed value whose computation takes more steps than are feasible.
* {lit}`doubling`, {lit}`normalForm` — a value whose term has an exponential size, and the normal
  form of a value.
* {lit}`hypThm`, {lit}`translatedBy` — a theorem of a hypothesis, and whether a derivation of it
  is translated.
* {lit}`ruleDecl`, {lit}`roundTrips` — a declaration whose step rewrites by rules, and whether a
  declaration's text reads back to the declaration.

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
open Internal (Term Thm ConvDeriv ConvDecl Rule Deriv)

/-- The certificate of an equation by a step of the machine at each side, every definition of the
library unfolded, the rose-tree folds' lists built by the translation's primitives. -/
def byMachine : ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.machine 4096 lib.length [] 0 1 []) [],
      RoseTree.node (.machine 4096 lib.length [] 0 1 []) []]

/-- Whether a step of the machine at each side proves an equation of closed terms. -/
def proves (t u : Term) : Bool :=
  (⟨0, [], [], Term.eq t u⟩ : Thm).convChecks G entries [] byMachine

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
each definition of two arguments equal to the literal of its value. -/
def agrees (bound : ℕ) : Bool :=
  [Sym.add, .mul, .eqB, .cmp, .ltB, .sub, .divMod].all fun s ↦
    (List.range bound).all fun a ↦ (List.range bound).all fun b ↦
      match Geb.FreeTopos.Literals.eval (bin s a b) with
      | some v => proves (bin s a b) v.term
      | none => false

#guard agrees 9

/-- A delayed value whose computation takes more steps than are feasible, its source the unit. -/
def infeasible : Internal.Val :=
  Internal.delayed (Thunk.mk fun _ ↦ (2 ^ 64).fold (fun _ _ r ↦ r) none)
    (Internal.vnode .star [])

-- reading back a delayed value, at the root and below a node, does not compute it
#guard Internal.readBack 0 infeasible = Term.star
#guard Internal.readBack 0 (Internal.vnode .pair [infeasible, infeasible]) =
  Term.pair Term.star Term.star

/-- A value sharing its subvalues whose term has a size exponential in a number. -/
def doubling (m : ℕ) : Internal.Val :=
  m.rec (Internal.vnode .star []) fun _ v ↦ Internal.vnode .pair [v, v]

/-- The normal form of a value in the empty context. -/
def normalForm (v : Internal.Val) : Option Term :=
  ((Internal.machine G 0 (fun _ ↦ true) 0 1 (fun _ _ _ ↦ none) 64).nf [] 0 v).map Prod.fst

-- the normal form of a closure and of a fold reads no value of the environment their bodies omit
#guard normalForm (Internal.vnode (.clo bitsTy (Term.var 0) 0) [doubling 64]) =
  some (Term.lam bitsTy (Term.var 0))
#guard normalForm (Internal.vnode (.natRec (Term.var 0) 0)
    [Internal.vnode .star [], Internal.vnode (.free (-1)) [], doubling 64]) =
  some (Term.natRec Term.star (Term.var 0) (Term.var 0))

-- a value read back under further binders denotes the same variable
#guard Internal.readBack 3 (Internal.vnode (.free 0) []) = Term.var 2
#guard Internal.readBack 3 (Internal.vnode (.free (-1)) []) = Term.var 3

-- the steps of folds are reduced, and a step's variable is its fold's
#guard proves (Term.lam nat (Term.natRec Term.star
    (Term.fst (Term.pair (Term.var 0) Term.star)) (Term.var 0)))
  (Term.lam nat (Term.natRec Term.star (Term.var 0) (Term.var 0)))
#guard !proves (Term.lam nat (Term.natRec (Term.var 0) (Term.var 0) (Term.var 0)))
  (Term.lam nat (Term.natRec (Term.var 0) (Term.var 1) (Term.var 0)))

/-- The theorem that two variables are equal, under the hypothesis that the first two are. -/
def hypThm (u v : ℕ) : Thm :=
  ⟨0, [bitsTy, bitsTy], [Term.eq (Term.var 0) (Term.var 1)], Term.eq (Term.var u) (Term.var v)⟩

/-- A join rewriting one side by the hypothesis, in a direction, and the other by no rule. -/
def hypDeriv (flip : Bool) : Deriv :=
  RoseTree.node .join [RoseTree.node (.rwHyp 0 flip) [], RoseTree.node .refl []]

/-- Whether a theorem's derivation is replaced by a certificate of steps of the machine. -/
def translatedBy (a : Thm) (d : Deriv) : Bool :=
  match Internal.Thm.byMachine G entries 4096 a d with
  | .conv _ _ => true
  | _ => false

-- a join rewriting by a hypothesis from its left side is translated, and from its right side not
#guard translatedBy (hypThm 0 1) (hypDeriv false)
#guard (hypThm 1 0).checks G entries (hypDeriv true)
#guard !translatedBy (hypThm 1 0) (hypDeriv true)

-- the rules a derivation cites, and the definitions it unfolds
#guard (Internal.citedIn (hypDeriv false)).map List.length = some 1
#guard (Internal.citedIn (hypDeriv true)).isNone
#guard (Internal.citedIn (RoseTree.node .refl [])).map List.length = some 0
#guard (Internal.unfoldsIn G entries 0 (RoseTree.node .delta []) [] [] (bin .add 1 2)).length = 1
#guard (Internal.unfoldsIn G entries 0 (RoseTree.node .refl []) [] [] (bin .add 1 2)).isEmpty

/-- A declaration whose certificate is a step of the machine at a list of rules. -/
def ruleDecl (rs : List Internal.NormRule) : ConvDecl :=
  .conv ⟨0, [], [], Term.star⟩ (RoseTree.node (.machine 8 2 [1] 3 4 rs) [])

/-- Whether a declaration's text reads back to the declaration, by their numbers. -/
def roundTrips (d : ConvDecl) : Bool :=
  (Stored.convDeclsToNats [d]).any fun ns ↦
    ((Stored.convDeclsOfText (" ".intercalate (ns.map toString))).bind
      Stored.convDeclsToNats) == some ns

-- a step's rules are stored and read back
#guard roundTrips (ruleDecl [.thm 5 [], .hyp 6])
#guard Stored.convDeclsToNats [ruleDecl [.hyp 6]] != Stored.convDeclsToNats [ruleDecl [.hyp 7]]

end GebTests.Prototypes.FreeTopos.Machine

end
