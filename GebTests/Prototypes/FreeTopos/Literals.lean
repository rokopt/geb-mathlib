/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.Conversion -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Conversion -- shake: keep

set_option doc.verso true in
/-!
# The library's arithmetic at numerals, by conversion

The equations of the library's arithmetic at the numerals' bits
({name}`Geb.FreeTopos.Literals.lemmas`) proved by the prover in the library's constants, after the
rebuildings of bitstrings by the folds that pair a list with a value, and the certificates of the
checker with a step of conversion that evaluate the arithmetic at numerals in one step, each
equation of a term and its value's numeral proved by that step at the term. The evaluation agrees
with the library's definitions unfolded and normalized; it is rejected where the equations are not
the theorems it names, and a false equation is not proved.

## Main definitions

* {lit}`development` — the rebuildings and the equations, each with its derivation.
* {lit}`entries`, {lit}`first` — the development's theorems, and the index of the first equation.
* {lit}`proves` — whether a step of evaluation proves an equation of closed terms.

## Tags

internal language, conversion, arithmetic, numeral, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Literals

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open scoped FinEnum
open Geb.FreeTopos.Literals (Sym Val bitsT num val lemmas ready)
open GebTests.Prototypes.FreeTopos.Translation (baseRules value)
open GebTests.Prototypes.FreeTopos.TranslationProofs (deltas develop rebuild lcaseRebuild listInd
  sides)
open Internal (Term Thm Entry Decl NormRule ConvDeriv)

/-- The constants: the library's definitions. -/
def G : Internal.Globals := globals []

/-- The rules of the normalization: the language's equations and the unfolding of every
definition. -/
def rs : List NormRule := baseRules ++ deltas lib.length

/-- The rebuildings of bitstrings by the folds of addition, of the successor, of the case
analysis of lists, of doubling and of the predecessor, each a theorem whose side is in normal
form. -/
def rebuilds : Option (List Thm) :=
  [rebuild G rs D.add, rebuild G rs D.succ, lcaseRebuild G rs, rebuild G rs D.dbl,
    rebuild G rs D.pred].mapM id

/-- The rules of the equations' proofs: the rebuildings, before the normalization's. -/
def rulesR : List NormRule :=
  [.thm 0 [], .thm 1 [], .thm 2 [bitTy, bitsTy], .thm 2 [bitTy, ordTy], .thm 3 [], .thm 4 []] ++ rs

/-- The development: the rebuildings, by induction on bitstrings, and then the equations, by
normalization with the rebuildings. -/
def development : Option (List Decl) := do
  let rbs ← rebuilds
  let ind (a : Thm) (E : Array Entry) : Option Internal.Deriv := match a.arity with
    | 0 => listInd G (consT bitTy (v 1) (v 0)) rs 256 a E
    | _ => Internal.byListInd G E 2 0 1 (consT X₀ (v 1) (v 0)) rs 256 a.ctx a.hyps (sides a).1
      (sides a).2
  develop (rbs.map (fun a ↦ (a, ind a)) ++
    lemmas.map fun a ↦ (a, fun E ↦ normH G E rulesR a.ctx [] (sides a).1 (sides a).2))

/-- The index of the first equation among the development's theorems. -/
def first : ℕ := 5

/-- The development's theorems. -/
def entries : Array Entry :=
  ((development.getD []).filterMap fun
    | .language a _ => some (Entry.language a)
    | _ => none).toArray

-- the development proves each of its theorems
#guard development.any fun ds ↦ ds.length = first + lemmas.length &&
  (Internal.checkDev G #[] ds).isSome

-- the equations are its theorems from the first index on, and the evaluation is ready there
#guard ready G entries 0 [] first
#guard !ready G entries 0 [] 0

/-- The certificate of an equation by a step of evaluation at its left side, from the theorems at
an index. -/
def byLit (j : ℕ) : ConvDeriv :=
  RoseTree.node (.base .join) [RoseTree.node (.lit j) [], RoseTree.node (.base .refl) []]

/-- Whether a step of evaluation proves an equation of closed terms, from the theorems at an
index. -/
def proves (t u : Term) (j : ℕ := first) : Bool :=
  (⟨0, [], [], Term.eq t u⟩ : Thm).convChecks G entries (byLit j)

/-- The numeral of a number. -/
def lit (k : ℕ) : Term := bitsT (num k)

/-- A definition of two arguments at numerals. -/
def bin (s : Sym) (a b : ℕ) : Term := s.call [lit a, lit b]

-- arithmetic, comparison and their compositions in one step
#guard proves (bin .add 7 9) (lit 16)
#guard proves (bin .mul 1000 1000) (lit 1000000)
#guard proves (bin .sub 50 8) (lit 42)
#guard proves (bin .sub 3 5) (lit 0)
#guard proves (bin .ltB 3 5) trueT && proves (bin .ltB 5 3) bnilT
#guard proves (bin .cmp 4 4) eqO && proves (bin .cmp 9 4) gtO
#guard proves (Sym.eqB.call [bin .add 2 3, lit 5]) trueT
#guard proves (Sym.pred.call [Sym.dbl.call [Sym.succ.call [lit 20]]]) (lit 41)

-- a false equation, the equations named at another index, and a term with a variable are
-- not proved
#guard !proves (bin .add 2 2) (lit 5)
#guard !proves (bin .add 7 9) (lit 16) 0
#guard !proves (Sym.succ.call [Term.var 0]) (lit 1)

/-- The value of a literal's numeral, by the library's definitions unfolded and normalized. -/
def valueOf (v : Val) : Option Term := value v.term

/-- Whether, at the numerals of numbers below a bound, a step of evaluation proves each
definition of two arguments, and its result is the value of the definitions unfolded and
normalized. -/
def agrees (bound : ℕ) : Bool :=
  [Sym.add, .mul, .eqB, .cmp, .ltB, .sub].all fun s ↦
    (List.range bound).all fun a ↦ (List.range bound).all fun b ↦
      match Literals.eval (bin s a b) with
      | some v => proves (bin s a b) v.term && valueOf v == value (bin s a b)
      | none => false

#guard agrees 9

end GebTests.Prototypes.FreeTopos.Literals

end
