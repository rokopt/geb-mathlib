/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Logic in the internal language

The connectives defined from equality, as in a local set theory ({cite}`RuizHernandezSolorzano2021`,
§3.2): truth is the equality of the element of the terminal object with itself, a conjunction the
equality of the pair of its formulas with the pair of truths, an implication the equality of the
conjunction with the antecedent, a universal quantification the equality of the abstraction of
its formula with the abstraction of truth, and falsity the universal quantification of every
formula. Their introduction and elimination rules are theorems of the internal language with
hypotheses, derived by the checker's rules: rewriting with a hypothesis, the cut, rewriting a
formula before or after its proof, propositional and function extensionality, and the
application of an earlier theorem. The theorems of addition and appending proved by induction
with the step of their recursions are proved again by induction with the induction hypothesis.

## Main definitions

* {lit}`tt`, {lit}`andT`, {lit}`impT`, {lit}`allT`, {lit}`ffT` — the connectives.
* {lit}`theorems` — the rules and the inductions, each with its proof.
* {lit}`development` — the development of their derivations.

## References

* {cite}`RuizHernandezSolorzano2021`

## Tags

internal language, local set theory, derivation, induction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalLogic

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv Rule byNatIndHyp byListIndHyp checkThms)

/-- Truth: the equality of the element of the terminal object with itself. -/
def tt : Term := Term.eq Term.star Term.star

/-- Conjunction: the pair of the formulas is the pair of truths. -/
def andT (p q : Term) : Term := Term.eq (Term.pair p q) (Term.pair tt tt)

/-- Implication: the conjunction is the antecedent. -/
def impT (p q : Term) : Term := Term.eq (andT p q) p

/-- Universal quantification over a type: the abstraction of the formula is the abstraction of
truth. -/
def allT (a : Tree) (p : Term) : Term := Term.eq (Term.lam a p) (Term.lam a tt)

/-- Falsity: every formula. -/
def ffT : Term := allT omega (Term.var 0)

/-- A derivation's node of a rule. -/
def nd (l : Rule) (cs : List Deriv := []) : Deriv := RoseTree.node l cs

/-- The proof of truth: its sides are one term. -/
def trueI : Deriv := nd .join [nd .refl, nd .refl]

/-- The proof of the equality of a hypothesis of an index with truth: truth under it, and it
under truth. -/
def eqTrue (i : ℕ) : Deriv := nd .propExt [trueI, nd (.hyp i)]

/-- The proof of a formula {lit}`φ` that the rewriting {lit}`d` takes to truth. -/
def byTrue (d : Deriv) : Deriv := nd .conv [d, trueI]

/-- The formulas of the context of two formulas, the outer first. -/
def p : Term := Term.var 1

/-- The inner formula of the context of two formulas. -/
def q : Term := Term.var 0

/-- The theorems, each with its proof from the theorems before it. -/
def theorems : List (Thm × (Array Thm → Option Deriv)) := [
  -- 0: truth
  (⟨0, [], [], tt⟩, fun _ ↦ some trueI),
  -- 1: conjunction introduction, each formula rewritten to truth
  (⟨0, [omega, omega], [p, q], andT p q⟩, fun _ ↦ some <|
    nd (.cut (Term.eq p tt)) [eqTrue 0, nd (.cut (Term.eq q tt)) [eqTrue 1,
      nd .join [nd .cong [nd (.rwHyp 2 false), nd (.rwHyp 3 false)], nd .refl]]]),
  -- 2: conjunction elimination, the first component of the pair
  (⟨0, [omega, omega], [andT p q], p⟩, fun _ ↦ some <|
    nd (.convFrom (Term.fst (Term.pair p q))) [nd .fstPair,
      byTrue (nd .trans [nd .cong [nd (.rwHyp 0 false)], nd .fstPair])]),
  -- 3: conjunction elimination, the second component of the pair
  (⟨0, [omega, omega], [andT p q], q⟩, fun _ ↦ some <|
    nd (.convFrom (Term.snd (Term.pair p q))) [nd .sndPair,
      byTrue (nd .trans [nd .cong [nd (.rwHyp 0 false)], nd .sndPair])]),
  -- 4: implication elimination, the conjunction rewritten to the antecedent and so to truth
  (⟨0, [omega, omega], [impT p q, p], q⟩, fun _ ↦ some <|
    nd (.cut (Term.eq p tt)) [eqTrue 1, nd (.apply 3 [] [q, p])
      [byTrue (nd .trans [nd (.rwHyp 0 false), nd (.rwHyp 2 false)])]]),
  -- 5: implication introduction, of a formula from itself
  (⟨0, [omega], [], impT (Term.var 0) (Term.var 0)⟩, fun _ ↦ some <|
    nd .propExt [nd (.apply 2 [] [Term.var 0, Term.var 0]) [nd (.hyp 0)],
      nd (.apply 1 [] [Term.var 0, Term.var 0]) [nd (.hyp 0), nd (.hyp 0)]]),
  -- 6: universal elimination, the abstraction applied to the element
  (⟨1, [x 0, exp (x 0) omega], [allT (x 0) (Term.app (Term.var 2) (Term.var 0))],
      Term.app (Term.var 1) (Term.var 0)⟩, fun _ ↦ some <|
    nd (.convFrom (Term.app (Term.lam (x 0) (Term.app (Term.var 2) (Term.var 0))) (Term.var 0)))
      [nd .beta, byTrue (nd .trans [nd .cong [nd (.rwHyp 0 false), nd .refl], nd .beta])]),
  -- 7: universal introduction, of reflexivity, by function extensionality
  (⟨1, [], [], allT (x 0) (Term.eq (Term.var 0) (Term.var 0))⟩, fun _ ↦ some <|
    nd .funExt [nd .conv [nd .cong [nd .beta, nd .beta], nd .propExt [trueI, trueI]]]),
  -- 8: falsity elimination, universal elimination at the formula
  (⟨0, [omega], [ffT], Term.var 0⟩, fun _ ↦ some <|
    nd (.convFrom (Term.app (Term.lam omega (Term.var 0)) (Term.var 0))) [nd .beta,
      nd (.apply 6 [omega] [Term.var 0, Term.lam omega (Term.var 0)])
        [nd .conv [nd .cong [nd .cong [nd .beta], nd .refl], nd (.hyp 0)]]]),
  -- 9: zero is a left unit of addition, by induction with the induction hypothesis
  (⟨0, [nat], [], Term.eq (addT zeroT (Term.var 0)) (Term.var 0)⟩,
    fun E ↦ byNatIndHyp G E 0 2 3 (InternalDerivation.eqns ++ [.delta 1]) 64 [nat] []
      (addT zeroT (Term.var 0)) (Term.var 0)),
  -- 10: the empty list is a right unit of appending, by induction with the induction hypothesis
  (⟨1, [L], [], Term.eq (appendT (Term.var 0) nilT) (Term.var 0)⟩,
    fun E ↦ byListIndHyp G E 1 0 1 (InternalDerivation.eqns ++ [.delta 0]) 64 [L] []
      (appendT (Term.var 0) nilT) (Term.var 0))]

/-- The development: each theorem with its derivation, from those before it. -/
def development : Option (List (Thm × Deriv)) :=
  (theorems.foldl (fun acc (a, p) ↦ acc.bind fun (E, ds) ↦
    (p E).map fun d ↦ (E.push a, ds ++ [(a, d)])) (some (#[], []))).map Prod.snd

-- every theorem is proved, and the development checks
#guard development.any fun ds ↦ ds.length == 11 && checkThms G ds #[]

end GebTests.Prototypes.FreeTopos.InternalLogic

end
