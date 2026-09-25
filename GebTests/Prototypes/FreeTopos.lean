/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos -- shake: keep
public meta import Geb.Prototypes.FreeTopos -- shake: keep

set_option doc.verso true in
/-!
# The partial Horn theory of an elementary topos

Every axiom of {name}`Geb.FreeTopos.theory` has its variables in its context and sides of one
sort. The checker {name}`Geb.PartialHorn.check` accepts certificates of a theorem with a
hypothesis, of the instance of an axiom at a compound term, of the uniqueness of recursion from
the natural numbers object, which is induction, and of an equation of a characteristic map; and
rejects certificates that instantiate an axiom at a term of the wrong sort, cite a missing
hypothesis, compose equations whose middle terms differ, apply strictness to a variable, or
prove a hypothesis other than the instance the axiom requires.

## Main definitions

* {lit}`idx` — the index of an axiom by its block and its position there.
* {lit}`cHyp`, {lit}`cRefl`, {lit}`cSymm`, {lit}`cTrans`, {lit}`cCong`, {lit}`cStrict`,
  {lit}`cAx` — certificates by rule.
* {lit}`natIdRec` — the certificate that recursion with zero and the successor is the identity.

## Tags

elementary topos, partial Horn logic, proof certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts

/-- The index of the axiom at position {lit}`k` of the block after {lit}`before`. -/
def idx (before : List (List Seq)) (k : ℕ) : ℕ := (before.map List.length).sum + k

/-- The certificate of a hypothesis, by index. -/
def cHyp (i : ℕ) : Tree := RoseTree.node Rule.hyp [RoseTree.node i []]

/-- The certificate that a variable is defined. -/
def cRefl (i : ℕ) : Tree := RoseTree.node Rule.refl [RoseTree.node i []]

/-- The certificate of symmetry. -/
def cSymm (p : Tree) : Tree := RoseTree.node Rule.symm [p]

/-- The certificate of transitivity. -/
def cTrans (p q : Tree) : Tree := RoseTree.node Rule.trans [p, q]

/-- The certificate of congruence at a defined application. -/
def cCong (d : Tree) (ps : List Tree) : Tree := RoseTree.node Rule.cong (d :: ps)

/-- The certificate of strictness at an argument's position. -/
def cStrict (j : ℕ) (p : Tree) : Tree := RoseTree.node Rule.strict [RoseTree.node j [], p]

/-- The certificate of an axiom's instance: its index, the terms, their definedness, and the
instances of its hypotheses. -/
def cAx (j : ℕ) (ts ds hs : List Tree) : Tree :=
  RoseTree.node Rule.ax (RoseTree.node j [] :: ts ++ ds ++ hs)

/-- The checker in the theory, citing no theorems. -/
def chk (c : Tree) (Γ : List ℕ) (H : List Eqn) : Option Eqn := check theory [] c Γ H

/-- Whether both sides of an equation have one sort in a context. -/
def wellSorted (Γ : List ℕ) (q : Eqn) : Bool :=
  match sortOf sig Γ q.lhs, sortOf sig Γ q.rhs with
  | some s, some t => s == t
  | _, _ => false

-- every axiom is in scope and well sorted
#guard axioms.all fun a ↦ a.Scoped && (a.concl :: a.hyps).all (wellSorted a.ctx)

-- the domain of an arrow is defined
#guard chk (cAx 0 [x 0] [cRefl 0] []) [arr] [] = some (dfd (dom (x 0)))

/-- The certificate that a composite is defined, from the hypothesis that its arrows compose. -/
def compDfd : Tree := cAx 4 [x 0, x 1] [cRefl 0, cRefl 1] [cHyp 0]

/-- The hypothesis that {lit}`x 1` and {lit}`x 0` compose. -/
def composable : Eqn := ⟨cod (x 1), dom (x 0)⟩

-- a theorem with a hypothesis: the domain of a composite
#guard chk (cAx 5 [x 0, x 1] [cRefl 0, cRefl 1] [compDfd]) [arr, arr] [composable] =
  some ⟨dom (comp (x 0) (x 1)), dom (x 1)⟩

-- a substitution: the right identity law at a composite
#guard chk (cAx 10 [comp (x 0) (x 1)] [compDfd] []) [arr, arr] [composable] =
  some ⟨comp (comp (x 0) (x 1)) (idt (dom (comp (x 0) (x 1)))), comp (x 0) (x 1)⟩

/-- The blocks before the natural numbers object's. -/
def beforeNat : List (List Seq) := [categoryAxioms, terminalAxioms, productAxioms,
  equalizerAxioms, initialAxioms, coproductAxioms, coequalizerAxioms, exponentialAxioms,
  classifierAxioms]

/-- The equation {lit}`dom zeroN = one`. -/
def zDom : Tree := cAx (idx beforeNat 0) [] [] []

/-- The equation {lit}`cod zeroN = nat`. -/
def zCod : Tree := cAx (idx beforeNat 1) [] [] []

/-- The equation {lit}`dom succ = nat`. -/
def sDom : Tree := cAx (idx beforeNat 2) [] [] []

/-- The equation {lit}`cod succ = nat`. -/
def sCod : Tree := cAx (idx beforeNat 3) [] [] []

/-- Zero is defined. -/
def zDfd : Tree := cStrict 0 zDom

/-- The successor is defined. -/
def sDfd : Tree := cStrict 0 sDom

/-- The natural numbers object is defined. -/
def natDfd : Tree := cTrans (cSymm zCod) zCod

/-- The identity of the natural numbers object is defined. -/
def idNatDfd : Tree := cAx 2 [nat] [natDfd] []

/-- Recursion with zero and the successor is defined. -/
def recDfd : Tree :=
  cAx (idx beforeNat 7) [zeroN, succ] [zDfd, sDfd]
    [zDom, cTrans zCod (cSymm sDom), cTrans sDom (cSymm sCod)]

/-- The left identity law at an arrow {lit}`f` whose codomain is proved equal to {lit}`b` by
{lit}`hcod`, with {lit}`hf` its definedness: {lit}`comp (idt b) f = f`. -/
def leftId (f hf hcod : Tree) : Tree :=
  let law := cAx 11 [f] [hf] []
  cTrans (cSymm (cCong law [cCong (cStrict 0 law) [hcod], hf])) law

/-- The right identity law at an arrow {lit}`f` whose domain is proved equal to {lit}`a` by
{lit}`hdom`, with {lit}`hf` its definedness: {lit}`comp f (idt a) = f`. -/
def rightId (f hf hdom : Tree) : Tree :=
  let law := cAx 10 [f] [hf] []
  cTrans (cSymm (cCong law [hf, cCong (cStrict 1 law) [hdom]])) law

/-- Induction: recursion with zero and the successor is the identity of the natural numbers
object, by the uniqueness of recursion. -/
def natIdRec : Tree :=
  cAx (idx beforeNat 12) [zeroN, succ, idt nat] [zDfd, sDfd, idNatDfd]
    [recDfd, cAx 8 [nat] [natDfd] [], leftId zeroN zDfd zCod,
      cTrans (leftId succ sDfd sCod) (cSymm (rightId succ sDfd sDom))]

#guard chk (leftId zeroN zDfd zCod) [] [] = some ⟨comp (idt nat) zeroN, zeroN⟩

#guard chk natIdRec [] [] = some ⟨idt nat, natRec zeroN succ⟩

/-- The blocks before the classifier's. -/
def beforeClassifier : List (List Seq) := [categoryAxioms, terminalAxioms, productAxioms,
  equalizerAxioms, initialAxioms, coproductAxioms, coequalizerAxioms, exponentialAxioms]

-- a characteristic map: the square of a monomorphism commutes
#guard chk (cAx (idx beforeClassifier 7) [x 0] [cRefl 0] [cHyp 0]) [arr] [dfd (chi (x 0))] =
  some ⟨comp (chi (x 0)) (x 0), comp tru (bang (dom (x 0)))⟩

-- an axiom instantiated at a term of the wrong sort
#guard chk (cAx 2 [x 0] [cRefl 0] []) [arr] [] = none

-- a missing hypothesis
#guard chk (cHyp 3) [arr] [] = none

-- a transitivity whose middle terms differ
#guard chk (cTrans (cRefl 0) (cRefl 1)) [arr, arr] [] = none

-- strictness at a variable
#guard chk (cStrict 0 (cRefl 0)) [arr] [] = none

-- a hypothesis other than the instance the axiom requires
#guard chk compDfd [arr, arr] [⟨dom (x 0), cod (x 1)⟩] = none

end GebTests.Prototypes.FreeTopos

end
