/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos -- shake: keep
public meta import Geb.Prototypes.FreeTopos -- shake: keep
public import Geb.Prototypes.PartialHorn.Development
public meta import Geb.Prototypes.PartialHorn.Development -- shake: keep

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
#guard chk (Cert.ax 0 [x 0] [Cert.refl 0] []) [arr] [] = some (dfd (dom (x 0)))

/-- The certificate that a composite is defined, from the hypothesis that its arrows compose. -/
def compDfd : Tree := Cert.ax 4 [x 0, x 1] [Cert.refl 0, Cert.refl 1] [Cert.hyp 0]

/-- The hypothesis that {lit}`x 1` and {lit}`x 0` compose. -/
def composable : Eqn := ⟨cod (x 1), dom (x 0)⟩

-- a theorem with a hypothesis: the domain of a composite
#guard chk (Cert.ax 5 [x 0, x 1] [Cert.refl 0, Cert.refl 1] [compDfd]) [arr, arr] [composable] =
  some ⟨dom (comp (x 0) (x 1)), dom (x 1)⟩

-- a substitution: the right identity law at a composite
#guard chk (Cert.ax 10 [comp (x 0) (x 1)] [compDfd] []) [arr, arr] [composable] =
  some ⟨comp (comp (x 0) (x 1)) (idt (dom (comp (x 0) (x 1)))), comp (x 0) (x 1)⟩

/-- The blocks before the natural numbers object's. -/
def beforeNat : List (List Seq) := [categoryAxioms, terminalAxioms, productAxioms,
  equalizerAxioms, initialAxioms, coproductAxioms, coequalizerAxioms, exponentialAxioms,
  classifierAxioms]

/-- The equation {lit}`dom zeroN = one`. -/
def zDom : Tree := Cert.ax (idx beforeNat 0) [] [] []

/-- The equation {lit}`cod zeroN = nat`. -/
def zCod : Tree := Cert.ax (idx beforeNat 1) [] [] []

/-- The equation {lit}`dom succ = nat`. -/
def sDom : Tree := Cert.ax (idx beforeNat 2) [] [] []

/-- The equation {lit}`cod succ = nat`. -/
def sCod : Tree := Cert.ax (idx beforeNat 3) [] [] []

/-- Zero is defined. -/
def zDfd : Tree := Cert.strict 0 zDom

/-- The successor is defined. -/
def sDfd : Tree := Cert.strict 0 sDom

/-- The natural numbers object is defined. -/
def natDfd : Tree := Cert.trans (Cert.symm zCod) zCod

/-- The identity of the natural numbers object is defined. -/
def idNatDfd : Tree := Cert.ax 2 [nat] [natDfd] []

/-- Recursion with zero and the successor is defined. -/
def recDfd : Tree :=
  Cert.ax (idx beforeNat 7) [zeroN, succ] [zDfd, sDfd]
    [zDom, Cert.trans zCod (Cert.symm sDom), Cert.trans sDom (Cert.symm sCod)]

/-- The left identity law at an arrow {lit}`f` whose codomain is proved equal to {lit}`b` by
{lit}`hcod`, with {lit}`hf` its definedness: {lit}`comp (idt b) f = f`. -/
def leftId (f hf hcod : Tree) : Tree :=
  let law := Cert.ax 11 [f] [hf] []
  Cert.trans (Cert.symm (Cert.cong law [Cert.cong (Cert.strict 0 law) [hcod], hf])) law

/-- The right identity law at an arrow {lit}`f` whose domain is proved equal to {lit}`a` by
{lit}`hdom`, with {lit}`hf` its definedness: {lit}`comp f (idt a) = f`. -/
def rightId (f hf hdom : Tree) : Tree :=
  let law := Cert.ax 10 [f] [hf] []
  Cert.trans (Cert.symm (Cert.cong law [hf, Cert.cong (Cert.strict 1 law) [hdom]])) law

/-- Induction: recursion with zero and the successor is the identity of the natural numbers
object, by the uniqueness of recursion. -/
def natIdRec : Tree :=
  Cert.ax (idx beforeNat 12) [zeroN, succ, idt nat] [zDfd, sDfd, idNatDfd]
    [recDfd, Cert.ax 8 [nat] [natDfd] [], leftId zeroN zDfd zCod,
      Cert.trans (leftId succ sDfd sCod) (Cert.symm (rightId succ sDfd sDom))]

#guard chk (leftId zeroN zDfd zCod) [] [] = some ⟨comp (idt nat) zeroN, zeroN⟩

#guard chk natIdRec [] [] = some ⟨idt nat, natRec zeroN succ⟩

/-- The blocks before the classifier's. -/
def beforeClassifier : List (List Seq) := [categoryAxioms, terminalAxioms, productAxioms,
  equalizerAxioms, initialAxioms, coproductAxioms, coequalizerAxioms, exponentialAxioms]

-- a characteristic map: the square of a monomorphism commutes
#guard chk (Cert.ax (idx beforeClassifier 7) [x 0] [Cert.refl 0] [Cert.hyp 0]) [arr]
    [dfd (chi (x 0))] =
  some ⟨comp (chi (x 0)) (x 0), comp tru (bang (dom (x 0)))⟩

-- an axiom instantiated at a term of the wrong sort
#guard chk (Cert.ax 2 [x 0] [Cert.refl 0] []) [arr] [] = none

-- a missing hypothesis
#guard chk (Cert.hyp 3) [arr] [] = none

-- a transitivity whose middle terms differ
#guard chk (Cert.trans (Cert.refl 0) (Cert.refl 1)) [arr, arr] [] = none

-- strictness at a variable
#guard chk (Cert.strict 0 (Cert.refl 0)) [arr] [] = none

-- a hypothesis other than the instance the axiom requires
#guard chk compDfd [arr, arr] [⟨dom (x 0), cod (x 1)⟩] = none

end GebTests.Prototypes.FreeTopos

end
