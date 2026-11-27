/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Weakening
public import Geb.Prototypes.Kernel
public meta import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep
public meta import Geb.Prototypes.Kernel -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Tests of the case analysis of a member of a datatype

A program of recognizers written as the expansion of the datatype language writes them
({lit}`bootstrap/recognize.geb`), of a datatype of two constructors of no field and of one, of a
datatype of a constructor of two fields, and of a datatype whose constructor takes one field and
then the remaining children; and theorems about the members of each, proved by
{name}`Geb.FreeTopos.Tactics.byMemberCases` and checked.

## Main definitions

* {lit}`text`, {lit}`program` — the program and its translation.
* {lit}`development` — the lemmas of trees, the connectives' rules and the theorems.

## Tags

internal language, datatype, recognizer, case analysis, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Members

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Translation (baseRules)
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry ConvDeriv ConvDecl)
open scoped FinEnum

/-- The program: for each datatype its recognizer, the fold whose value at a node is the node of
the bit of its membership, the test of membership as a tree, and a function that rebuilds a
member from its label and children. -/
def text : String := "
(def Opt.member
  (lam ((t T))
    (child
      (fold T
        (lam ((l T) (r (List T)))
          (let n T (node 0 r)
            (node 0
              (cons (if (if (eq l 0) (eq (arity n) 0) (if (eq l 1) (eq (arity n) 1) 0)) 1 0)
                (nil T)))))
        t)
      0)))
(def Opt.is (lam ((x T)) (if (Opt.member x) 1 0)))
(def Opt.rebuild
  (lam ((x T)) (if (eq (label x) 0) (node 0 (nil T)) (node 1 (cons (child x 0) (nil T))))))
(def Two.member
  (lam ((t T))
    (child
      (fold T
        (lam ((l T) (r (List T)))
          (let n T (node 0 r)
            (node 0 (cons (if (if (eq l 0) (eq (arity n) 2) 0) 1 0) (nil T)))))
        t)
      0)))
(def Two.is (lam ((x T)) (if (Two.member x) 1 0)))
(def Two.rebuild (lam ((x T)) (node 0 (cons (child x 0) (cons (child x 1) (nil T))))))
(def Rest.member
  (lam ((t T))
    (child
      (fold T
        (lam ((l T) (r (List T)))
          (let n T (node 0 r)
            (node 0 (cons (if (if (eq l 0) (lt 1 (add (arity n) 1)) 0) 1 0) (nil T)))))
        t)
      0)))
(def Rest.is (lam ((x T)) (if (Rest.member x) 1 0)))
(def Rest.label (lam ((x T)) (label x)))
"

/-- The translated program. -/
def program : Option Prog := do
  let ds ← Kernel.readProgram text.toList
  prog? ds fun name ↦ ((defIndex ds name.toList).getD 0)

/-- The rules of the reduction with the successor kept folded. -/
def succFolded (P : Prog) : List NormRule := baseRules ++ [.unitVar, .deltaBelow P.o [D.succ]]

/-- The theorem that a function of the program equals another at the members of a datatype: at
a tree for which the datatype's test of membership is the tree of label one. -/
def atMembers (P : Prog) (is f : String) (g : Term → Term) : Internal.Thm :=
  ⟨0, [treeTy], [Term.eq (Term.app (call (P.idx is) [] []) (v 0)) (leafT (numeral 1))],
    Term.eq (Term.app (call (P.idx f) [] []) (v 0)) (g (v 0))⟩

/-- The proof of a theorem about the members of a datatype by cases on its constructors, each a
number of fields and whether a last field takes the remaining children, each case by reduction. -/
def byCases (P : Prog) (ix : String → ℕ) (E : Array Entry) (cs : List (ℕ × Bool))
    (a : Internal.Thm) : Option ConvDeriv :=
  let rs := baseNorm P
  let refute := refuteMember P.G E 0 P.o logicBase rs
  let p := byMode .full P.G E 0 (.thm (ix "lambek") [] :: rs)
  let clause (l c : ℕ) : Internal.Prover := match cs[l]? with
    | some (k, false) =>
      byFixed P.G E 0 P.o logicBase rs (succFolded P) k (Nat.log2 (k + 1) + 1) p c
    | some (k, true) => byRest P.G E 0 P.o logicBase rs k p c
    | none => refute
  byMemberCases P.G P.o logicBase (ix "lambek") 0 0 (Nat.log2 cs.length + 1) clause refute
    a.ctx a.hyps (sides a).1 (sides a).2

/-- The development: the lemmas of trees, the connectives' rules, and a theorem about the members
of each datatype, the first datatype's by cases on the constructors {lit}`cs`. -/
def development (P : Prog) (cs : List (ℕ × Bool)) : List Step :=
  let opt := atMembers P "Opt.is" "Opt.rebuild" id
  let two := atMembers P "Two.is" "Two.rebuild" id
  let rest := atMembers P "Rest.is" "Rest.label" fun _ ↦ leafT bnilT
  unfoldingThms P ++ logicThms P ++
    [step "opt" opt fun ix E ↦ byCases P ix E cs opt,
      step "two" two fun ix E ↦ byCases P ix E [(2, false)] two,
      step "rest" rest fun ix E ↦ byCases P ix E [(1, true)] rest]

/-- Whether the development by cases on the first datatype's constructors {lit}`cs` is found and
checks. -/
def proved (cs : List (ℕ × Bool)) : Bool := program.any fun P ↦
  match developNamed (development P cs) with
  | .ok ds => Internal.checkConvThms P.G ds #[]
  | .error _ => false

-- every theorem is proved, at the constructors of no field and of one, of two fields, and of one
-- field before the remaining children, and the development checks
#guard proved [(0, false), (1, false)]

-- cases that are not those of the datatype's constructors prove nothing: a constructor missing,
-- a constructor of another number of fields, and a constructor taking the remaining children
#guard !proved [(0, false)]
#guard !proved [(0, false), (2, false)]
#guard !proved [(1, false), (1, false)]

end GebTests.Prototypes.FreeTopos.Members

end
