/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeMembers
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramAccepted

set_option doc.verso true in
/-!
# The definitions of the type of trees and of a datatype's, in an accepted program

The soundness of the forms the datatype language's stage-1 compiler accepts
({lit}`DatatypeProgramAccepted.program_sound_accepted`) relates each definition to its type. At
the type of trees and at a datatype the relation is a fact about the evaluator alone
({lit}`DatatypeMembers.globRel_tree`, {lit}`DatatypeMembers.globRel_data`), so the soundness
states, of the programs the compiler accepts under the hypotheses it keeps: a definition of the
type of trees evaluates to a tree's quotation, and a definition of a datatype's type to the
quotation of a member of the datatype, by the markers of the typing environment the typing ends
in.

## Main statements

* {lit}`accepted_tree` — a definition of the type of trees evaluates to a tree's quotation.
* {lit}`accepted_data` — a definition of a datatype's type evaluates to the quotation of a
  member of the datatype.

## Tags

internal language, datatypes, kernel, evaluator, compiler, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMembers

open Geb
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements (Conv Level)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion (names)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses (HypFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror
open GebTests.Prototypes.FreeTopos.Certified.DatatypeEntry (Accepts)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeMembers (globRel_tree globRel_data)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramAccepted (program_sound_accepted)

variable (es : List Kernel.Tree) (hacc : Accepts es) (hplain : hypFns.PlainOk es)
  (hmark : hypFns.MarkersOk es) (hnames : hypFns.NamesOk (hypFns.msK es))
  (hctors : hypFns.CtorsOk (hypFns.msK es)) (hforms : hypFns.FormsOk es)

include hacc hplain hmark hnames hctors hforms

/-- In a program the compiler accepts, under the hypotheses the soundness keeps
({name}`program_sound_accepted`), a definition the typing environment gives the type of trees
has an index among the reader's names, at which the reader's terms have one whose evaluation
converges to a tree's quotation. -/
theorem accepted_tree {n : Kernel.Tree}
    (hn : (evalFns.isSome
      (evalFns.lookupName n (evalFns.envDefs (passFns.run es).1))).label ≠ 0)
    {ts : List Kernel.Tree}
    (hA : evalFns.get (evalFns.lookupName n (evalFns.envDefs (passFns.run es).1)) =
      RoseTree.node Kernel.Label.tyTree ts) :
    ∃ i, evalFns.indexOf n (names passFns es) = evalFns.just i ∧
      ∃ d, evalFns.nth (passFns.terms es) i = evalFns.just d ∧
        Conv evalFns.just (fun k ↦ (Level evalFns (passFns.terms es) k).1 [] d) fun w ↦
          ∃ t, w = evalFns.valQuote t :=
  globRel_tree (program_sound_accepted es hacc hplain hmark hnames hctors hforms).1 hn hA

/-- In a program the compiler accepts, under the hypotheses the soundness keeps
({name}`program_sound_accepted`), a definition the typing environment gives a datatype's type
has an index among the reader's names, at which the reader's terms have one whose evaluation
converges to the quotation of a member of the datatype, by the markers of the typing
environment. -/
theorem accepted_data {n : Kernel.Tree}
    (hn : (evalFns.isSome
      (evalFns.lookupName n (evalFns.envDefs (passFns.run es).1))).label ≠ 0)
    {a : Kernel.Tree} {ts : List Kernel.Tree}
    (hA : evalFns.get (evalFns.lookupName n (evalFns.envDefs (passFns.run es).1)) =
      RoseTree.node 5 (a :: ts)) :
    ∃ i, evalFns.indexOf n (names passFns es) = evalFns.just i ∧
      ∃ d, evalFns.nth (passFns.terms es) i = evalFns.just d ∧
        Conv evalFns.just (fun k ↦ (Level evalFns (passFns.terms es) k).1 [] d) fun w ↦
          ∃ t, w = evalFns.valQuote t ∧
            (evalFns.memberOf (evalFns.envMs (passFns.run es).1)
              (RoseTree.node 1 a.children) t).label ≠ 0 :=
  globRel_data (program_sound_accepted es hacc hplain hmark hnames hctors hforms).1 hn hA

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMembers

end
