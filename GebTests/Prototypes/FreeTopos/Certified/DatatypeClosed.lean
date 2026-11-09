/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCata
public import GebTests.Prototypes.FreeTopos.DatatypeClosed
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeCata -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeClosed -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at every tree, proved in the internal language

The soundness of the datatype language's stage-1 compiler at every tree, without hypotheses: the
development of the discharge of the keywords the soundness at every tree takes as hypotheses,
checked after the statements of the theorems it continues from, in the order of its certificate's
search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main statements

* {lit}`sound_valid` — the soundness at every tree is valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The developments the discharge continues from, in the order of its search. -/
def before : List Internal.Decl :=
  DatatypeCata.upToCataSrc ++ DatatypeDatum.datumCase ++ DatatypeDatum.decodeCase ++
    DatatypeForms.app ++ DatatypeForms.lam ++ DatatypeForms.data ++ DatatypeForms.lists ++
    DatatypeForms.sound

/-- The development of the certificate {lit}`datatype-closed`. -/
def closed : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-closed.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom closedChecked :
    checkedAfterIn extended3 (·.1.G) before closed = true

set_option doc.verso false in
/-- The development's last declaration states the soundness at every tree without hypotheses, as
Lean's evaluator decides. -/
evaluation_axiom closedStates :
    statesLastIn extended3 closed (fun PST ↦ soundClosedThm PST.1 PST.2.1 PST.2.2) = true

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {name}`before` are valid in every model of the program. -/
theorem before_valid : m.Valid before :=
  (((((((DatatypeCata.upToCataSrc_valid h m).append (DatatypeDatum.datumCase_valid h m)).append
    (DatatypeDatum.decodeCase_valid h m)).append (DatatypeForms.app_valid h m)).append
    (DatatypeForms.lam_valid h m)).append (DatatypeForms.data_valid h m)).append
    (DatatypeForms.lists_valid h m)).append (DatatypeForms.sound_valid h m)

/-- The theorems of {lit}`datatype-closed` are valid in every model of the program. -/
theorem closed_valid : m.Valid closed :=
  DatatypeList.valid_after h (before_valid h m) closedChecked

/-- The soundness of the datatype language's stage-1 compiler at every tree, without hypotheses
({name}`soundClosedThm`), is valid in every model of the program. -/
theorem sound_valid : (soundClosedThm PST.1 PST.2.1 PST.2.2).Valid m.M PST.1.G :=
  have hl := mem_thmsOf_of_statesLastIn h closedStates
  closed_valid h m _ hl

end GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed

end
