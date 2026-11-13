/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Chain
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated
public meta import GebTests.Prototypes.FreeTopos.Certified.Chain -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The passes' runs over a program's forms, proved in the internal language

The developments the soundness of a whole program of the datatype language continues from, and
those of the runs of the compiler's passes over a program's forms: the typing's runs, checked
after the base's theorems, and the runs of the expansion, the reader and the kernel's check with
the invariants the reading of a definition preserves, each checked after the theorems of those
before it, in the order of their search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main definitions

* {lit}`before` — the developments the soundness of a whole program continues from.
* {lit}`runs`, {lit}`upToRuns` — the developments of the passes' runs, and all with them.

## Main statements

* {lit}`upToRuns_valid` — their theorems are valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The development of the certificate {lit}`datatype-base`. -/
def base : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-base.cert")

/-- The development of the certificate {lit}`datatype-program`. -/
def program : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the base's theorems, as Lean's
evaluator decides. -/
evaluation_axiom programChecked :
    checkedAfterIn extended3 (·.1.G) base program = true

/-- The developments the soundness of a whole program continues from, in the order of its
search. -/
def before : List Internal.Decl :=
  DatatypeGenerated.upToCtorNest ++ program ++ DatatypeClosed.closed ++ DatatypeForms.app ++
    DatatypeForms.lam

/-- The developments of the runs of the passes over a program's forms, in the order of their
search. -/
def runs : List (List Internal.Decl) :=
  [ofText (include_str "../../../../bootstrap/certificates/datatype-program-read.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-expand.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-prefix.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-out-step.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-out.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-lists.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-lookup.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-kernel.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-inv.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-plain.cert")]

set_option doc.verso false in
/-- Each of the developments checks in the extended program, after the theorems of those it
continues from and of those before it, as Lean's evaluator decides. -/
evaluation_axiom runsChecked :
    checkedChainIn extended3 (·.1.G) runs before = true

/-- With the passes' runs. -/
def upToRuns : List Internal.Decl := before ++ runs.flatten

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {lit}`datatype-base` are valid in every model of the program. -/
theorem base_valid : m.Valid base :=
  (DatatypeList.decls_valid h m).left.left

/-- The theorems of {lit}`datatype-program` are valid in every model of the program. -/
theorem program_valid : m.Valid program :=
  DatatypeList.valid_after h (base_valid h m) programChecked

/-- The theorems of {name}`before` are valid in every model of the program. -/
theorem before_valid : m.Valid before :=
  ((((DatatypeGenerated.upToCtorNest_valid h m).append (program_valid h m)).append
    (DatatypeClosed.closed_valid h m)).append (DatatypeForms.app_valid h m)).append
    (DatatypeForms.lam_valid h m)

/-- The theorems of {name}`upToRuns` are valid in every model of the program. -/
theorem upToRuns_valid : m.Valid upToRuns :=
  ProgramModel.Valid.chain h runs (before_valid h m) runsChecked

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram

end
