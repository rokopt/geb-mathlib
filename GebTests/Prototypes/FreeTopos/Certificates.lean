/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeList
public import GebTests.Prototypes.FreeTopos.Expansion
public import GebTests.Prototypes.FreeTopos.Normalization

set_option doc.verso true in
/-!
# The searches of the developments of the internal language

The developments the internal language proves about the programs of the bootstrap are found by
the proofs of their modules, which search for derivations, and are stored, each as the list of its
declarations, in a file of {lit}`bootstrap/certificates/`, which the modules stating the theorems
read and check. {lit}`GebTests.Prototypes.FreeTopos.StoredWriter` runs the searches and writes
the certificates, as {lit}`scripts/certificates.sh` runs it; the search is the costly part, and is
run when the proofs or the programs change, as the bootstrap's artifacts are regenerated. A
certificate is the table of the distinct nodes of the development's tree, read by
{lit}`GebTests.Prototypes.FreeTopos.Stored`.

## Main definitions

* {lit}`searches` — the searches that find the developments, each with its name.

## Tags

internal language, development, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certificates

open Geb Geb.FreeTopos
open Internal (Decl)

/-- A search of a translated program's developments: each development's declarations with the name
of its certificate, where the program translates and every lemma is proved. -/
def inProgram {α : Type} (program : Option α)
    (search : α → Except String (List (String × List Decl))) :
    Except String (List (String × List Decl)) :=
  match program with
  | some P => search P
  | none => .error "the program does not translate"

/-- A search of developments: the names of the certificates it continues from, and, given their
theorems in that order, each development's declarations with the name of its certificate, or the
reason a lemma is not proved. -/
abbrev Search :=
  List String × (List (List Internal.Thm) → Except String (List (String × List Decl)))

set_option compiler.extract_closed false in
/-- The searches of the developments with certificates, each with its name, after those whose
certificates it continues from. Closed terms are not extracted, so that each search runs when it
is timed rather than when the program starts. -/
def searches : List (String × Search) :=
  [("weakening", ([], fun _ ↦ inProgram Weakening.program fun P ↦
      (Weakening.certificate P).map fun ds ↦ [("weakening", ds)])),
    ("substitution", ([], fun _ ↦ inProgram Substitution.program fun P ↦
      (Substitution.certificate P).map fun ds ↦ [("substitution", ds)])),
    ("tree-cases", ([], fun _ ↦ inProgram TreeCases.program fun P ↦
      (TreeCases.certificate P).map fun ds ↦ [("tree-cases", ds)])),
    ("expansion", ([], fun _ ↦ inProgram Expansion.program fun P ↦
      (Expansion.certificate P).map fun ds ↦ [("expansion", ds)])),
    ("normalization", ([], fun _ ↦ inProgram Normalization.extended fun (P, S) ↦
      Normalization.certificates P S)),
    ("datatype-base", ([], fun _ ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
      Datatypes.certificates P S T)),
    ("datatype-atom", (["datatype-base"], fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
      Datatypes.atomCertificates P S T dss.flatten)),
    ("datatype-list", (["datatype-base", "datatype-atom"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.listCertificates P S T dss.flatten))]

end GebTests.Prototypes.FreeTopos.Certificates

end
