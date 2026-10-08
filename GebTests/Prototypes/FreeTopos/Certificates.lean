/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

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

set_option compiler.extract_closed false in
/-- The searches of the developments with certificates, each with its name. Closed terms are not
extracted, so that each search runs when it is timed rather than when the program starts. -/
def searches : List (String × (Unit → Except String (List (String × List Decl)))) :=
  [("weakening", fun _ ↦ inProgram Weakening.program fun P ↦
      (Weakening.certificate P).map fun ds ↦ [("weakening", ds)]),
    ("substitution", fun _ ↦ inProgram Substitution.program fun P ↦
      (Substitution.certificate P).map fun ds ↦ [("substitution", ds)]),
    ("tree-cases", fun _ ↦ inProgram TreeCases.program fun P ↦
      (TreeCases.certificate P).map fun ds ↦ [("tree-cases", ds)]),
    ("expansion", fun _ ↦ inProgram Expansion.program fun P ↦
      (Expansion.certificate P).map fun ds ↦ [("expansion", ds)]),
    ("normalization", fun _ ↦ inProgram Normalization.extended fun (P, S) ↦
      Normalization.certificates P S)]

end GebTests.Prototypes.FreeTopos.Certificates

end
