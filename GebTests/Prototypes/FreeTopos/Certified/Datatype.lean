/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeBase
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep
public import GebTests.Prototypes.ProgramCommand
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at an atom, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`, stored in
{lit}`bootstrap/certificates/datatype-base.cert`, proves in the program extended for the datatype
language's soundness the soundness at an atom: an atom that the stage-1 typing written in Geb gives
a type, and that the reader written in Geb resolves, resolves to a term whose evaluation by the
evaluator written in Geb converges to a value related at that type.

## Main statements

* {lit}`atom_proved` — the development proves the soundness at an atom.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.Datatype

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes

/-- The development, read from its certificate. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-base.cert")

set_option doc.verso false in
/-- The development checks in the extended program and its last declaration states the soundness
at an atom, as Lean's evaluator decides. -/
evaluation_axiom proved :
    provedIn extended3 (·.1.G) decls (fun (P, S, T) ↦ atomThm P S T) = true

/-- The development proves the soundness at an atom in the extended program. -/
theorem atom_proved :
    ∃ PST, extended3 = some PST ∧ Proves PST.1.G decls (atomThm PST.1 PST.2.1 PST.2.2) :=
  provedIn_eq_true proved

end GebTests.Prototypes.FreeTopos.Certified.Datatype

end
