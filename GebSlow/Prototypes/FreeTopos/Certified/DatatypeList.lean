/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Datatype
public meta import GebTests.Prototypes.FreeTopos.Certified.Datatype -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeList
public meta import GebTests.Prototypes.FreeTopos.DatatypeList -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at the keywords' forms, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.DatatypeList`, stored in
{lit}`bootstrap/certificates/datatype-list.cert` after the base's and the atom's
({lit}`GebTests.Prototypes.FreeTopos.Certified.Datatype`), proves in the program extended for the
datatype language's soundness the soundness at the keywords' forms, one keyword at a time, given
the soundness at their elements, the binding of a name last. Lean's evaluator takes hours to
decide the check, which is therefore among the slow checks rather than the tests.

## Main statements

* {lit}`let_proved` — the developments prove the soundness at a binding of a name.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebSlow.Prototypes.FreeTopos.Certified.DatatypeList

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Certified

/-- The developments, the soundness at the keywords' forms after the base's and the atom's. -/
def decls : List Internal.Decl :=
  Datatype.decls ++ ofText (include_str "../../../../bootstrap/certificates/datatype-list.cert")

set_option doc.verso false in
/-- The developments check in the extended program and the last declaration states the soundness
at a binding of a name, as Lean's evaluator decides. -/
evaluation_axiom proved :
    provedIn extended3 (·.1.G) decls
      (fun (P, S, T) ↦ kwThm P S T "Reader.kwLet" 4 [false, false, true, true]) = true

/-- The developments prove the soundness at a binding of a name in the extended program: the
binding's form, given the soundness at the bound term and at the body, its antecedents holding,
resolves to a term whose evaluation converges to a value related at its type. -/
theorem let_proved :
    ∃ PST, extended3 = some PST ∧ Proves PST.1.G decls
      (kwThm PST.1 PST.2.1 PST.2.2 "Reader.kwLet" 4 [false, false, true, true]) :=
  provedIn_eq_true proved

end GebSlow.Prototypes.FreeTopos.Certified.DatatypeList

end
