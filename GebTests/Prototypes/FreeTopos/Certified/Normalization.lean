/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.Normalization
public meta import GebTests.Prototypes.FreeTopos.Normalization -- shake: keep
public import GebTests.Prototypes.ProgramCommand
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Well-typed terms evaluate, proved in the internal language

The developments of the fundamental lemma ({lit}`GebTests.Prototypes.FreeTopos.Normalization`),
the base, the convergence lemmas, the constants' relations and the lemma, are stored in
{lit}`bootstrap/certificates/` and, one after another, prove the lemma in the extended program:
a term to which the type checker written in Geb gives a type evaluates, by the evaluator written
in Geb, to a value related at that type. It is the internal counterpart of
{name}`Geb.Kernel.Eval.fundamental`.

## Main statements

* {lit}`fundamental_proved` — the developments prove the fundamental lemma.

## References

* {cite}`Tait1967`, for the logical relation and its fundamental lemma.

## Tags

internal language, logical relation, fundamental lemma, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.Normalization

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Weakening
  GebTests.Prototypes.FreeTopos.Normalization

/-- The developments, read from their certificates, one after another. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/normalization-base.cert") ++
    ofText (include_str "../../../../bootstrap/certificates/normalization-const.cert") ++
    ofText (include_str "../../../../bootstrap/certificates/normalization-rel.cert") ++
    ofText (include_str "../../../../bootstrap/certificates/normalization.cert")

set_option doc.verso false in
/-- The developments check in the extended program and the last declaration states the lemma, as
Lean's evaluator decides. -/
evaluation_axiom proved :
    provedIn extended (·.1.G) decls (fun (P, S) ↦ fundamentalThm P S) = true

/-- The developments prove the fundamental lemma in the extended program. -/
theorem fundamental_proved :
    ∃ PS, extended = some PS ∧ Proves PS.1.G decls (fundamentalThm PS.1 PS.2) :=
  provedIn_eq_true proved

end GebTests.Prototypes.FreeTopos.Certified.Normalization

end
