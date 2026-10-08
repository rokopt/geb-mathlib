/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.Expansion
public meta import GebTests.Prototypes.FreeTopos.Expansion -- shake: keep
public import GebTests.Prototypes.ProgramCommand

set_option doc.verso true in
/-!
# The expansion of kernel forms is the identity, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.Expansion`, whose last lemma states that
the datatype language's expansion is the identity on programs of kernel forms, is stored in
{lit}`bootstrap/certificates/expansion.cert` and proves the statement in the translated program.

## Main statements

* {lit}`expansion_proved` — the development proves the statement.

## Tags

internal language, datatype language, expansion, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.Expansion

open Geb Geb.FreeTopos

/-- The development, read from its certificate. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/expansion.cert")

set_option doc.verso false in
/-- The development checks in the translated program and its last declaration states the
expansion's identity, as Lean's evaluator decides. -/
evaluation_axiom proved :
    provedIn Expansion.program Weakening.Prog.G decls Expansion.expansion = true

/-- The development proves that the datatype language's expansion is the identity on programs of
kernel forms, in the translated program. -/
theorem expansion_proved :
    ∃ P, Expansion.program = some P ∧ Proves P.G decls (Expansion.expansion P) :=
  provedIn_eq_true proved

end GebTests.Prototypes.FreeTopos.Certified.Expansion

end
