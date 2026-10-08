/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.Substitution
public meta import GebTests.Prototypes.FreeTopos.Substitution -- shake: keep
public import GebTests.Prototypes.ProgramCommand

set_option doc.verso true in
/-!
# Substitution preserves types, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.Substitution`, the lemmas and the statement
that the kernel's type checker written in Geb preserves types by substitution, is stored in
{lit}`bootstrap/certificates/substitution.cert` and proves the statement in the translated
program.

## Main statements

* {lit}`substitution_proved` — the development proves substitution.

## Tags

internal language, type checker, substitution, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.Substitution

open Geb Geb.FreeTopos

/-- The development, read from its certificate. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/substitution.cert")

set_option doc.verso false in
/-- The development checks in the translated program and its last declaration states
substitution, as Lean's evaluator decides. -/
evaluation_axiom proved :
    provedIn Substitution.program Weakening.Prog.G decls Substitution.substitution = true

/-- The development proves that the kernel's type checker written in Geb preserves types by
substitution, in the translated program. -/
theorem substitution_proved :
    ∃ P, Substitution.program = some P ∧ Proves P.G decls (Substitution.substitution P) :=
  provedIn_eq_true proved

end GebTests.Prototypes.FreeTopos.Certified.Substitution

end
