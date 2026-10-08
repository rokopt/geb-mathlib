/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.Weakening
public meta import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep
public import GebTests.Prototypes.ProgramCommand

set_option doc.verso true in
/-!
# Weakening preserves types, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.Weakening`, the lemmas and the statement
that the kernel's type checker written in Geb preserves types by weakening, is stored in
{lit}`bootstrap/certificates/weakening.cert` and proves the statement in the translated
program.

## Main statements

* {lit}`weakening_proved` — the development proves weakening.

## Tags

internal language, type checker, weakening, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.Weakening

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Weakening

/-- The development, read from its certificate. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/weakening.cert")

set_option doc.verso false in
/-- The development checks in the translated program and its last declaration states weakening,
as Lean's evaluator decides. -/
evaluation_axiom proved : provedIn program Prog.G decls weakening = true

/-- The development proves that the kernel's type checker written in Geb preserves types by
weakening, in the translated program. -/
theorem weakening_proved : ∃ P, program = some P ∧ Proves P.G decls (weakening P) :=
  provedIn_eq_true proved

end GebTests.Prototypes.FreeTopos.Certified.Weakening

end
