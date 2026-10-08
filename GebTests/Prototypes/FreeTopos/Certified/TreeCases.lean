/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public meta import GebTests.Prototypes.FreeTopos.Certified.Basic -- shake: keep
public import GebTests.Prototypes.FreeTopos.TreeCases
public meta import GebTests.Prototypes.FreeTopos.TreeCases -- shake: keep
public import GebTests.Prototypes.ProgramCommand

set_option doc.verso true in
/-!
# The lemmas of trees, proved in the internal language

The development of {lit}`GebTests.Prototypes.FreeTopos.TreeCases`, the lemmas on the unfolding of
trees, the conditionals and the heads of lists, is stored in
{lit}`bootstrap/certificates/tree-cases.cert` and checks in the translated program.

## Main statements

* {lit}`treeCases_checked` — the development checks.

## Tags

internal language, trees, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.TreeCases

open Geb Geb.FreeTopos

/-- The development, read from its certificate. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/tree-cases.cert")

set_option doc.verso false in
/-- The development checks in the translated program, as Lean's evaluator decides. -/
evaluation_axiom checked : checkedIn TreeCases.program Weakening.Prog.G decls = true

/-- The development checks in the translated program. -/
theorem treeCases_checked : ∃ P, TreeCases.program = some P ∧ Checks P.G decls :=
  checkedIn_eq_true checked

end GebTests.Prototypes.FreeTopos.Certified.TreeCases

end
