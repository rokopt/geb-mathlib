/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Unfolded
public import GebTests.Prototypes.FreeTopos.DatatypeBase
public import GebTests.Prototypes.ProgramCommand
public meta import Geb.Prototypes.FreeTopos.Internal.Unfolded -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep

set_option doc.verso true in
/-!
# The constants of the datatype language's soundness are accepted

The constants of the program the datatype language's soundness is stated in, the translated
compilers extended by the relations' definitions, are ones the developments' soundness reads
({name}`Geb.FreeTopos.Internal.Globals.accepted`): each definition compiles over the
definitions before it, the check accepts the primitive arrows and the definitions, and the
definitions they compile to are well formed. Lean's evaluator decides it. The theory of a topos
extended by those definitions therefore has models, in each of which the constants' invariant
holds, so that the validity of a development's theorems in every model of the program is that
of each of them.

## Main statements

* {lit}`accepted` — the constants of the extended program are accepted.

## Tags

internal language, datatypes, definitional extension, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- Whether the constants of a program, where one is given, are ones the check accepts that
compile to well-formed definitions ({name}`Geb.FreeTopos.Internal.Globals.accepted`). -/
def acceptedIn {α : Type} (o : Option α) (G : α → Internal.Globals) : Bool :=
  match o with
  | some P => (G P).accepted
  | none => false

set_option doc.verso false in
/-- The constants of the extended program are accepted and compile to well-formed definitions,
as Lean's evaluator decides. -/
evaluation_axiom constantsAccepted : acceptedIn extended3 (·.1.G) = true

/-- The constants of the extended program are accepted. -/
theorem accepted {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    PST.1.G.accepted = true := by
  have ha := constantsAccepted
  rw [h] at ha
  exact ha

end GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

end
