/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import GebTests.Prototypes.FreeTopos.Agreement.Load

set_option doc.verso true in
/-!
# The metalogic's checker written in Geb decides as the checker in Lean

The checker of the metalogic written in Geb, {lit}`bootstrap/free-topos/`, loads, and the last of
its globals is a function which, at the encodings of constants, entries and declarations, gives
the encoding of what {name}`Geb.FreeTopos.Internal.checkDev` gives at the same inputs: the state
after the development, or nothing where a declaration's proof does not prove it. The two checkers
therefore accept the same developments with the same results, in both directions, at every
input.

Constants are encoded by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encGlobals`, entries by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encEntry`, declarations by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encDecl` and states by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encState`. The proof composes the kernel's
evaluation of the loading ({lit}`GebTests.Prototypes.FreeTopos.Agreement.Load`) with the agreement
of the program's Lean mirror with the Lean checker, proved definition by definition
({name}`GebTests.Prototypes.FreeTopos.Agreement.Derivation.checkDev_eq`).

## Main statements

* {lit}`checkDev_agree` — the loaded checker written in Geb decides as the checker in Lean.

## Tags

metalogic, checker, development, agreement, soundness, completeness
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Load GebTests.Prototypes.FreeTopos.Agreement.Derivation

/-- The metalogic's checker written in Geb decides as the checker in Lean: its program loads to
globals whose last is a function of the check's type that, at encoded constants, entries and
declarations, gives the encoding of the Lean checker's state after the development. -/
theorem checkDev_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    ∃ f : Ty.den checkDevTy, G'[372]? = some ⟨checkDevTy, f⟩ ∧
      ∀ (G : Internal.Globals) (E : Array Internal.Entry) (ds : List Internal.Decl),
        f (encGlobals G) (E.toList.map encEntry) (ds.map encDecl) =
          encOpt ((Internal.checkDev G E ds).map encState) :=
  ⟨_, metalogic.load_eq, GebMirror.Metalogic.checkDev, metalogic_checkDev, checkDev_eq⟩

end GebTests.Prototypes.FreeTopos.Agreement

end
