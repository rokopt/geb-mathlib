/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import GebTests.Prototypes.FreeTopos.Agreement.Load
public import GebTests.Prototypes.FreeTopos.Agreement.Translation

set_option doc.verso true in
/-!
# The metalogic's checker and the translation written in Geb agree with Lean's

The checker of the metalogic written in Geb, {lit}`bootstrap/free-topos/`, loads, and one of its
globals is a function which, at the encodings of constants, entries and declarations, gives the
encoding of what {name}`Geb.FreeTopos.Internal.checkDev` gives at the same inputs: the state after
the development, or nothing where a declaration's proof does not prove it. The two checkers
therefore accept the same developments with the same results, in both directions, at every
input. The translation of the kernel into the internal language written in Geb,
{lit}`bootstrap/free-topos/translation.geb`, is part of the same program, and its translations of
a program's definitions, of a translated program's constants and of a theorem of Gödel's T give
the encodings of what {name}`Geb.FreeTopos.Translation.program`,
{name}`Geb.FreeTopos.Translation.globals` and {name}`Geb.FreeTopos.Translation.thm` give, at every
input.

Constants are encoded by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encGlobals`, entries by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encEntry`, declarations by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encDecl`, states by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encState`, translated programs by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.encProgram` and theorems of Gödel's T by
{name}`GebTests.Prototypes.GoedelT.MirrorEquations.encThm`. The proofs compose the kernel's
evaluation of the loading ({lit}`GebTests.Prototypes.FreeTopos.Agreement.Load`) with the agreement
of the program's Lean mirror with the Lean definitions, proved definition by definition
({name}`GebTests.Prototypes.FreeTopos.Agreement.Derivation.checkDev_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.program_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.trGlobals_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.thm_eq`).

## Main statements

* {lit}`checkDev_agree` — the loaded checker written in Geb decides as the checker in Lean.
* {lit}`translation_agree` — the loaded translation written in Geb translates as the translation
  in Lean.

## Tags

metalogic, checker, translation, development, agreement, soundness, completeness
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Load GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Translation

/-- The metalogic's checker written in Geb decides as the checker in Lean: its program loads to
globals among which is a function of the check's type that, at encoded constants, entries and
declarations, gives the encoding of the Lean checker's state after the development. -/
theorem checkDev_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    ∃ f : Ty.den checkDevTy, G'[372]? = some ⟨checkDevTy, f⟩ ∧
      ∀ (G : Internal.Globals) (E : Array Internal.Entry) (ds : List Internal.Decl),
        f (encGlobals G) (E.toList.map encEntry) (ds.map encDecl) =
          encOpt ((Internal.checkDev G E ds).map encState) :=
  ⟨_, metalogic.load_eq, GebMirror.Metalogic.checkDev, metalogic_checkDev, checkDev_eq⟩

/-- The translation written in Geb translates as the translation in Lean: its program loads to
globals among which are functions of their types that, at a program's definitions, at encoded
definitions of the language, and at the globals' types and an encoded theorem of Gödel's T, give
the encodings of the Lean translation's program, constants and theorem. -/
theorem translation_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den listFnTy, G'[533]? = some ⟨listFnTy, f⟩ ∧
      ∀ ds : List Tree, f ds = encOpt ((Translation.program ds).map encProgram)) ∧
    (∃ f : Ty.den listFnTy, G'[534]? = some ⟨listFnTy, f⟩ ∧
      ∀ defs : List Internal.Defn,
        f (defs.map encLDefn) = encGlobals (Translation.globals defs)) ∧
    (∃ f : Ty.den thmTy, G'[535]? = some ⟨thmTy, f⟩ ∧
      ∀ (gt : List Tree) (a : GoedelT.Thm),
        f gt (GebTests.Prototypes.GoedelT.MirrorEquations.encThm a) =
          encOpt ((Translation.thm gt a).map encThm)) :=
  ⟨_, metalogic.load_eq, ⟨GebMirror.Metalogic.program, metalogic_program, program_eq⟩,
    ⟨GebMirror.Metalogic.trGlobals, metalogic_trGlobals, trGlobals_eq⟩,
    ⟨GebMirror.Metalogic.thm, metalogic_thm, thm_eq⟩⟩

end GebTests.Prototypes.FreeTopos.Agreement

end
