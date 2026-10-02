/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic
public import GebTests.Prototypes.GoedelT.LoadCommand
public import GebTests.Prototypes.GoedelT.MirrorDelta

set_option doc.verso true in
/-!
# The metalogic's checker and the translation written in Geb, loaded by the kernel

The bootstrap compiler's Lean backend emits the checker of the metalogic written in Geb,
{lit}`bootstrap/free-topos/`, with the kernel's checker it translates the kernel's terms by and the
translation of the kernel into the internal language, as Lean definitions, one for each of the
program's definitions: the program's mirror, {lit}`GebMirror.Metalogic`. This module states, and
the kernel checks, that loading the program with {name}`Geb.Kernel.load` gives globals whose
denotations are the mirror's definitions.

The command {lit}`geb_program` of {lit}`GebTests.Prototypes.GoedelT.LoadCommand` declares the
program's definitions, globals and loading, one definition at a time. Among the globals are the
check of a development, at the type of the function from constants, entries and declarations to a
state, and the translations of a program, of its constants and of a theorem of Gödel's T; each
type is read from the definition, whose abstractions carry their types and whose body the front
end applies the identity at the result type to, by inverting the checker-evaluator.

## Main definitions

* {lit}`checkDevTy` — the type of the check of a development written in Geb.
* {lit}`listFnTy`, {lit}`thmTy` — the types of the translations of a program and of its constants,
  and of a theorem.

## Main statements

* {lit}`metalogic.load_eq` — the program loads to its globals.
* {lit}`checkDev_type`, {lit}`program_type`, {lit}`trGlobals_type`, {lit}`thm_type` — the types
  the kernel computes for those definitions, read from the definitions' annotations by inverting
  the checker-evaluator, without evaluating it.
* {lit}`metalogic_checkDev`, {lit}`metalogic_program`, {lit}`metalogic_trGlobals`,
  {lit}`metalogic_thm` — those globals are the mirror's definitions, at those types.

## Tags

metalogic, checker, translation, development, denotation, mirror, kernel reduction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Load

open Geb Geb.Kernel GebTests.Prototypes.GoedelT.Load GebTests.Prototypes.GoedelT.MirrorDelta

set_option maxHeartbeats 20000000 in
-- the kernel evaluates the checker-evaluator on each definition of the program, the largest the
-- checker's steps over derivations and declarations
set_option Elab.async false in
geb_program metalogic from "bootstrap/prelude.geb" "bootstrap/free-topos/base.geb"
  "bootstrap/free-topos/partial-horn.geb" "bootstrap/free-topos/theory.geb"
  "bootstrap/free-topos/infer.geb" "bootstrap/free-topos/language.geb"
  "bootstrap/free-topos/derivation.geb" "bootstrap/reader.geb" "bootstrap/check.geb"
  "bootstrap/free-topos/translation.geb" mirror GebMirror.Metalogic
  exports checkDev program trGlobals thm

/-- The type of the check of a development written in Geb: from the constants, the entries and
the declarations, to the optional state after them. -/
def checkDevTy : Tree := tArrow tT (tArrow (tList tT) (tArrow (tList tT) tT))

/-- The type the kernel computes for the check's definition is the check's type: the three
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkDev_type : metalogic.g372.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step372
  generalize metalogic.g372.1 = T at h ⊢
  obtain ⟨f, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨B, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 372
kernel_rfl metalogic_g372 : metalogic.pre536[372]? = some metalogic.g372

/-- The program's global of index 372 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.pre536[372]? = some (⟨checkDevTy, GebMirror.Metalogic.checkDev⟩ : Glob) :=
  metalogic_g372.trans
    (congrArg some (Sigma.ext checkDev_type (metalogic.checkDev_heq.trans HEq.rfl)))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g533.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step533
  generalize metalogic.g533.1 = T at h ⊢
  obtain ⟨f, h0⟩ := h
  obtain ⟨B, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g534.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step534
  generalize metalogic.g534.1 = T at h ⊢
  obtain ⟨f, h0⟩ := h
  obtain ⟨B, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g535.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step535
  generalize metalogic.g535.1 = T at h ⊢
  obtain ⟨f, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨B, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 533, 534 and 535
kernel_rfl metalogic_g533 : metalogic.pre536[533]? = some metalogic.g533
kernel_rfl metalogic_g534 : metalogic.pre536[534]? = some metalogic.g534
kernel_rfl metalogic_g535 : metalogic.pre536[535]? = some metalogic.g535

/-- The program's global of index 533 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.pre536[533]? = some (⟨listFnTy, GebMirror.Metalogic.program⟩ : Glob) :=
  metalogic_g533.trans
    (congrArg some (Sigma.ext program_type (metalogic.program_heq.trans HEq.rfl)))

/-- The program's global of index 534 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.pre536[534]? = some (⟨listFnTy, GebMirror.Metalogic.trGlobals⟩ : Glob) :=
  metalogic_g534.trans
    (congrArg some (Sigma.ext trGlobals_type (metalogic.trGlobals_heq.trans HEq.rfl)))

/-- The program's global of index 535 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.pre536[535]? = some (⟨thmTy, GebMirror.Metalogic.thm⟩ : Glob) :=
  metalogic_g535.trans
    (congrArg some (Sigma.ext thm_type (metalogic.thm_heq.trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
