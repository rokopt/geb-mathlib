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
# The metalogic's checker written in Geb, loaded by the kernel

The bootstrap compiler's Lean backend emits the checker of the metalogic written in Geb,
{lit}`bootstrap/free-topos/`, as Lean definitions, one for each of the program's definitions: the
program's mirror, {lit}`GebMirror.Metalogic`. This module states, and the kernel checks, that
loading the program with {name}`Geb.Kernel.load` gives globals whose denotations are the mirror's
definitions.

The command {lit}`geb_program` of {lit}`GebTests.Prototypes.GoedelT.LoadCommand` declares the
program's definitions, globals and loading, one definition at a time. The last global is the
check of a development, at the type of the function from constants, entries and declarations to a
state; that type is read from the check's definition, whose abstractions carry their types and
whose body the front end applies the identity at the result type to, by inverting the
checker-evaluator.

## Main definitions

* {lit}`checkDevTy` — the type of the check of a development written in Geb.

## Main statements

* {lit}`metalogic.load_eq` — the program loads to its globals.
* {lit}`checkDev_type` — the type the kernel computes for the check's definition is
  {lit}`checkDevTy`, read from the definition's annotations by inverting the checker-evaluator,
  without evaluating it.
* {lit}`metalogic_checkDev` — the last of those globals is the mirror's check of a development,
  at the type {lit}`checkDevTy`.

## Tags

metalogic, checker, development, denotation, mirror, kernel reduction
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
  "bootstrap/free-topos/derivation.geb" mirror GebMirror.Metalogic

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

-- the last of the program's globals is its global of index 372
kernel_rfl metalogic_last : metalogic.pre373[372]? = some metalogic.g372

/-- The last global of the program is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.pre373[372]? = some (⟨checkDevTy, GebMirror.Metalogic.checkDev⟩ : Glob) :=
  metalogic_last.trans
    (congrArg some (Sigma.ext checkDev_type (metalogic.last_heq.trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
