/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.GoedelT
public import GebTests.Prototypes.GoedelT.LoadCommand
public import GebTests.Prototypes.GoedelT.MirrorDelta

set_option doc.verso true in
/-!
# The checker of Gödel's T written in Geb, loaded by the kernel

The bootstrap compiler's Lean backend emits a Geb program as Lean definitions, one for each of
the program's definitions: the program's mirror, {lit}`GebMirror.GoedelT` for the checker of
Gödel's T. This module states, and the kernel checks, that loading the checker's program with
{name}`Geb.Kernel.load` gives globals whose denotations are the mirror's definitions.

The command {lit}`geb_program` of {lit}`GebTests.Prototypes.GoedelT.LoadCommand` declares the
program's definitions, globals and loading, one definition at a time. The last global is the
checker, at the type of the function from a program's definitions, theorems and global types, a
certificate, a context and hypotheses, to an optional equation; that type is read from the
checker's definition, whose abstractions carry their types and whose body the front end applies
the identity at the result type to, by inverting the checker-evaluator.

## Main definitions

* {lit}`checkCertTy` — the type of the checker written in Geb.

## Main statements

* {lit}`checker.load_eq` — the checker's program loads to its globals.
* {lit}`checkCert_type` — the type the kernel computes for the checker's definition is
  {lit}`checkCertTy`, read from the definition's annotations by inverting the
  checker-evaluator, without evaluating it.
* {lit}`checker_checkCert` — the last of those globals is the mirror's checker, at the type
  {lit}`checkCertTy`.

## Tags

Gödel's T, checker, denotation, mirror, kernel reduction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.MirrorLoad

open Geb Geb.Kernel GebTests.Prototypes.GoedelT.MirrorDelta

set_option Elab.async false in
geb_program checker from "bootstrap/prelude.geb" "bootstrap/reader.geb" "bootstrap/check.geb"
  "bootstrap/goedel-t/equations.geb" mirror GebMirror.GoedelT

/-- The type of the checker written in Geb: from a program's definitions, theorems about it and
its global types, a certificate, a context and hypotheses, to an optional equation. -/
def checkCertTy : Tree :=
  tArrow (tList tT) (tArrow (tList tT) (tArrow (tList tT) (tArrow tT
    (tArrow (tList tT) (tArrow (tList tT) tT)))))

/-- The type the kernel computes for the checker's definition is the checker's type: the six
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkCert_type : checker.g178.1 = checkCertTy := by
  have h := infer_of_loadStep checker.step178
  generalize checker.g178.1 = T at h ⊢
  obtain ⟨f, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨B, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, _, h7, -, -⟩ := infer_app_inv h6
  obtain ⟨_, _, hB, h8⟩ := infer_lam_inv h7
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h8.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the last of the checker's globals is its global of index 178
kernel_rfl checker_last : checker.pre179[178]? = some checker.g178

/-- The last global of the checker's program is the mirror's checker, at the checker's type. -/
theorem checker_checkCert :
    checker.pre179[178]? = some (⟨checkCertTy, GebMirror.GoedelT.checkCert⟩ : Glob) :=
  checker_last.trans (congrArg some (Sigma.ext checkCert_type (checker.last_heq.trans HEq.rfl)))

end GebTests.Prototypes.GoedelT.MirrorLoad

end
