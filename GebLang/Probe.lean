/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebMeta
import Lean.DocString.Syntax
import Mathlib.Logic.Basic
meta import GebMeta  -- shake: keep; supplies the mathlib_linters command

/-!
# Probe for the mathlib linter route

This module is a transient measurement of whether {lit}`mathlib_linters`
reaches mathlib's linters from inside a {lit}`GebLang` module that imports
mathlib ({lit}`docs/rules/lean-coding.md` § Literate modules). Removed once
the branch's closing commits land.

## Main definitions

- {lit}`gebLangProbeAnchor`, a term-mode use of a {lit}`Mathlib.Logic.Basic`
  lemma, present so the mathlib import survives extraction.

## Tags

geb, language
-/

mathlib_linters

@[expose] public section

/-- A term-mode declaration using a lemma from {lit}`Mathlib.Logic.Basic`,
present to exercise a mathlib import from this library. -/
theorem gebLangProbeAnchor (a b : Nat) : (a = b) = (b = a) :=
  eq_comm_eq a b
