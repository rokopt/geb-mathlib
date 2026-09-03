/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Lean.DocString.Syntax

/-!
# Anchor for the library's documentation pipelines

This module's prose is the literate site's page for the module, and
its declaration carries a docstring of the other kind, so the two
pipelines have a source of each to render.

## Main definitions

- {lit}`gebLangAnchor`, the declaration whose docstring exercises
  the declaration-level pipeline.

## Tags

geb, language
-/

@[expose] public section

/-- A declaration whose docstring renders in both of the library's
documentation pipelines: as page prose in the literate site, and in
doc-gen4's reference. Its checked {name}`Nat` reference elaborates
under the {option}`doc.verso` option. -/
def gebLangAnchor : Nat := 0
