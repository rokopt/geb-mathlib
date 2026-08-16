/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all, shake: keep-downstream

public import GebLang.Basic

import GebMeta
import Lean.DocString.Syntax

/-!
# The Geb language

{lit}`GebLang` holds the core data structures of the Geb language. It
sits at the bottom of this repository's dependency order: its modules
import mathlib, Batteries and Cslib, and each other, and nothing of
this repository.

The library is written in Verso's literate style. A module docstring
is the prose of the module's page, and declaration docstrings render
as prose beside their highlighted code. The same sources feed
doc-gen4's API reference.

## Main definitions

- {name}`gebLangAnchor`, in the {lit}`GebLang.Basic` module.
-/
