/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all, shake: keep-downstream

public import GebTests.Cslib
public import GebTests.Prototypes
public import GebTests.Lang
public import GebTests.Mathlib

import GebMeta

/-!
# GebTests root module

Test library root. Mirrors `Geb.lean` structure: `GebTests.Mathlib`
tests `Geb.Mathlib`; `GebTests.Cslib` tests `Geb.Cslib`;
`GebTests.Prototypes` tests `Geb.Prototypes`. `GebTests.Lang` tests
`GebLang`, whose sources are a sibling library rather than a `Geb`
subtree.
-/
