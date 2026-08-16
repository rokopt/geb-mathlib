/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebLang.Basic  -- shake: keep; #guard needs it
public meta import GebLang.Basic  -- shake: keep; #guard needs it

/-!
# Tests for the Geb language's anchor module

The anchor declaration evaluates to its stated value, exercising the
test driver against the `GebLang` library.

## Tags

geb, language
-/

@[expose] public section

#guard gebLangAnchor = 0
