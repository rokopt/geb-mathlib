/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Basic
public import Geb.Prototypes.Computability.Mazzanti.Combinators
public import Geb.Prototypes.Computability.Mazzanti.BitTree
meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# The non-size-increasing function algebra

Index for the modules on {cite}`Mazzanti2016`'s algebra {lit}`S(sbs₀, sbs₁)` over
bitstrings: its syntax and non-size-increase theorem, its expression
combinators, and the bit-tree recognizer written in it.
-/
