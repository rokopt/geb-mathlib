/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EndSegment
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Rep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The logspace subalgebra

Index for the modules on {cite}`Kristiansen2005`'s algebra
{lit}`[I, C_W; comp, simn]` as the successor-free subalgebra of
{name}`Geb.SizeBounded.S`: its expressions, the end-segment lemma, and the
interpretation on the logarithmic-space representation of values.
-/

set_option doc.verso true
