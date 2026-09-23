/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType.Depth
public import Geb.Prototypes.MType.Approx
public import Geb.Prototypes.MType.Basic
public import Geb.Prototypes.MType.Equiv

set_option doc.verso true in
/-!
# M-types constructed from W-types

Index for the modules constructing the M-type of an arbitrary polynomial
functor from W-types: the depths, a W-type; the observations of each depth,
the fibres of a presheaf W-type over the depths; the M-type, the agreeing
root trees of a slice W-type storing one observation at each depth, with its
constructor, destructor and corecursor; and its equivalence with mathlib's
M-type.
-/
