/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.WConstruction
public meta import Geb.Prototypes.BitStream.WConstruction -- shake: keep; #guard needs it

set_option doc.verso true in
/-!
# Executable observations of streams constructed from W-types

The checks evaluate a finite constructed stream, an infinite alternating
stream, and the tail of a prepended infinite stream. They exercise the
compiled dependent W-eliminator and the slice/presheaf W-tree encodings.

## Tags

bitstream, W-type, M-type, corecursion, test
-/
set_option doc.verso true
set_option linter.privateModule false

open Geb.BitStream.WConstruction

/-- An infinite stream whose consecutive bits alternate. -/
private def alternating : Stream := corec (fun b : Bool ↦ some (b, !b)) false

/-- Termination after the two bits one and zero. -/
private def finite : Stream := mk (some (true, mk (some (false, mk none))))

#guard (prefixEquiv (ofNat 4) (observe finite (ofNat 4))).val = [true, false]

#guard (prefixEquiv (ofNat 5) (observe alternating (ofNat 5))).val =
  [false, true, false, true, false]

#guard (prefixEquiv (ofNat 3) (observe (tail (mk (some (true, alternating)))) (ofNat 3))).val =
  [false, true, false]

#guard (prefixEquiv zero (observe alternating zero)).val = []
