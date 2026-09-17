/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Inc
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.InputMove
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.ReadBit
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.EmitRight

set_option doc.verso true in
/-!
# The phase machines of the logspace calculus

Index for the modules on the phases the logspace primitives are sequenced
from: the walks that increment and decrement a binary counter in place, the
moves of the input head, the read of one input bit into a flag, and the
emission of the input from the head rightwards, each with its closed-form run.
-/

set_option doc.verso true
