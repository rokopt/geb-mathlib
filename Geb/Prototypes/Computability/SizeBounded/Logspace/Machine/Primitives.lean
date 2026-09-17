/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Pop
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Seek
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.ReadInput
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Count
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.EmitSuffix

set_option doc.verso true in
/-!
# The primitives of the logspace calculus

Index for the modules on the primitives sequenced from the phase machines:
the pop of a register's head bit and the push of a bit, the seek of the input
head to the cell a counter names, the read of the input bit at that cell, the
count of the input's length into a counter, and the emission of the end
segment of the input a counter names, each with its contract.
-/

set_option doc.verso true
