/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Register
public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq
public import Geb.Prototypes.Computability.SizeBounded.Machine.SeqFin
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives

set_option doc.verso true

/-!
# The machine calculus

Index for the modules on the machine calculus: registers holding bitstrings
on the work tapes of a {name}`Turing.MultiTapeTM`, and the programs built
from them.
-/
