/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Phases
public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Iter
public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Transforms

set_option doc.verso true in
/-!
# The recursion loop

Index for the modules on the loop of the machine calculus: the machine that
peels the bits of a register's word one at a time and runs a body for each.
-/

set_option doc.verso true
