/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Counter
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Contract
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Branch
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Wrapper
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Main

set_option doc.verso true in
/-!
# The logspace machine calculus

Index for the modules on the machine calculus the successor-free subalgebra
compiles into: binary counters on a work tape, the input-aware contract of a
program, the loop and the branch, the phases and the primitives, the
compilation and its correctness, and the machine of a unary expression with
its polynomial time and logarithmic space bounds.
-/

set_option doc.verso true
