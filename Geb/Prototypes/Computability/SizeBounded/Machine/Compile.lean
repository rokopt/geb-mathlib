/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Bound
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Correct
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family

set_option doc.verso true

/-!
# Compiling the algebra

Index for the modules on the compilation of the size-bounded algebra into the
machine calculus: the carrier of a compiled expression and the fold that
assembles a node's program from its children's.
-/
