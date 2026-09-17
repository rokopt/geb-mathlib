/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Bound
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Correct
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Family
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Comp
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Body
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.LoopEval
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Srn
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Theorem

set_option doc.verso true in
/-!
# Compiling the subalgebra

Index for the modules on the compilation of the successor-free subalgebra
into the logspace calculus: the carrier of a compiled expression and the fold
that assembles a node's program from its children's, the tape need and the
step bound read off the syntax, the contract a compiled program meets, the
valuations a family of fresh writers produces, the substitution case, the
transformers of the two loop bodies, the simultaneous recursion the two loops
compute, the recursion case, and the theorem that every expression's
compilation meets the contract.
-/

set_option doc.verso true
