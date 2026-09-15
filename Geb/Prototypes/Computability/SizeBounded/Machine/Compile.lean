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
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Comp
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Body
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.LoopEval
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.SrnInit
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Srn
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Theorem

set_option doc.verso true

/-!
# Compiling the algebra

Index for the modules on the compilation of the size-bounded algebra into the
machine calculus: the carrier of a compiled expression and the fold that
assembles a node's program from its children's, the step bound read off an
expression's syntax, the contract a compiled program meets, the valuations a
family of fresh writers produces, the substitution case, the transformer of a
recursion body, the simultaneous recursion the loop computes, the valuation
entering the loop, the recursion case, and the theorem that every expression's
compilation meets the contract.
-/
