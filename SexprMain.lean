/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.ConcreteSyntax.Command

/-!
# S-expression executable entry point

Run the file command with `lake exe sexpr`. The command implementation is
`Geb.Sexpr.run`; the entry point is outside the library's module prefix.

## Main definitions

* `main`: forward command-line arguments to `Geb.Sexpr.run`.

## Tags

S-expression, command line
-/

/-- Run the S-expression file command. -/
public def main : List String → IO UInt32 := Geb.Sexpr.run
