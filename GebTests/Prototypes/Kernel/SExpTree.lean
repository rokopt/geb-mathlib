/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Document
public import Geb.Prototypes.Kernel.Reader

set_option doc.verso true in
/-!
# S-expressions as the Geb reader represents them

The tree by which the reader written in Geb represents an S-expression, in which the tests of
module elaboration and of the printer, and the proofs that the printer and the reader written in
Geb agree with Lean's, state what a Geb program reads and writes. The module reads no source, so
that the proofs importing it depend on no compiler's.

## Main definitions

* {lit}`sexpTree` — the tree of an S-expression.

## Tags

S-expression, reader, tree, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.ModulesTests

open Document

/-- An S-expression as the Geb reader represents it: an atom the node of label 1 over its
characters' codes, a list the node of label 2 over its elements. -/
def sexpTree : SExp → Tree :=
  RoseTree.elim fun a rs ↦
    match a with
    | some s => mk 1 (s.map fun c ↦ leaf c.toNat)
    | none => mk 2 rs

end Geb.Kernel.ModulesTests

end
