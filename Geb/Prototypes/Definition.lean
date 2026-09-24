/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Basic
public import Geb.Prototypes.Definition.Vertex
public import Geb.Prototypes.Definition.Solution
public import Geb.Prototypes.Definition.Guarded
public import Geb.Prototypes.Definition.Presentation

set_option doc.verso true in
/-!
# Definitions

Definitions as terms of the free monad of a polynomial signature: the terms, their linking
and their equation blocks; the vertices of a term, by which an environment is addressed; and
the equation blocks that are definitions: the well-founded blocks, having exactly one solution
in every algebra, and the guarded blocks, having exactly one solution in the M-type; and the
equational presentations whose sides are terms of any depth, with their classes of terms.
-/

set_option doc.verso true
