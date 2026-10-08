/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Basic
public import Geb.Prototypes.PHOAS.Scoped
public import Geb.Prototypes.PHOAS.Initial
public import Geb.Prototypes.PHOAS.Paranatural
public import Geb.Prototypes.PHOAS.Algebra
public import Geb.Prototypes.PHOAS.Category
public import Geb.Prototypes.PHOAS.Kmett
public import Geb.Prototypes.PHOAS.Dual
public import Geb.Prototypes.PHOAS.Cofree

set_option doc.verso true in
/-!
# Polynomial profunctors and PHOAS

Polynomial directions, their pointwise free monads, and ends of compatible families.
The end is the empty-context component of scoped syntax. The whole scoped family is the
initial algebra of the binding-signature endofunctor on functors of contexts, with
structural recursion, unique folds, and fold fusion.
Kmett's signature has no diagonal fixed point, no initial derived algebra, and no terminal
derived coalgebra. Distinct positions rule out initial and terminal diagonal elements of
the original profunctor, and the diagonal family of pointwise cofree carriers is empty.
-/

set_option doc.verso true
