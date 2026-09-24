/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Basic
public import Geb.Prototypes.Definition.Presentation.Definitional
public import Geb.Prototypes.Definition.Presentation.Free
public import Geb.Prototypes.Definition.Presentation.OneStep
public import Geb.Prototypes.Definition.Presentation.Presheaf
public import Geb.Prototypes.Definition.Presentation.Slice

set_option doc.verso true in
/-!
# Equational presentations

Equational presentations over a polynomial signature whose sides are terms of the free monad
of any depth: their witnesses, terms of the free monad of the signature summed with the
equations; the classes of terms, the coequalizer of the witnesses' two endpoints; and, for
finitary presentations, the classes as the free algebra satisfying the equations, isomorphic for
one-step equations to the quotient W-type of the quotient presheaf polynomial functor; and the
presentations of derived operations, whose classes are the terms of the signature they extend;
the many-sorted presentations over a slice polynomial endofunctor; and the presentations over a
presheaf polynomial endofunctor with free arities, whose classes form a presheaf.
-/

set_option doc.verso true
