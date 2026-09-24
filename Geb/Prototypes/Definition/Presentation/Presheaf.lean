/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.Basic
public import Geb.Prototypes.Definition.Presentation.Presheaf.OneStep
public import Geb.Prototypes.Definition.Presentation.Presheaf.QuotientAlg
public import Geb.Prototypes.Definition.Presentation.Presheaf.ClsModel
public import Geb.Prototypes.Definition.Presentation.Presheaf.Agreement

set_option doc.verso true in
/-!
# Equational presentations over presheaves

Equational presentations over a presheaf polynomial endofunctor with free arities, as
presentations over the slice of objects whose operations include the restrictions and whose
equations include those of naturality, identity and composition; their classes form a presheaf.
A quotient presheaf polynomial functor with free finitary arities, term arguments and congruences
has such a presentation, whose classes are its quotient W-type's.
-/

set_option doc.verso true
