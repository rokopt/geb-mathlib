/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Slice.Term
public import Geb.Prototypes.Definition.Presentation.Slice.Basic
public import Geb.Prototypes.Definition.Presentation.Slice.Free

set_option doc.verso true in
/-!
# Equational presentations over a slice

Many-sorted equational presentations, over a slice polynomial endofunctor, whose sides are
well-sorted terms of the free monad of any depth: the well-sorted terms and their evaluation in
algebras over the sorts; the classes of terms of each sort, the coequalizer of the endpoints of the
well-sorted witnesses of that sort; and, for finitary presentations, the classes as the free
algebra over the sorts satisfying the equations.
-/

set_option doc.verso true
