/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Arrows
public import Geb.Prototypes.FreeTopos.Category
public import Geb.Prototypes.FreeTopos.Check
public import Geb.Prototypes.FreeTopos.Infer
public import Geb.Prototypes.FreeTopos.Internal
public import Geb.Prototypes.FreeTopos.Model
public import Geb.Prototypes.FreeTopos.Prover
public import Geb.Prototypes.FreeTopos.Recursion
public import Geb.Prototypes.FreeTopos.Theory
public import Geb.Prototypes.FreeTopos.Topos

set_option doc.verso true in
/-!
# The free elementary topos with data objects

The metalogic's presentation of the free elementary topos with the natural numbers, list and
rose-tree objects, as a partial Horn theory whose sorts are objects and arrows, with the proof
that the category of each of its models is an elementary topos, a checker that infers the
typing of the terms of its certificates, a prover that computes certificates in it, the
uniqueness of its folds with a parameter, and its internal language, compiled to its
combinators.
-/

set_option doc.verso true
