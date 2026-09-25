/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Basic
public import Geb.Prototypes.PartialHorn.Definitional
public import Geb.Prototypes.PartialHorn.Development

set_option doc.verso true in
/-!
# Partial Horn logic

The logic of partial Horn theories over rose trees: signatures of partial operations, terms,
models, a checker of certificates proved sound in every model of a theory, developments of
certificates that cite the theorems before them, and definitional extensions of theories. The
metalogic's presentation of the free elementary topos is a partial Horn theory.
-/

set_option doc.verso true
