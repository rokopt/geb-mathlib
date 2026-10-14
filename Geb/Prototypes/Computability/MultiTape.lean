/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.MultiTape.Computes
public import Geb.Prototypes.Computability.MultiTape.OfTr
public import Geb.Prototypes.Computability.MultiTape.OutputString
public import Geb.Prototypes.Computability.MultiTape.Rename
public import Geb.Prototypes.Computability.MultiTape.RunFrom

/-!
# Multi-tape Turing machines

Index for the modules shared by every prototype built on CSLib's multi-tape Turing machines:
the iteration equations of a run, the evaluation of a run through a transition function, the
output emitted along a segment of a run, the resource bounds a halted run establishes, and the
renaming of a machine's alphabet and states.
-/
