/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Encoding
public import Geb.Prototypes.Computability.BitTreeScanner.Scan
public import Geb.Prototypes.Computability.BitTreeScanner.Counter
public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Machine
public import Geb.Prototypes.Computability.BitTreeScanner.Tapes
public import Geb.Prototypes.Computability.BitTreeScanner.Steps
public import Geb.Prototypes.Computability.BitTreeScanner.Bound

/-!
# The tree scanner

Index for the modules on binary trees with bitstrings at the leaves: their
prefix encoding, the scan recognizing it, the redundant binary counter a
machine keeps the pending count in, the cost model, the two-pass three-tape
machine, its steps, and its time and space bound.
-/
