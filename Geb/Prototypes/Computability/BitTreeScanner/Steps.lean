/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Cfg
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Transition
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Seek
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Count
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Leaf
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Bit
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Run

/-!
# The two-pass tree scanner's steps

Index for the modules resolving the machine's transition and composing its
steps into runs: the single steps and runs, the transition at each case of
its table, the counting pass, the pending count's chains, the leaf count's
chains, the steps at each bit, and the whole run.
-/
