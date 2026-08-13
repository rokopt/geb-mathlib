/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.TreeScannerSpike

/-!
# The scanner spike's cross-module measurements

The two facts about `Geb.spikeTM` that a module importing it faces and an
assertion inside its own module does not: whether a configuration family
defined there reduces against `initCfg` here, and whether the kernel
closes a machine's output over the word list the tree scanner's test
mirror will use.

## Main definitions

- `spikeWords` — the words the kernel measurement runs over.
- `spikeOutputs` — the spike's output on each of them.

## Main statements

- `spikeSeekCfg_zero` — the blank-taped family at index zero is the initial
  configuration, read across a module boundary.
- `spikeOutputs_eq` — the six-word output list closes in the kernel.

## Implementation notes

The output assertion runs through the named `def` `spikeOutputs` rather
than through an anonymous `example`, because `lake shake` infers a
module's required imports from the constants its olean references and an
anonymous `example` leaves no such reference.

## Tags

Turing machine, spike
-/

@[expose] public section

namespace Geb

open Turing MultiTapeTM

/-- The blank-taped family at index zero is the initial configuration. -/
theorem spikeSeekCfg_zero (input : List (Fin 2)) :
    spikeSeekCfg input 0 (Nat.zero_le _) = spikeTM.initCfg input := rfl

/-- The words the measurement runs over: the six the tree scanner's test
mirror will use. -/
def spikeWords : List (List Bool) :=
  [[], [false], [true], [true, false], [false, true, false],
   [true, true, false, false, false]]

/-- The spike's output on each word, at the step count the tree scanner's
test mirror will use. -/
def spikeOutputs : List (List (Fin 2)) :=
  spikeWords.map fun w ↦
    spikeTM.outputString (spikeTM.initCfg (w.map spikeEmb)) (2 * w.length + 3)

/-- The spike emits its single symbol on each of the six words. -/
theorem spikeOutputs_eq : spikeOutputs = spikeWords.map fun _ ↦ [1] := by decide

end Geb
