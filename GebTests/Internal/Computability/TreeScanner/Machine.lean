/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.TreeScanner.Machine

/-!
# The tree scanner's output against `validBool`

`treeScanner`'s output on a short list of words, checked against
`RankedAlphabet.Binary.binRanked.validBool` by kernel evaluation.

## Main definitions

* `sampleWords` — the words the mirror checks.
* `sampleOutputs` — the scanner's output on each sample word.

## Main statements

* `sampleOutputs_eq` — the scanner emits the decision function's value on
  each sample word.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Measurement
(`#print axioms`) finds `sampleWords` axiom-free but `sampleOutputs` and
`sampleOutputs_eq` depending on `Classical.choice`: the taint enters
through `treeScanner.outputString`, which reads the input via
`Turing.MultiTapeTM.Cfg.inputSymbol`, the same root `Steps.lean`'s
implementation notes name for that module's `Classical.choice`
dependency. The module's own subject is the correspondence between
`treeScanner` and Cslib's `Turing.MultiTapeTM.outputString`, so the
allowlist's primary criterion covers it outright.

## Tags

Turing machine, tree, preorder encoding, test
-/

@[expose] public section

open Geb.TreeScanner Turing MultiTapeTM RankedAlphabet.Binary

/-- The words the mirror checks. -/
def sampleWords : List (List Bool) :=
  [[], [false], [true], [false, false], [true, false], [false, true, false],
   [true, true, false, false, false]]

/-- The scanner's output on each sample word. -/
def sampleOutputs : List (List (Fin 2)) :=
  sampleWords.map fun w ↦
    treeScanner.outputString (treeScanner.initCfg (w.map boolEmb))
      (2 * w.length + 3)

/-- The scanner emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (binRanked.validBool w)] := by
  decide
