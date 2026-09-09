/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Machine

/-!
# The one-pass tree scanner's output against `validBool`

`bitTreeScanner`'s output on a short list of words, checked against
`Geb.BitTreeScanner.validBool` by kernel evaluation.

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
through `bitTreeScanner.outputString`, which reads the input via
`Turing.MultiTapeTM.Cfg.inputSymbol`, the same root
`Geb/Prototypes/Computability/BitTreeScanner/Steps.lean`'s implementation
notes name for that module's `Classical.choice` dependency. The module has no
choice-free content of its own left to state: its subject is the
correspondence between `bitTreeScanner` and Cslib's
`Turing.MultiTapeTM.outputString`, and `sampleWords` is packaging, the
literal the other two declarations are stated over.

## Tags

Turing machine, tree, prefix code, test
-/

@[expose] public section

open Geb.BitTreeScanner Turing MultiTapeTM
open Geb.TreeScanner (boolEmb)

namespace BitTreeScannerTest

/-- The words the mirror checks. -/
def sampleWords : List (List Bool) :=
  [[], [false], [false, false], [true], [true, false, false, false, false],
   [true, false, false, false, true, true, false], [false, false, false],
   [false, true, true, true, false], [true, true, false, false, false, false, false, false]]

/-- The scanner's output on each sample word. -/
def sampleOutputs : List (List (Fin 2)) :=
  sampleWords.map fun w ↦
    bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) (w.length + 1)

/-- The scanner emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (validBool w)] := by
  decide

end BitTreeScannerTest
