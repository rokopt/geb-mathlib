/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Machine
public import Geb.Prototypes.Computability.MultiTape.OfTr
public import Geb.Prototypes.Computability.MultiTape.OutputString

/-!
# The tree scanner's output against `validBool`

`treeScanner`'s output on a short list of words, checked against
`RankedAlphabet.Binary.binRanked.validBool` by kernel evaluation.

## Main definitions

* `sampleWords` — the words the mirror checks.
* `sampleOutputs` — the output tape of a run of the scanner's transition
  function on each sample word.

## Main statements

* `sampleOutputs_eq` — the run emits the decision function's value on each
  sample word.
* `outputString_sampleWords` — the scanner emits the decision function's
  value on each sample word.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Measurement
(`#print axioms`) finds `sampleWords` axiom-free but `sampleOutputs` and
`sampleOutputs_eq` depending on `Classical.choice`: the taint enters
through `Turing.Cfg.inputSymbol`, the same root `Steps.lean`'s
implementation notes name for that module's `Classical.choice`
dependency. The module has no choice-free content of its own left to
state: its subject is the correspondence between `treeScanner` and
the output emitted along a run of Cslib's `Turing.MultiTapeTM.runFrom`, and `sampleWords` is
packaging, the literal the other declarations are stated over.

Cslib's step of a machine is chosen from its transition relation and does
not reduce, so the kernel evaluates the run of `transition` by
`Turing.MultiTapeTM.stepOfTr`, and `Turing.MultiTapeTM.runFrom_ofTr`
identifies that run with the scanner's.

## Tags

Turing machine, tree, preorder encoding, test
-/

@[expose] public section

open Geb.TreeScanner Turing MultiTapeTM RankedAlphabet.Binary

/-- The words the mirror checks. -/
def sampleWords : List (List Bool) :=
  [[], [false], [true], [false, false], [true, false], [false, true, false],
   [true, true, false, false, false]]

/-- The output tape of a run of the scanner's transition function on each
sample word. -/
def sampleOutputs : List (List (Fin 2)) :=
  sampleWords.map fun w ↦
    ((stepOfTr transition)^[2 * w.length + 3] (Cfg.init stSeek (w.map boolEmb))).output

/-- The run emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (binRanked.validBool w)] := by
  decide

/-- The scanner emits the decision function's value on each sample word. -/
theorem outputString_sampleWords :
    sampleWords.map (fun w ↦
      treeScanner.outputString (treeScanner.initCfg (w.map boolEmb)) (2 * w.length + 3)) =
      sampleWords.map fun w ↦ [boolEmb (binRanked.validBool w)] := by
  rw [← sampleOutputs_eq]
  refine List.map_congr_left fun w _ ↦ ?_
  rw [← initCfg_runFrom_output, treeScanner, runFrom_ofTr]
  rfl
