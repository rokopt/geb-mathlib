/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.DatatypeSoundness
public import GebTests.Prototypes.ProgramCommand

set_option doc.verso true in
/-!
# The program of the datatype language's soundness, loaded by the kernel

The bootstrap compiler's Lean backend emits the program the datatype language's soundness is
stated in ({lit}`bootstrap/datatype-soundness.manifest`: the stage-1 compiler's typing and
expansion with the reader, the kernel's type checker, the recognizers, the traversal of kernel
terms and the evaluator, and the statements of weakening and of the soundness) as Lean
definitions, one for each of the program's definitions: the program's mirror,
{lit}`GebMirror.DatatypeSoundness`. This module states, and the kernel checks, that loading the
program with {name}`Geb.Kernel.load` gives globals whose denotations are the mirror's
definitions. The command {lit}`geb_program` of {lit}`GebTests.Prototypes.ProgramCommand` declares
the program's definitions, globals and loading, one definition at a time, each step proved by the
checker-evaluator's equation at each node of the definition. The trees of the program's
definitions are compiled besides, so that Lean's evaluator compares them with the definitions
that the soundness's own reading of the program gives.

## Main definitions

* {lit}`At` — the global at an index of the program is a definition of the mirror.

## Main statements

* {lit}`GebMirror.datatypeSoundness.load_globals` — the program loads to its globals, listed one
  by one.
* {lit}`At.«Datatype.expandTyped»` and the statements of its form, one for each entry of the
  manifest — the entry's global is its mirror.

## Tags

kernel, loading, mirror, datatypes, test
-/

set_option doc.verso true

@[expose] public section

open GebMirror.DatatypeSoundness

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeLoad

open Geb Geb.Kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- the kernel checks the checker-evaluator's equation at each node of each of the definitions
set_option Elab.async false in
geb_program _root_.GebMirror.datatypeSoundness from "bootstrap/datatype-soundness.manifest"
  mirror GebMirror.DatatypeSoundness

open GebMirror (datatypeSoundness)

-- the trees of the program's definitions and their list, compiled
open Lean Elab Command in
run_cmd liftCoreM do
  let n := `GebMirror.datatypeSoundness
  let some info := (← getEnv).find? n | throwError "the program is not declared"
  for d in info.value!.getUsedConstants do
    if d.getPrefix == n then Lean.compileDecls #[d]
  Lean.compileDecls #[n]

/-- The global at an index of the program is a definition of the mirror: the global the kernel
loads there has the definition as its denotation, at a type whose denotation is the definition's
type. -/
def At (k : ℕ) {A : Type} (m : A) : Prop :=
  ∃ g : Glob, datatypeSoundness.globals[k]? = some g ∧ HEq g.2 m

-- the list of the globals is unfolded to an entry in as many steps as the entry's index
set_option maxRecDepth 10000

/-- The global of the definition {lit}`Prelude.length` is its mirror. -/
theorem At.«Prelude.length» : At 1 «Prelude.length» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.length_heq»⟩

/-- The global of the definition {lit}`Prelude.some` is its mirror. -/
theorem At.«Prelude.some» : At 5 «Prelude.some» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.some_heq»⟩

/-- The global of the definition {lit}`Prelude.isSome` is its mirror. -/
theorem At.«Prelude.isSome» : At 7 «Prelude.isSome» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.isSome_heq»⟩

/-- The global of the definition {lit}`Prelude.get` is its mirror. -/
theorem At.«Prelude.get» : At 8 «Prelude.get» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.get_heq»⟩

/-- The global of the definition {lit}`Prelude.and` is its mirror. -/
theorem At.«Prelude.and» : At 9 «Prelude.and» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.and_heq»⟩

/-- The global of the definition {lit}`Prelude.or` is its mirror. -/
theorem At.«Prelude.or» : At 10 «Prelude.or» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.or_heq»⟩

/-- The global of the definition {lit}`Prelude.nth` is its mirror. -/
theorem At.«Prelude.nth» : At 12 «Prelude.nth» :=
  ⟨_, rfl, datatypeSoundness.«Prelude.nth_heq»⟩

/-- The global of the definition {lit}`Reader.isAtom` is its mirror. -/
theorem At.«Reader.isAtom» : At 50 «Reader.isAtom» :=
  ⟨_, rfl, datatypeSoundness.«Reader.isAtom_heq»⟩

/-- The global of the definition {lit}`Reader.nameOf` is its mirror. -/
theorem At.«Reader.nameOf» : At 52 «Reader.nameOf» :=
  ⟨_, rfl, datatypeSoundness.«Reader.nameOf_heq»⟩

/-- The global of the definition {lit}`Reader.named` is its mirror. -/
theorem At.«Reader.named» : At 53 «Reader.named» :=
  ⟨_, rfl, datatypeSoundness.«Reader.named_heq»⟩

/-- The global of the definition {lit}`Reader.kwT` is its mirror. -/
theorem At.«Reader.kwT» : At 54 «Reader.kwT» :=
  ⟨_, rfl, datatypeSoundness.«Reader.kwT_heq»⟩

/-- The global of the definition {lit}`Reader.kwUnit` is its mirror. -/
theorem At.«Reader.kwUnit» : At 55 «Reader.kwUnit» :=
  ⟨_, rfl, datatypeSoundness.«Reader.kwUnit_heq»⟩

/-- The global of the definition {lit}`Reader.kwDef` is its mirror. -/
theorem At.«Reader.kwDef» : At 74 «Reader.kwDef» :=
  ⟨_, rfl, datatypeSoundness.«Reader.kwDef_heq»⟩

/-- The global of the definition {lit}`Reader.kwDeftype` is its mirror. -/
theorem At.«Reader.kwDeftype» : At 75 «Reader.kwDeftype» :=
  ⟨_, rfl, datatypeSoundness.«Reader.kwDeftype_heq»⟩

/-- The global of the definition {lit}`Reader.kwDefnum` is its mirror. -/
theorem At.«Reader.kwDefnum» : At 76 «Reader.kwDefnum» :=
  ⟨_, rfl, datatypeSoundness.«Reader.kwDefnum_heq»⟩

/-- The global of the definition {lit}`Reader.indexOf` is its mirror. -/
theorem At.«Reader.indexOf» : At 78 «Reader.indexOf» :=
  ⟨_, rfl, datatypeSoundness.«Reader.indexOf_heq»⟩

/-- The global of the definition {lit}`Reader.numeral` is its mirror. -/
theorem At.«Reader.numeral» : At 80 «Reader.numeral» :=
  ⟨_, rfl, datatypeSoundness.«Reader.numeral_heq»⟩

/-- The global of the definition {lit}`Reader.expandNums` is its mirror. -/
theorem At.«Reader.expandNums» : At 81 «Reader.expandNums» :=
  ⟨_, rfl, datatypeSoundness.«Reader.expandNums_heq»⟩

/-- The global of the definition {lit}`Reader.numOf` is its mirror. -/
theorem At.«Reader.numOf» : At 82 «Reader.numOf» :=
  ⟨_, rfl, datatypeSoundness.«Reader.numOf_heq»⟩

/-- The global of the definition {lit}`Reader.node2` is its mirror. -/
theorem At.«Reader.node2» : At 85 «Reader.node2» :=
  ⟨_, rfl, datatypeSoundness.«Reader.node2_heq»⟩

/-- The global of the definition {lit}`Reader.readProgram` is its mirror. -/
theorem At.«Reader.readProgram» : At 107 «Reader.readProgram» :=
  ⟨_, rfl, datatypeSoundness.«Reader.readProgram_heq»⟩

/-- The global of the definition {lit}`Check.checkProgram` is its mirror. -/
theorem At.«Check.checkProgram» : At 122 «Check.checkProgram» :=
  ⟨_, rfl, datatypeSoundness.«Check.checkProgram_heq»⟩

/-- The global of the definition {lit}`Typing.envDefs` is its mirror. -/
theorem At.«Typing.envDefs» : At 203 «Typing.envDefs» :=
  ⟨_, rfl, datatypeSoundness.«Typing.envDefs_heq»⟩

/-- The global of the definition {lit}`Typing.envNoms` is its mirror. -/
theorem At.«Typing.envNoms» : At 204 «Typing.envNoms» :=
  ⟨_, rfl, datatypeSoundness.«Typing.envNoms_heq»⟩

/-- The global of the definition {lit}`Typing.envMs` is its mirror. -/
theorem At.«Typing.envMs» : At 207 «Typing.envMs» :=
  ⟨_, rfl, datatypeSoundness.«Typing.envMs_heq»⟩

/-- The global of the definition {lit}`Typing.env0` is its mirror. -/
theorem At.«Typing.env0» : At 208 «Typing.env0» :=
  ⟨_, rfl, datatypeSoundness.«Typing.env0_heq»⟩

/-- The global of the definition {lit}`Typing.lookupName` is its mirror. -/
theorem At.«Typing.lookupName» : At 209 «Typing.lookupName» :=
  ⟨_, rfl, datatypeSoundness.«Typing.lookupName_heq»⟩

/-- The global of the definition {lit}`Typing.hasName` is its mirror. -/
theorem At.«Typing.hasName» : At 210 «Typing.hasName» :=
  ⟨_, rfl, datatypeSoundness.«Typing.hasName_heq»⟩

/-- The global of the definition {lit}`Typing.recognizerName` is its mirror. -/
theorem At.«Typing.recognizerName» : At 213 «Typing.recognizerName» :=
  ⟨_, rfl, datatypeSoundness.«Typing.recognizerName_heq»⟩

/-- The global of the definition {lit}`Typing.markerNames` is its mirror. -/
theorem At.«Typing.markerNames» : At 243 «Typing.markerNames» :=
  ⟨_, rfl, datatypeSoundness.«Typing.markerNames_heq»⟩

/-- The global of the definition {lit}`Typing.memberOf` is its mirror. -/
theorem At.«Typing.memberOf» : At 247 «Typing.memberOf» :=
  ⟨_, rfl, datatypeSoundness.«Typing.memberOf_heq»⟩

/-- The global of the definition {lit}`Typing.decimalChars` is its mirror. -/
theorem At.«Typing.decimalChars» : At 269 «Typing.decimalChars» :=
  ⟨_, rfl, datatypeSoundness.«Typing.decimalChars_heq»⟩

/-- The global of the definition {lit}`Typing.markerCtors` is its mirror. -/
theorem At.«Typing.markerCtors» : At 286 «Typing.markerCtors» :=
  ⟨_, rfl, datatypeSoundness.«Typing.markerCtors_heq»⟩

/-- The global of the definition {lit}`Typing/OName.nothing` is its mirror. -/
theorem At.«Typing/OName.nothing» : At 299 «Typing/OName.nothing» :=
  ⟨_, rfl, datatypeSoundness.«Typing/OName.nothing_heq»⟩

/-- The global of the definition {lit}`Typing.checkAll` is its mirror. -/
theorem At.«Typing.checkAll» : At 313 «Typing.checkAll» :=
  ⟨_, rfl, datatypeSoundness.«Typing.checkAll_heq»⟩

/-- The global of the definition {lit}`Datatype/Txs.reverse` is its mirror. -/
theorem At.«Datatype/Txs.reverse» : At 318 «Datatype/Txs.reverse» :=
  ⟨_, rfl, datatypeSoundness.«Datatype/Txs.reverse_heq»⟩

/-- The global of the definition {lit}`Datatype/Txs.drop` is its mirror. -/
theorem At.«Datatype/Txs.drop» : At 320 «Datatype/Txs.drop» :=
  ⟨_, rfl, datatypeSoundness.«Datatype/Txs.drop_heq»⟩

/-- The global of the definition {lit}`Datatype.isListTx` is its mirror. -/
theorem At.«Datatype.isListTx» : At 338 «Datatype.isListTx» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.isListTx_heq»⟩

/-- The global of the definition {lit}`Datatype.namedTx` is its mirror. -/
theorem At.«Datatype.namedTx» : At 339 «Datatype.namedTx» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.namedTx_heq»⟩

/-- The global of the definition {lit}`Datatype.elems` is its mirror. -/
theorem At.«Datatype.elems» : At 340 «Datatype.elems» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.elems_heq»⟩

/-- The global of the definition {lit}`Datatype.nthTx` is its mirror. -/
theorem At.«Datatype.nthTx» : At 341 «Datatype.nthTx» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.nthTx_heq»⟩

/-- The global of the definition {lit}`Datatype.kwData` is its mirror. -/
theorem At.«Datatype.kwData» : At 387 «Datatype.kwData» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.kwData_heq»⟩

/-- The global of the definition {lit}`Datatype.kwTreeData` is its mirror. -/
theorem At.«Datatype.kwTreeData» : At 388 «Datatype.kwTreeData» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.kwTreeData_heq»⟩

/-- The global of the definition {lit}`Datatype.kwDefn` is its mirror. -/
theorem At.«Datatype.kwDefn» : At 391 «Datatype.kwDefn» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.kwDefn_heq»⟩

/-- The global of the definition {lit}`Datatype.kwGeneric` is its mirror. -/
theorem At.«Datatype.kwGeneric» : At 396 «Datatype.kwGeneric» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.kwGeneric_heq»⟩

/-- The global of the definition {lit}`Datatype.memberName` is its mirror. -/
theorem At.«Datatype.memberName» : At 401 «Datatype.memberName» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.memberName_heq»⟩

/-- The global of the definition {lit}`Datatype.xpStep` is its mirror. -/
theorem At.«Datatype.xpStep» : At 474 «Datatype.xpStep» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.xpStep_heq»⟩

/-- The global of the definition {lit}`Datatype.genericStep` is its mirror. -/
theorem At.«Datatype.genericStep» : At 475 «Datatype.genericStep» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.genericStep_heq»⟩

/-- The global of the definition {lit}`Datatype.expandTyped` is its mirror. -/
theorem At.«Datatype.expandTyped» : At 476 «Datatype.expandTyped» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.expandTyped_heq»⟩

/-- The global of the definition {lit}`Datatype.markersFirst` is its mirror. -/
theorem At.«Datatype.markersFirst» : At 484 «Datatype.markersFirst» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.markersFirst_heq»⟩

/-- The global of the definition {lit}`Datatype.kernelForms` is its mirror. -/
theorem At.«Datatype.kernelForms» : At 485 «Datatype.kernelForms» :=
  ⟨_, rfl, datatypeSoundness.«Datatype.kernelForms_heq»⟩

/-- The global of the definition {lit}`Recognize.markers` is its mirror. -/
theorem At.«Recognize.markers» : At 531 «Recognize.markers» :=
  ⟨_, rfl, datatypeSoundness.«Recognize.markers_heq»⟩

/-- The global of the definition {lit}`Recognize.insertRecognizers` is its mirror. -/
theorem At.«Recognize.insertRecognizers» : At 543 «Recognize.insertRecognizers» :=
  ⟨_, rfl, datatypeSoundness.«Recognize.insertRecognizers_heq»⟩

/-- The global of the definition {lit}`Eval.valQuote` is its mirror. -/
theorem At.«Eval.valQuote» : At 558 «Eval.valQuote» :=
  ⟨_, rfl, datatypeSoundness.«Eval.valQuote_heq»⟩

/-- The global of the definition {lit}`Eval.valUnit` is its mirror. -/
theorem At.«Eval.valUnit» : At 559 «Eval.valUnit» :=
  ⟨_, rfl, datatypeSoundness.«Eval.valUnit_heq»⟩

/-- The global of the definition {lit}`Eval.valPair` is its mirror. -/
theorem At.«Eval.valPair» : At 560 «Eval.valPair» :=
  ⟨_, rfl, datatypeSoundness.«Eval.valPair_heq»⟩

/-- The global of the definition {lit}`Eval.listOf` is its mirror. -/
theorem At.«Eval.listOf» : At 565 «Eval.listOf» :=
  ⟨_, rfl, datatypeSoundness.«Eval.listOf_heq»⟩

/-- The global of the definition {lit}`Eval.next` is its mirror. -/
theorem At.«Eval.next» : At 581 «Eval.next» :=
  ⟨_, rfl, datatypeSoundness.«Eval.next_heq»⟩

/-- The global of the definition {lit}`Eval.level` is its mirror. -/
theorem At.«Eval.level» : At 582 «Eval.level» :=
  ⟨_, rfl, datatypeSoundness.«Eval.level_heq»⟩

/-- The global of the definition {lit}`charsFixed` is its mirror. -/
theorem At.«charsFixed» : At 591 «charsFixed» :=
  ⟨_, rfl, datatypeSoundness.«charsFixed_heq»⟩

/-- The global of the definition {lit}`srcForm` is its mirror. -/
theorem At.«srcForm» : At 592 «srcForm» :=
  ⟨_, rfl, datatypeSoundness.«srcForm_heq»⟩

/-- The global of the definition {lit}`implName` is its mirror. -/
theorem At.«implName» : At 594 «implName» :=
  ⟨_, rfl, datatypeSoundness.«implName_heq»⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeLoad

end
