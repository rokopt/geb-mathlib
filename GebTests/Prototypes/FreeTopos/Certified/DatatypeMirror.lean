/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses
public import GebTests.Prototypes.FreeTopos.Certified.DatatypePasses

set_option doc.verso true in
/-!
# The compilers' functions the soundness reads are their mirror's definitions

The soundness of a whole program of the datatype language's stage-1 compiler is read in Lean at
the values of the globals the kernel loads for the compilers' definitions
({lit}`DatatypePasses.PassFns`, {lit}`DatatypeStatements.EvalFns`,
{lit}`DatatypeHypotheses.HypFns`), of which it assumes that they are loaded and nothing else.
The kernel loads the compilers' program to its mirror's definitions
({lit}`DatatypeLoad`), the Lean the bootstrap compiler emits from the program, and the program
is the one the soundness is stated in: its definitions' trees are those loaded, and its
manifest's entries are at the indices the loading has them at, as Lean's evaluator decides
({lit}`DatatypeAccepted.mirrorTrees`, {lit}`DatatypeAccepted.mirrorIndexed`). The values the
soundness reads are therefore the mirror's definitions, functions of Lean defined by the
equations the compilers' sources state.

## Main definitions

* {lit}`passFns`, {lit}`evalFns`, {lit}`hypFns` — the functions the soundness reads, as the
  mirror defines them.

## Main statements

* {lit}`globals_eq` — the globals the kernel loads for the soundness's program are the mirror's.
* {lit}`loaded_at` — a loaded value at an entry's name is the entry's mirror.
* {lit}`passFns_loaded`, {lit}`evalFns_loaded`, {lit}`hypFns_loaded` — the mirror's definitions
  are the loaded values.

## Tags

internal language, datatypes, kernel, loading, mirror, test
-/

set_option doc.verso true

@[expose] public section

open GebMirror.DatatypeSoundness

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypeLoad (At)
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (PassFns exists_passFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements (EvalFns exists_evalFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses (HypFns exists_hypFns)
open GebMirror (datatypeSoundness)
open scoped FinEnum

variable {PST : Prog × Defs × Defs3}

/-- The globals the kernel loads for the program the soundness is stated in are those it loads
for the mirror's program: the two programs have the same definitions
({name}`DatatypeAccepted.mirrorTrees`). -/
theorem globals_eq (L : Translated PST) : L.Gk = datatypeSoundness.globals := by
  have ht := mirrorTrees
  rw [L.bundledTypes_eq] at ht
  have hds : L.ds.map Prod.snd = datatypeSoundness := of_decide_eq_true ht
  have hl := L.load
  rw [hds, datatypeSoundness.load_globals] at hl
  exact (Option.some.inj hl).symm

/-- An entry of the manifest has, among the soundness's constants, the index after the
library's that the loading has it at ({name}`DatatypeAccepted.mirrorIndexed`). -/
theorem index_eq (L : Translated PST) {name : String} {k : ℕ}
    (hm : (name, k) ∈ mirrorIndices) : PST.1.idx name = lib.length + k := by
  have hi := mirrorIndexed
  rw [L.bundledTypes_eq] at hi
  have hp := of_decide_eq_true (List.all_eq_true.mp hi (name, k) hm)
  simp [L.idx, Weakening.defIndex, hp]

/-- An entry of the manifest, by its position among the entries. -/
theorem entry (i : ℕ) {name : String} {k : ℕ} (h : mirrorIndices[i]? = some (name, k)) :
    (name, k) ∈ mirrorIndices :=
  List.mem_of_getElem? h

/-- A loaded value at an entry's name is the entry's mirror: the global at the entry's index
is the one whose denotation is the mirror's definition. -/
theorem loaded_at (L : Translated PST) {name : String} {T : Kernel.Tree} {f : Kernel.Ty.den T}
    (h : Loaded L.Gk PST.1.idx name T f) {k : ℕ} (hm : (name, k) ∈ mirrorIndices)
    {m : Kernel.Ty.den T} (ha : At k m) : Loaded L.Gk PST.1.idx name T m := by
  obtain ⟨n, hn, hG⟩ := h
  obtain ⟨g, hg, hgm⟩ := ha
  obtain rfl : n = k := Nat.add_left_cancel (hn.symm.trans (index_eq L hm))
  rw [globals_eq L] at hG
  obtain rfl : (⟨T, f⟩ : Kernel.Glob) = g := Option.some.inj (hG.symm.trans hg)
  obtain rfl : f = m := eq_of_heq hgm
  exact ⟨n, hn, by rw [globals_eq L]; exact hG⟩

/-- The functions of the compiler's passes that the mirror defines. -/
def passFns : PassFns where
  expandTyped := «Datatype.expandTyped»
  nothing := «Typing/OName.nothing»
  checkAll := «Typing.checkAll»
  env0 := «Typing.env0»
  markersFirst := «Datatype.markersFirst»
  insertRecognizers := «Recognize.insertRecognizers»
  kernelForms := «Datatype.kernelForms»
  readProgram := «Reader.readProgram»
  get := «Prelude.get»
  isSome := «Prelude.isSome»
  checkProgram := «Check.checkProgram»

/-- The mirror's definitions of those functions are the values of the globals the kernel
loads. -/
theorem passFns_loaded (L : Translated PST) : passFns.Loaded L.Gk PST.1.idx := by
  obtain ⟨f, hf⟩ := exists_passFns L
  exact
    { expandTyped := loaded_at L hf.expandTyped (entry 48 rfl) At.«Datatype.expandTyped»
      nothing := loaded_at L hf.nothing (entry 33 rfl) At.«Typing/OName.nothing»
      checkAll := loaded_at L hf.checkAll (entry 34 rfl) At.«Typing.checkAll»
      env0 := loaded_at L hf.env0 (entry 25 rfl) At.«Typing.env0»
      markersFirst := loaded_at L hf.markersFirst (entry 49 rfl) At.«Datatype.markersFirst»
      insertRecognizers := loaded_at L hf.insertRecognizers
        (entry 52 rfl) At.«Recognize.insertRecognizers»
      kernelForms := loaded_at L hf.kernelForms (entry 50 rfl) At.«Datatype.kernelForms»
      readProgram := loaded_at L hf.readProgram (entry 20 rfl) At.«Reader.readProgram»
      get := loaded_at L hf.get (entry 3 rfl) At.«Prelude.get»
      isSome := loaded_at L hf.isSome (entry 2 rfl) At.«Prelude.isSome»
      checkProgram := loaded_at L hf.checkProgram (entry 21 rfl) At.«Check.checkProgram» }

/-- The functions the soundness's conclusion calls that the mirror defines. -/
def evalFns : EvalFns where
  just := «Prelude.some»
  nth := «Prelude.nth»
  get := «Prelude.get»
  isSome := «Prelude.isSome»
  level := «Eval.level»
  next := «Eval.next»
  valQuote := «Eval.valQuote»
  valUnit := «Eval.valUnit»
  valPair := «Eval.valPair»
  listOf := «Eval.listOf»
  memberOf := «Typing.memberOf»
  lookupName := «Typing.lookupName»
  envDefs := «Typing.envDefs»
  hasName := «Typing.hasName»
  envNoms := «Typing.envNoms»
  recognizerName := «Typing.recognizerName»
  indexOf := «Reader.indexOf»
  envMs := «Typing.envMs»

/-- The mirror's definitions of those functions are the values of the globals the kernel
loads. -/
theorem evalFns_loaded (L : Translated PST) : evalFns.Loaded L.Gk PST.1.idx := by
  obtain ⟨f, hf⟩ := exists_evalFns L
  exact
    { just := loaded_at L hf.just (entry 1 rfl) At.«Prelude.some»
      nth := loaded_at L hf.nth (entry 6 rfl) At.«Prelude.nth»
      get := loaded_at L hf.get (entry 3 rfl) At.«Prelude.get»
      isSome := loaded_at L hf.isSome (entry 2 rfl) At.«Prelude.isSome»
      level := loaded_at L hf.level (entry 58 rfl) At.«Eval.level»
      next := loaded_at L hf.next (entry 57 rfl) At.«Eval.next»
      valQuote := loaded_at L hf.valQuote (entry 53 rfl) At.«Eval.valQuote»
      valUnit := loaded_at L hf.valUnit (entry 54 rfl) At.«Eval.valUnit»
      valPair := loaded_at L hf.valPair (entry 55 rfl) At.«Eval.valPair»
      listOf := loaded_at L hf.listOf (entry 56 rfl) At.«Eval.listOf»
      memberOf := loaded_at L hf.memberOf (entry 30 rfl) At.«Typing.memberOf»
      lookupName := loaded_at L hf.lookupName (entry 26 rfl) At.«Typing.lookupName»
      envDefs := loaded_at L hf.envDefs (entry 22 rfl) At.«Typing.envDefs»
      hasName := loaded_at L hf.hasName (entry 27 rfl) At.«Typing.hasName»
      envNoms := loaded_at L hf.envNoms (entry 23 rfl) At.«Typing.envNoms»
      recognizerName := loaded_at L hf.recognizerName (entry 28 rfl) At.«Typing.recognizerName»
      indexOf := loaded_at L hf.indexOf (entry 15 rfl) At.«Reader.indexOf»
      envMs := loaded_at L hf.envMs (entry 24 rfl) At.«Typing.envMs» }

/-- The functions the soundness's remaining hypotheses call that the mirror defines. -/
def hypFns : HypFns where
  genericStep := «Datatype.genericStep»
  xpStep := «Datatype.xpStep»
  and := «Prelude.and»
  or := «Prelude.or»
  isListTx := «Datatype.isListTx»
  namedTx := «Datatype.namedTx»
  nthTx := «Datatype.nthTx»
  elems := «Datatype.elems»
  kwGeneric := «Datatype.kwGeneric»
  kwData := «Datatype.kwData»
  kwTreeData := «Datatype.kwTreeData»
  kwDefn := «Datatype.kwDefn»
  kwDef := «Reader.kwDef»
  kwDeftype := «Reader.kwDeftype»
  kwDefnum := «Reader.kwDefnum»
  kwT := «Reader.kwT»
  kwUnit := «Reader.kwUnit»
  srcForm := «srcForm»
  expandNums := «Reader.expandNums»
  numOf := «Reader.numOf»
  nameOf := «Reader.nameOf»
  node2 := «Reader.node2»
  reverse := «Datatype/Txs.reverse»
  drop := «Datatype/Txs.drop»
  kernelForms := «Datatype.kernelForms»
  markers := «Recognize.markers»
  markerCtors := «Typing.markerCtors»
  markerNames := «Typing.markerNames»
  isAtom := «Reader.isAtom»
  named := «Reader.named»
  length := «Prelude.length»
  numeral := «Reader.numeral»
  decimalChars := «Typing.decimalChars»
  charsFixed := «charsFixed»
  implName := «implName»
  memberName := «Datatype.memberName»
  get := «Prelude.get»
  isSome := «Prelude.isSome»
  just := «Prelude.some»
  indexOf := «Reader.indexOf»

/-- The mirror's definitions of those functions are the values of the globals the kernel
loads. -/
theorem hypFns_loaded (L : Translated PST) : hypFns.Loaded L.Gk PST.1.idx := by
  obtain ⟨f, hf⟩ := exists_hypFns L
  exact
    { genericStep := loaded_at L hf.genericStep (entry 47 rfl) At.«Datatype.genericStep»
      xpStep := loaded_at L hf.xpStep (entry 46 rfl) At.«Datatype.xpStep»
      and := loaded_at L hf.and (entry 4 rfl) At.«Prelude.and»
      or := loaded_at L hf.or (entry 5 rfl) At.«Prelude.or»
      isListTx := loaded_at L hf.isListTx (entry 37 rfl) At.«Datatype.isListTx»
      namedTx := loaded_at L hf.namedTx (entry 38 rfl) At.«Datatype.namedTx»
      nthTx := loaded_at L hf.nthTx (entry 40 rfl) At.«Datatype.nthTx»
      elems := loaded_at L hf.elems (entry 39 rfl) At.«Datatype.elems»
      kwGeneric := loaded_at L hf.kwGeneric (entry 44 rfl) At.«Datatype.kwGeneric»
      kwData := loaded_at L hf.kwData (entry 41 rfl) At.«Datatype.kwData»
      kwTreeData := loaded_at L hf.kwTreeData (entry 42 rfl) At.«Datatype.kwTreeData»
      kwDefn := loaded_at L hf.kwDefn (entry 43 rfl) At.«Datatype.kwDefn»
      kwDef := loaded_at L hf.kwDef (entry 12 rfl) At.«Reader.kwDef»
      kwDeftype := loaded_at L hf.kwDeftype (entry 13 rfl) At.«Reader.kwDeftype»
      kwDefnum := loaded_at L hf.kwDefnum (entry 14 rfl) At.«Reader.kwDefnum»
      kwT := loaded_at L hf.kwT (entry 10 rfl) At.«Reader.kwT»
      kwUnit := loaded_at L hf.kwUnit (entry 11 rfl) At.«Reader.kwUnit»
      srcForm := loaded_at L hf.srcForm (entry 60 rfl) At.«srcForm»
      expandNums := loaded_at L hf.expandNums (entry 17 rfl) At.«Reader.expandNums»
      numOf := loaded_at L hf.numOf (entry 18 rfl) At.«Reader.numOf»
      nameOf := loaded_at L hf.nameOf (entry 8 rfl) At.«Reader.nameOf»
      node2 := loaded_at L hf.node2 (entry 19 rfl) At.«Reader.node2»
      reverse := loaded_at L hf.reverse (entry 35 rfl) At.«Datatype/Txs.reverse»
      drop := loaded_at L hf.drop (entry 36 rfl) At.«Datatype/Txs.drop»
      kernelForms := loaded_at L hf.kernelForms (entry 50 rfl) At.«Datatype.kernelForms»
      markers := loaded_at L hf.markers (entry 51 rfl) At.«Recognize.markers»
      markerCtors := loaded_at L hf.markerCtors (entry 32 rfl) At.«Typing.markerCtors»
      markerNames := loaded_at L hf.markerNames (entry 29 rfl) At.«Typing.markerNames»
      isAtom := loaded_at L hf.isAtom (entry 7 rfl) At.«Reader.isAtom»
      named := loaded_at L hf.named (entry 9 rfl) At.«Reader.named»
      length := loaded_at L hf.length (entry 0 rfl) At.«Prelude.length»
      numeral := loaded_at L hf.numeral (entry 16 rfl) At.«Reader.numeral»
      decimalChars := loaded_at L hf.decimalChars (entry 31 rfl) At.«Typing.decimalChars»
      charsFixed := loaded_at L hf.charsFixed (entry 59 rfl) At.«charsFixed»
      implName := loaded_at L hf.implName (entry 61 rfl) At.«implName»
      memberName := loaded_at L hf.memberName (entry 45 rfl) At.«Datatype.memberName»
      get := loaded_at L hf.get (entry 3 rfl) At.«Prelude.get»
      isSome := loaded_at L hf.isSome (entry 2 rfl) At.«Prelude.isSome»
      just := loaded_at L hf.just (entry 1 rfl) At.«Prelude.some»
      indexOf := loaded_at L hf.indexOf (entry 15 rfl) At.«Reader.indexOf» }

end GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror

end
