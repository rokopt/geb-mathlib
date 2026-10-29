/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebBench.Prototypes.FreeTopos.TranslationProofs
public import Geb.Prototypes.FreeTopos.Internal.ByMachine
public import GebTests.Prototypes.FreeTopos.Expansion
public import GebTests.Prototypes.FreeTopos.Stored
public import GebTests.Prototypes.FreeTopos.Substitution

set_option doc.verso true in
/-!
# The developments translated by steps of the machine

The developments of weakening, of substitution and of the expansion's identity, read from their
certificates, translated by {name}`Geb.FreeTopos.Internal.devByMachine`, each join whose sides
the environment machine joins replaced by two steps of the machine. For each: its number of
theorems and of those translated, the bytes of the text of its certificate and of the
translation's, the milliseconds of the translation, and the least of three times the check of
the development and of the translation read back from its text take, in milliseconds.

## Main definitions

* {lit}`measure` — the measurement of one development.
* {lit}`run` — the measurements.

## Tags

internal language, abstract machine, certificate, translation, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.ByMachine

open Geb Geb.FreeTopos
open GebTests.Prototypes.FreeTopos
open GebBench.Prototypes.FreeTopos.TranslationProofs (timeUs)

set_option compiler.extract_closed false in
/-- The measurement of the development a certificate stores, with the constants of {lit}`G`,
printed, and an error where a check fails. -/
def measure (name : String) (G : Internal.Globals) : IO Unit := do
  let text ← IO.FS.readFile s!"bootstrap/certificates/{name}.cert"
  let some ds := Stored.declsOfText text | throw (IO.userError s!"{name} does not read")
  let t₀ ← IO.monoMsNow
  let cds ← IO.lazyPure fun _ ↦ Internal.devByMachine G #[] 4096 ds
  let translated := (cds.filter fun | .conv _ _ => true | _ => false).length
  let t₁ ← IO.monoMsNow
  let some text' := (Stored.convDeclsToNats cds).map fun ns ↦ " ".intercalate (ns.map toString)
    | throw (IO.userError s!"{name}: the translation does not store")
  let some cds' := Stored.convDeclsOfText text'
    | throw (IO.userError s!"{name}: the translation's text does not read")
  let (ok₁, tb) ← timeUs fun _ ↦ (Internal.checkDev G #[] ds).isSome
  let (ok₂, tc) ← timeUs fun _ ↦ (Internal.checkConvDev G #[] cds').isSome
  if !(ok₁ && ok₂) then throw (IO.userError s!"{name}: a check fails")
  IO.println s!"{name},{ds.length},{translated},{text.utf8ByteSize},{text'.utf8ByteSize},{t₁ - t₀},\
    {tb / 1000},{tc / 1000}"

set_option compiler.extract_closed false in
/-- The measurements. Closed terms are not extracted, so that each runs when it is timed rather
than when the program starts. -/
def run : IO Unit := do
  IO.println "certificate,theorems,translated,bytes,translated_bytes,translation_milliseconds,\
    check_milliseconds,translated_check_milliseconds"
  if let some P := Weakening.program then measure "weakening" (Weakening.Prog.G P)
  if let some P := Substitution.program then measure "substitution" (Weakening.Prog.G P)
  if let some P := Expansion.program then measure "expansion" (Weakening.Prog.G P)

end GebBench.Prototypes.FreeTopos.ByMachine

end
