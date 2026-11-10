/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebHost.Compiler
public import GebMirror.Authoring

set_option doc.verso true

/-!
# Proof-source execution and replay

The host reads a program's manifest and a proof document, compiles the program with the
bootstrap compiler, and runs the proof-source reader, prover and checker written in Geb.
Certificates carry their format, theory, profile and checked program. Replay compares that program
with the current compilation and checks the saved derivations against the source statements.
The host writes an output only after all checks succeed.

## Main definitions

* {lit}`GebHost.Authoring.readDocument` reads authoring or strict durable documents.
* {lit}`GebHost.Authoring.checkExamples` checks the tree-valued examples in a program's notes.
* {lit}`GebHost.Authoring.execute` proves or replays a proof document.

## Tags

authoring, proof script, certificate, document, command line
-/

open Geb Geb.Kernel Geb.Kernel.Document
open scoped FinEnum

@[expose] public section

namespace GebHost.Authoring

/-- A document from its authoring spelling or its strict durable encoding. -/
def readDocument (path : System.FilePath) (profile : Profile) : IO Durable := do
  IO.ofExcept profile.check
  let text := Command.chars (← IO.FS.readBinFile path)
  if let some (header, doc) := readBasic text then
    let profile' ← IO.ofExcept (Profile.parse header)
    let d : Durable := ⟨profile', doc⟩
    unless decide (d.profile.toSExp = profile.toSExp) do
      throw <| IO.userError s!"{path}: document profile differs from the manifest"
    return d
  let some d := readDoc text
    | throw <| IO.userError s!"{path}: malformed source document"
  if d.items.any (headIs kwDoc) then
    throw <| IO.userError s!"{path}: malformed durable document"
  return ⟨profile, d⟩

/-- The inverse of the host's byte-to-character conversion. -/
def bytesOf (cs : List Char) : ByteArray :=
  ⟨(cs.map fun c ↦ c.toNat.toUInt8).toArray⟩

/-- The authoring spelling of a document, with every decoration retained. -/
def sourceBytes (d : Doc) : ByteArray :=
  bytesOf (printAt (defaultLayout .profile 100 d) d)

/-- Compile source with the current Geb compiler and retain its checked bundle; a rejection is
the diagnostic of what was compiled from the sources given
({name}`GebHost.Compiler.diagnostic`). -/
def compile (what : String) (sources : List Compiler.Source) (text : ByteArray) : IO Tree := do
  let input := ofBytes text
  let out := GebBoot.«Compile.bundleOf» input
  if out.label == 0 then
    throw <| IO.userError
      (Compiler.diagnostic what sources (Compiler.rejectionOf input)).render
  let b := GebBoot.«Prelude.get» out
  unless (unbundle b).isSome do throw <| IO.userError "compiler returned a malformed bundle"
  return b

/-- The sources of a manifest in the authoring spelling, as written, in which a rejected program's
occurrences are found; a source in a strict encoding has no lines and columns to report. -/
def writtenSources (paths : List System.FilePath) : IO (List Compiler.Source) :=
  paths.filterMapM fun path ↦ do
    let s ← Compiler.Source.read path
    return if (readBasic s.text).isSome then none else some s

/-- A manifest's compiled program and the text from which its examples are checked. -/
def readProgram (path : System.FilePath) : IO (Manifest × ByteArray × Tree) := do
  let m ← Manifest.read path
  let paths := Manifest.sourcePaths path m
  let text ← paths.foldlM (init := ByteArray.empty) fun acc src ↦ do
    let d ← readDocument src m.profile
    discard <| IO.ofExcept (notesOf d.doc)
    return (acc ++ sourceBytes d.doc.eraseNotes).push 10
  let b ← compile path.toString (← writtenSources paths) text
  let some ds := unbundle b | throw <| IO.userError "malformed bundle"
  IO.ofExcept (m.checkEntries (ds.map fun d ↦ String.ofList d.1))
  return (m, text, b)

/-- Check every note's example by compiling and evaluating its two tree-valued expressions. -/
def checkExamples (manifest : System.FilePath) (m : Manifest) (text : ByteArray) : IO Unit := do
  for path in Manifest.sourcePaths manifest m do
    let d ← readDocument path m.profile
    let notes ← IO.ofExcept (notesOf d.doc)
    for (name, fields) in notes do
      let declaration := ".".intercalate (name.map String.ofList)
      for field in fields do
        if let .example term value := field then
          let suffix := "\n(def __geb_example_actual (lam ((input T)) ".toList ++
            canonOf term ++ "))\n".toList ++
            "(def __geb_example_expected (lam ((input T)) ".toList ++
            canonOf value ++ "))\n".toList
          let b ← compile path.toString [] (text ++ bytesOf suffix)
          let some actual := runEntry b "__geb_example_actual".toList (leaf 0)
            | throw <| IO.userError s!"{path}: example of {declaration} does not return a tree"
          let some expected := runEntry b "__geb_example_expected".toList (leaf 0)
            | throw <| IO.userError s!"{path}: expected value of {declaration} \
                does not return a tree"
          unless decide (actual = expected) do
            throw <| IO.userError s!"{path}: example of {declaration} \
              differs from its expected value"

/-- The certificate format of a proof source's version: version 0 saves one declaration for each
theorem, and version 1 saves each theorem followed by its companion. -/
def formatOf (version : Tree) : Tree :=
  nameTree (if decide (version = leaf 0) then "geb-proof/v1" else "geb-proof/v2").toList

/-- The version of a proof source, read against the program's statements. -/
def versionOf (program input : Tree) : Except String Tree :=
  let result := GebMirror.Metalogic.«Authoring.version» program input
  if result.label == 0 then .error "invalid proof source"
  else .ok (GebMirror.Metalogic.«Prelude.get» result)

/-- The certificate format and theory are separate from the kernel image's wire version. -/
def envelope (format : Tree) (profile : Profile) (program certificate : Tree) : Tree :=
  mk 0 [format, nameTree "free-topos/base/v1".toList,
    nameTree (canonOf profile.toSExp), program, certificate]

/-- Read a certificate only for the format, program and theory against which it was produced. -/
def certificateOf (expected : Tree) (profile : Profile) (program : Tree) (saved : Tree) :
    Except String Tree :=
  match saved.children with
  | [format, theory, header, source, cert] =>
    if saved.label == 0 && decide (format = expected) &&
        decide (theory = nameTree "free-topos/base/v1".toList) &&
        decide (header = nameTree (canonOf profile.toSExp)) && decide (source = program) then
      .ok cert
    else .error "certificate format, theory, profile, or compiled program differs"
  | _ => .error "malformed certificate envelope"

/-- Prove or replay, reporting rejection without replacing an existing output. -/
def execute (mode manifest proofs certificate : String) : IO UInt32 := do
  let (m, text, b) ← readProgram manifest
  checkExamples manifest m text
  let d ← readDocument proofs m.profile
  let input := ofBytes (sourceBytes d.doc)
  let format := formatOf (← IO.ofExcept ((versionOf b input).mapError (s!"{proofs}: {·}")))
  match mode with
  | "prove" =>
    let result := GebMirror.Metalogic.«Authoring.prove» b input
    if result.label == 0 then
      throw <| IO.userError s!"{proofs}: invalid proof source or normalization \
        did not prove a statement"
    let cert := GebMirror.Metalogic.«Prelude.get» result
    unless (GebMirror.Metalogic.«Authoring.replay» b input cert).label == 1 do
      throw <| IO.userError s!"{proofs}: generated certificate does not replay"
    IO.FS.writeBinFile certificate (writeImage (envelope format m.profile b cert))
  | "replay" =>
    let some saved := readImage (← IO.FS.readBinFile certificate)
      | throw <| IO.userError s!"{certificate}: malformed certificate image"
    let cert ← IO.ofExcept (certificateOf format m.profile b saved)
    unless (GebMirror.Metalogic.«Authoring.replay» b input cert).label == 1 do
      throw <| IO.userError s!"{proofs}: certificate does not prove these statements"
  | _ => throw <| IO.userError "expected prove or replay"
  IO.println s!"{proofs}: {mode} accepted; examples checked"
  return 0

end GebHost.Authoring

end
