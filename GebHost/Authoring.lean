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

A proof document from version 2 names the documents whose theorems it cites, by forms
{lit}`(import PATH)`. The host resolves them, each against the directory of the document that
imports it, and gives the runner the development: the imported documents, each before those
importing it, and the document last. The runner reads the theorems of all of them as one list, so
the development's certificate holds the declarations of the imported theorems before the
document's own, and replays without the certificates of the imported documents.

A proof document from version 2 may name its program, by a form {lit}`(program NAME)`: the
manifest of that program name in the document's directory, or else in the nearest directory above
it that holds one. The host proves a document against the program it names where no manifest is
given, and a manifest given takes its place. Only the document proved is consulted: the documents
it imports are read against its program, so that a document holding in every program names none
and a development is proved again in a larger program by a document that imports it.

Where the runner rejects a development it reports a reason and the theorem concerned, which the
host writes as a diagnostic at the theorem's name in the document that states it
({name}`GebHost.Compiler.Diagnostic`).

## Main definitions

* {lit}`GebHost.Authoring.readDocument` reads authoring or strict durable documents.
* {lit}`GebHost.Authoring.checkExamples` checks the tree-valued examples in a program's notes.
* {lit}`GebHost.Authoring.development` reads a proof document after the documents it imports.
* {lit}`GebHost.Authoring.manifestOf` finds the manifest of the program a proof document names.
* {lit}`GebHost.Authoring.execute` proves or replays a development.
* {lit}`GebHost.Authoring.checkFile` checks a program's source or a proof document and writes
  nothing.

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

/-! ## Developments -/

/-- The head of a proof document, {lit}`proofs`. -/
def kwProofs : List Char := "proofs".toList

/-- The head of an import, {lit}`import`. -/
def kwImport : List Char := "import".toList

/-- The head of a theorem, {lit}`theorem`. -/
def kwTheorem : List Char := "theorem".toList

/-- The head of the form naming a document's program, {lit}`program`. -/
def kwProgram : List Char := "program".toList

/-- The atoms of the forms {lit}`(HEAD ATOM)` of a given head among those of a proof document's
form {lit}`(proofs V …)`, or what rejects them: such a form in a document of a version before 2,
which reads none. -/
def headerAtoms (head : List Char) (d : Doc) : Except String (List String) :=
  match d.items.find? (headIs kwProofs) with
  | some root =>
    let atoms := root.children.filterMap fun c ↦
      match c.children with
      | [_, p] => if headIs head c && p.children.isEmpty then p.label.2.map String.ofList else none
      | _ => none
    let version := root.children[1]?.bind (·.label.2)
    if atoms.isEmpty || version == some ['2'] || version == some ['3'] then .ok atoms
    else .error s!"a document of a version before 2 has no form ({String.ofList head} …)"
  | none => .ok []

/-- The paths a proof document imports: the atoms of its forms {lit}`(import PATH)`. -/
def importsOf (d : Doc) : Except String (List String) := headerAtoms kwImport d

/-- The name of the program a proof document names, by its form {lit}`(program NAME)`, where it
names one; a document names no more than one. -/
def programOf (d : Doc) : Except String (Option String) :=
  (headerAtoms kwProgram d).bind fun names ↦
    match names with
    | [] => .ok none
    | [name] => .ok (some name)
    | _ => .error "the document names more than one program"

/-- The greatest number of documents of a development. -/
def documentLimit : Nat := 4096

/-- The documents of a development: those a proof document imports, and those they import, each
before the documents importing it, and the document last. An import is a path as a manifest's
source is ({name}`Geb.Kernel.Manifest.validSource`), resolved against the importing document's
directory, and a document is read once however many import it. An import that does not read is
reported with the document importing it, and imports that return to a document are rejected. -/
def development (proofs : System.FilePath) (profile : Profile) :
    IO (List (System.FilePath × Durable)) := do
  let mut seen : List (String × Durable × List String) := []
  let mut work : List (String × Option String) := [(proofs.toString, none)]
  for _ in [0:documentLimit] do
    match work with
    | [] => break
    | (p, importer) :: rest =>
      work := rest
      if seen.any (·.1 == p) then continue
      let d ← match importer with
        | none => readDocument p profile
        | some i =>
          try readDocument p profile
          catch e => throw <| IO.userError s!"{i}: the import {p} does not read: {e}"
      let imports ← (← IO.ofExcept ((importsOf d.doc).mapError (s!"{p}: {·}"))).mapM fun s ↦ do
        unless Manifest.validSource s do
          throw <| IO.userError s!"{p}: the import {s} is not a relative path below the document"
        return (Manifest.resolve p s).toString
      seen := seen ++ [(p, d, imports)]
      work := imports.map (·, some p) ++ work
  unless work.isEmpty do
    throw <| IO.userError s!"{proofs}: the development has more than {documentLimit} documents"
  let mut ordered : List (System.FilePath × Durable) := []
  for _ in seen do
    for (p, d, imports) in seen do
      if !ordered.any (·.1.toString == p) &&
          imports.all (fun i ↦ ordered.any (·.1.toString == i)) then
        ordered := ordered ++ [(System.FilePath.mk p, d)]
  unless ordered.length == seen.length do
    throw <| IO.userError s!"{proofs}: the imports of the development return to a document"
  return ordered

/-- The sources of a development as the runner written in Geb reads them: the node of its
documents, each the node of its characters in the authoring spelling. -/
def sourcesTree (docs : List (System.FilePath × Durable)) : Tree :=
  mk 0 (docs.map fun d ↦ ofBytes (sourceBytes d.2.doc))

/-- The certificate format of a development's version, that of its last document: version 0
saves one declaration for each theorem, and the later versions save each theorem followed by its
companion, version 2 the theorems of the documents imported before its own, and version 3 the
connectives' rules before every theorem. -/
def formatOf (version : Tree) : Tree :=
  nameTree (match version.label with
    | 0 => "geb-proof/v1"
    | 1 => "geb-proof/v2"
    | 2 => "geb-proof/v3"
    | _ => "geb-proof/v4").toList

/-- Why the reader and prover written in Geb reject a development: the reason's number and the
theorem it concerns, as {lit}`bootstrap/authoring.geb` reports them. -/
def reasonOf (report : Tree) : Nat × Option String :=
  match report.children with
  | [why, name] =>
    (why.label, (ofNameTree name).bind fun cs ↦
      if cs.isEmpty then none else some (String.ofList cs))
  | _ => (0, none)

/-- The message of a reason and the theorem it concerns. -/
def reasonMessage (why : Nat) (name : String) : String :=
  match why with
  | 1 => s!"the theorem {name} is declared before"
  | 2 => s!"the theorem {name} is not (theorem NAME STATEMENT (by SCRIPT)), or its statement \
    does not read"
  | 3 => s!"the script of the theorem {name} does not read"
  | 4 => s!"the script of the theorem {name} does not prove it"
  | 5 => s!"the sides of the theorem {name} have no weak normal forms within the budget"
  | 6 => "the derivations of the development do not check"
  | _ => "a document of the development is not (proofs V FORM…) of a version this host reads \
    with a theorem, or a document of version 0 is combined with others, or a document imports \
    one of a later version"

/-- The span of the name of a theorem in a document as written: of the last theorem of that name
among the forms of its form {lit}`(proofs V …)`. -/
def theoremSpan (text : List Char) (name : String) : Option Locate.Span :=
  match Locate.locate text with
  | .ok items =>
    ((items.filter (Locate.headIs kwProofs)).flatMap (·.children)).reverse.findSome? fun t ↦
      if Locate.headIs kwTheorem t then
        t.children[1]?.bind fun n ↦
          if n.label.2 == some name.toList then some n.label.1 else none
      else none
  | .error _ => none

/-- The diagnostic of a development the runner written in Geb rejects: at the name of the
theorem the report concerns, in the last document as written that states it, and else at the
proof document without a position. -/
def rejection (proofs : String) (written : List Compiler.Source) (report : Tree) :
    Compiler.Diagnostic :=
  let (why, name) := reasonOf report
  let message := reasonMessage why (name.getD "")
  match name.bind fun n ↦ written.reverse.findSome? fun s ↦
      (theoremSpan s.text n).map (s.path, ·) with
  | some (path, span) => ⟨path, some span, message⟩
  | none => ⟨proofs, none, message⟩

/-- A present tree's content, or the diagnostic of the failure the runner reports in its
place; the empty tree is the runner's rejection of the program. -/
def present (proofs : String) (written : List Compiler.Source) (result : Tree) :
    Except String Tree :=
  if result.label == 1 then .ok (GebMirror.Metalogic.«Prelude.get» result)
  else if result.label == 2 then .error (rejection proofs written result).render
  else .error s!"{proofs}: the program has no translation into the metalogic"

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

/-! ## The program a document names -/

/-- A proof document as written, read without the profile of its program: its strict encoding
carries its own, and its authoring spelling needs none. -/
def proofDocument (path : System.FilePath) : IO Doc := do
  let text := Command.chars (← IO.FS.readBinFile path)
  if let some (_, doc) := readBasic text then return doc
  let some d := readDoc text | throw <| IO.userError s!"{path}: malformed source document"
  return d

/-- The manifest of the program of a name, for a proof document: the manifest of that program
name in the document's directory, or else in the nearest directory above it that holds one. A
directory holding several is rejected. -/
def manifestNamed (proofs : System.FilePath) (name : String) : IO System.FilePath := do
  let target ← IO.FS.realPath proofs
  for d in (Compiler.ancestors target.toString).drop 1 do
    let found ← (← Compiler.manifestsIn d).filterM fun path ↦ do
      return match ← (Manifest.read path).toBaseIO with
        | .ok m => m.name == name
        | .error _ => false
    match found with
    | [path] => return path
    | [] => continue
    | _ => throw <| IO.userError s!"{proofs}: several manifests of {d} name the program {name}"
  throw <| IO.userError
    s!"{proofs}: no manifest of the program {name} is in the document's directory or above it"

/-- The manifest a proof document is proved against where none is given: that of the program it
names. -/
def manifestOf (proofs : System.FilePath) : IO System.FilePath := do
  let d ← proofDocument proofs
  match ← IO.ofExcept ((programOf d).mapError (s!"{proofs}: {·}")) with
  | some name => manifestNamed proofs name
  | none => throw <| IO.userError s!"{proofs}: the document names no program; give its manifest"

/-! ## Proving and replaying -/

/-- A development read against its program: the profile, the compiled program, the development's
sources as the runner reads them, its documents as written, and its certificate's format. -/
structure Session where
  /-- The profile of the program's manifest. -/
  profile : Profile
  /-- The compiled program. -/
  program : Tree
  /-- The sources of the development. -/
  input : Tree
  /-- The documents of the development in the authoring spelling, as written. -/
  written : List Compiler.Source
  /-- The format of the development's certificate. -/
  format : Tree

/-- Read a development against a manifest's program, whose examples are checked; a development
that does not read is the diagnostic of what rejects it. -/
def Session.read (manifest proofs : String) : IO Session := do
  let (m, text, b) ← readProgram manifest
  checkExamples manifest m text
  let docs ← development proofs m.profile
  let written ← writtenSources (docs.map (·.1))
  let input := sourcesTree docs
  let version ← IO.ofExcept
    (present proofs written (GebMirror.Metalogic.«Authoring.version» b input))
  return ⟨m.profile, b, input, written, formatOf version⟩

/-- The certificate the runner finds for a development, which replays; a theorem its script does
not prove is the diagnostic at its name. -/
def Session.prove (s : Session) (proofs : String) : IO Tree := do
  let cert ← IO.ofExcept
    (present proofs s.written (GebMirror.Metalogic.«Authoring.prove» s.program s.input))
  unless (GebMirror.Metalogic.«Authoring.replay» s.program s.input cert).label == 1 do
    throw <| IO.userError s!"{proofs}: generated certificate does not replay"
  return cert

/-- Prove or replay a development, reporting rejection without replacing an existing output. The
development is the proof document after the documents it imports. A failure the runner reports
of a theorem is a diagnostic at the theorem's name. -/
def execute (mode manifest proofs certificate : String) : IO UInt32 := do
  let s ← Session.read manifest proofs
  match mode with
  | "prove" =>
    let cert ← s.prove proofs
    IO.FS.writeBinFile certificate (writeImage (envelope s.format s.profile s.program cert))
  | "replay" =>
    let some saved := readImage (← IO.FS.readBinFile certificate)
      | throw <| IO.userError s!"{certificate}: malformed certificate image"
    let cert ← IO.ofExcept (certificateOf s.format s.profile s.program saved)
    unless (GebMirror.Metalogic.«Authoring.replay» s.program s.input cert).label == 1 do
      throw <| IO.userError s!"{proofs}: certificate does not prove these statements"
  | _ => throw <| IO.userError "expected prove or replay"
  IO.println s!"{proofs}: {mode} accepted; examples checked"
  return 0

/-- Check a file and write nothing: a proof document, one whose text holds a form
{lit}`(proofs V …)`, is proved against the program it names, and any other file is compiled as
{name}`GebHost.Compiler.checkSource` compiles a source. -/
def checkFile (file : String) : IO UInt32 := do
  let proofs := match Locate.locate (Command.chars (← IO.FS.readBinFile file)) with
    | .ok items => items.any (Locate.headIs kwProofs)
    | .error _ => false
  if proofs then
    let s ← Session.read (← manifestOf file).toString file
    discard <| s.prove file
    return 0
  else Compiler.checkSource Compiler.checked file

end GebHost.Authoring

end
