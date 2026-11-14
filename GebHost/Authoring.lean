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

Where the runner rejects a development it reports its failures, each a reason and the theorem
concerned, which the host writes as a diagnostic at the theorem's name in the document that
states it ({name}`GebHost.Compiler.Diagnostic`). A theorem whose script leaves a hole open, or
does not prove it, is reported by its obligations instead: each hole, and each innermost step
that fails, at its place in the script as written, with the goal it is given. The goal is the
runner's statement of it, which the host prints in the authoring spelling; the host finds the
place by the positions of the script's children, after expanding the document's abbreviations as
the runner does. Nothing of this is checked: a development with an obligation has no
certificate, and the place and the goal are for the author.

## Main definitions

* {lit}`GebHost.Authoring.readDocument` reads authoring or strict durable documents.
* {lit}`GebHost.Authoring.checkExamples` checks the tree-valued examples in a program's notes.
* {lit}`GebHost.Authoring.development` reads a proof document after the documents it imports.
* {lit}`GebHost.Authoring.manifestOf` finds the manifest of the program a proof document names.
* {lit}`GebHost.Authoring.failuresOf`, {lit}`GebHost.Authoring.diagnosticsOf` read the failures
  the runner reports and locate their obligations.
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

/-! ## Failures and obligations -/

/-- An obligation the runner reports of a theorem's script ({lit}`Authoring.reportOf` of
{lit}`bootstrap/authoring.geb`): a hole the script leaves open, or a step of the script that
does not prove the goal it is given. -/
structure Obligation where
  /-- Whether the obligation is a hole's, and not a failing step's. -/
  hole : Bool
  /-- The name of the hole. -/
  name : String
  /-- The positions of the children from the script down to the hole or the step. -/
  path : List Nat
  /-- The goal, a statement of the internal language as the Geb reader reads one. -/
  goal : Tree

/-- A failure the runner reports of a development: its reason, the theorem it concerns, where it
concerns one, and the obligations of that theorem's script. -/
structure Failure where
  /-- The number of the reason. -/
  why : Nat
  /-- The name of the theorem. -/
  name : Option String
  /-- The obligations. -/
  obligations : List Obligation

/-- The obligation a tree reports: the node of its kind over the hole's name, the node of its path
and its goal. -/
def obligationOf (t : Tree) : Option Obligation :=
  match t.children with
  | [name, path, goal] =>
    some ⟨t.label == 0, String.ofList ((ofNameTree name).getD []), path.children.map (·.label),
      goal⟩
  | _ => none

/-- The failures a runner's report holds: each the node of its reason, the name of the theorem it
concerns, empty where it concerns none, and the theorem's obligations. -/
def failuresOf (report : Tree) : List Failure :=
  report.children.map fun f ↦
    match f.children with
    | why :: name :: obs =>
      ⟨why.label, (ofNameTree name).bind fun cs ↦
        if cs.isEmpty then none else some (String.ofList cs), obs.filterMap obligationOf⟩
    | _ => ⟨0, none, []⟩

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
  | 7 => s!"the script of the theorem {name} leaves holes open"
  | _ => "a document of the development is not (proofs V FORM…) of a version this host reads \
    with a theorem, or a document of version 0 is combined with others, or a document imports \
    one of a later version"

/-- The S-expression a tree of the Geb reader holds: an atom is the node of label 1 over the
leaves of its characters, and a list the node of label 2 over its elements. -/
def sexpOfTree : Tree → SExp :=
  RoseTree.para fun l rs ↦
    if l == 1 then atomOf (rs.map fun r ↦ Char.ofNat r.1.label) else listOf (rs.map Prod.snd)

/-- The greatest length of a goal written on the line of its diagnostic alone. -/
def goalWidth : Nat := 72

/-- A goal as a diagnostic's message holds it: on the diagnostic's line, so that an editor
reading diagnostics a line at a time keeps it, and, where it is longer than
{name}`goalWidth`, also laid out on the lines after, each indented. -/
def goalText (goal : Tree) : String :=
  let d : Doc := ⟨[plain (sexpOfTree goal)], []⟩
  let printed (ds : Array (Bool × ℕ)) : List Char :=
    ((printAt ds d).reverse.dropWhile (· == '\n')).reverse
  let line := printed #[]
  if line.length ≤ goalWidth then String.ofList line
  else
    String.ofList (line ++ '\n' :: ' ' :: ' ' ::
      (printed (defaultLayout .profile 98 d)).flatMap fun c ↦
        if c == '\n' then ['\n', ' ', ' '] else [c])

/-- The message of an obligation of a theorem's script. -/
def obligationMessage (name : String) (o : Obligation) : String :=
  (if o.hole then s!"the script of the theorem {name} leaves the hole ?{o.name} open, at the goal "
    else s!"the script of the theorem {name} does not prove it: this step does not prove the \
      goal ") ++ goalText o.goal

/-- The head of an abbreviation, {lit}`abbreviation`. -/
def kwAbbreviation : List Char := "abbreviation".toList

/-- A located S-expression with every span replaced by one. -/
def relocate (sp : Locate.Span) (t : Locate.Located) : Locate.Located :=
  t.map fun l ↦ (sp, l.2)

/-- The items a located S-expression stands for under abbreviations, the latest first, as
{lit}`Authoring.expandItems` expands them: an atom naming an abbreviation is its items, each at
the atom's span, since the text holds them there. -/
def expandItems (table : List (List Char × List Locate.Located)) :
    Locate.Located → List Locate.Located :=
  RoseTree.elim fun l rs ↦
    match l.2.bind fun name ↦ table.find? (·.1 == name) with
    | some (_, items) => items.map (relocate l.1)
    | none => [RoseTree.node l rs.flatten]

/-- The forms of a proof document's form {lit}`(proofs V …)` as the runner reads them
({lit}`Authoring.readDocument`), each located: from version 2 without the forms the host
resolves, and in version 3 with the abbreviations expanded and left out. -/
def formsOf (root : Locate.Located) : List Locate.Located :=
  let v := ((root.children[1]?.bind (·.label.2)).bind decimal?).getD 0
  let fs := (root.children.drop 2).filter fun f ↦
    !(v > 1 && f.children.length == 2 && (Locate.headIs kwImport f || Locate.headIs kwProgram f))
  (fs.foldl (fun (st : List (List Char × List Locate.Located) × List Locate.Located) f ↦
    match f.children with
    | _ :: n :: item :: items =>
      match n.label.2 with
      | some name =>
        if v > 2 && Locate.headIs kwAbbreviation f && n.children.isEmpty && !name.isEmpty &&
            !isNumeral name then
          ((name, (item :: items).flatMap (expandItems st.1)) :: st.1, st.2)
        else (st.1, st.2 ++ expandItems st.1 f)
      | none => (st.1, st.2 ++ expandItems st.1 f)
    | _ => (st.1, st.2 ++ expandItems st.1 f)) ([], [])).2

/-- The form of a theorem in a document as written, as the runner reads it: the last theorem of
that name among the forms of its form {lit}`(proofs V …)`. -/
def theoremForm (text : List Char) (name : String) : Option Locate.Located :=
  match Locate.locate text with
  | .ok items =>
    ((items.filter (Locate.headIs kwProofs)).flatMap formsOf).reverse.find? fun t ↦
      Locate.headIs kwTheorem t &&
        (t.children[1]?.bind (·.label.2)) == some name.toList
  | .error _ => none

/-- The script of a theorem's form at a path: the script of its form {lit}`(by SCRIPT)`, and at
each position of the path the child of that position. -/
def scriptAt (t : Locate.Located) (path : List Nat) : Option Locate.Located :=
  path.foldl (fun node i ↦ node.bind (·.children[i]?))
    (t.children[3]?.bind (·.children[1]?))

/-- The diagnostics of a failure the runner reports: of each obligation at the hole or the step
of the script it concerns, in the last document as written that states the theorem, and of a
failure without obligations at the theorem's name; where no document as written states the
theorem, at the proof document without a position. -/
def diagnosticsOf (proofs : String) (written : List Compiler.Source) (f : Failure) :
    List Compiler.Diagnostic :=
  let name := f.name.getD ""
  let stated := f.name.bind fun n ↦ written.reverse.findSome? fun s ↦
    (theoremForm s.text n).map (s.path, ·)
  let report (sp : Option Locate.Span) (message : String) : Compiler.Diagnostic :=
    match stated with
    | some (path, t) => ⟨path, some (sp.getD (Compiler.nameSpan t)), message⟩
    | none => ⟨proofs, none, message⟩
  if f.obligations.isEmpty then [report none (reasonMessage f.why name)]
  else f.obligations.map fun o ↦
    report (stated.bind fun st ↦ (scriptAt st.2 o.path).map (·.label.1)) (obligationMessage name o)

/-- The diagnostics of a development the runner written in Geb rejects, one to a line but for the
lines of a goal laid out. -/
def rejection (proofs : String) (written : List Compiler.Source) (report : Tree) : String :=
  "\n".intercalate (((failuresOf report).flatMap (diagnosticsOf proofs written)).map (·.render))

/-- A present tree's content, or the diagnostics of the failures the runner reports in its
place; the empty tree is the runner's rejection of the program. -/
def present (proofs : String) (written : List Compiler.Source) (result : Tree) :
    Except String Tree :=
  if result.label == 1 then .ok (GebMirror.Metalogic.«Prelude.get» result)
  else if result.label == 2 then .error (rejection proofs written result)
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
