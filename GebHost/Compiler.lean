/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Command
public import GebBoot
public import GebHost.Locate

set_option doc.verso true

/-!
# Compiled bootstrap compiler entry point

Run the Lean the bootstrap compiler emits from its own source with
{lit}`lake exe geb-compile image|lean [--manifest] INPUT OUTPUT`:
{lit}`image` compiles a program's source file to its image, and {lit}`lean` to a Lean module;
with {lit}`--manifest` the input is the program's
manifest, whose entry points it checks the program defines. The file driver is
{name}`Geb.Kernel.Command.runBytes`. {lit}`lake exe geb-compile check SOURCE` compiles, and
writes nothing, the sources of a program up to one of them: those of the nearest manifest that
lists it, or the source alone where none does; and {lit}`check --manifest MANIFEST` a manifest's
program.

The compiler's entry points return the empty tree for a program they reject. The driver then
reports on standard error what rejects it, exits with status 1 and leaves the output file
untouched, so that an empty output is never written for a failure. It finds what rejects the
program by running the compiler's stages in the order of {lit}`Compile.bundleOf`, each stage's
definitions being those the compiled compiler holds.

A failure is reported as a diagnostic, {lit}`FILE:LINE:COLUMN: error: MESSAGE`, the line and
the column those of the occurrence the failure concerns in the source that holds it, each from
one: a character that is not well formed, a parenthesis that is not closed or closes nothing, an
atom the implementation reserves, the name of the module among whose forms the modules do not
elaborate, or the name of the first declaration that a stage rejects. Where no occurrence is
found the diagnostic is {lit}`INPUT: MESSAGE`. The occurrence is found from the sources
as written ({name}`GebHost.Locate.locate`) after the compiler has rejected the program, and
decides nothing about it.

## Main definitions

* {lit}`GebHost.Compiler.rejection`: what rejects a program the compiler rejects.
* {lit}`GebHost.Compiler.Diagnostic`: a failure with its source occurrence.
* {lit}`GebHost.Compiler.compileManifest`: compile a manifest and check its entry points.
* {lit}`GebHost.Compiler.checkSource`: compile the program a source belongs to, up to it.

## Tags

bootstrap, compiler, diagnostics, command line
-/

open Geb.Kernel
open GebHost.Locate
open scoped FinEnum

public section

namespace GebHost.Compiler

/-- What a rejection concerns, by which its occurrence in the sources is found. -/
inductive Subject where
  /-- The text of a source, which does not read. -/
  | text
  /-- An atom the implementation reserves. -/
  | reserved
  /-- The form of a position among the forms of the program as written. -/
  | form (k : Nat)
  /-- The declaration of a name of the flat program, of a position among those of that name. -/
  | declaration (name : String) (nth : Nat)
  /-- No occurrence. -/
  | program

/-- A stage's rejection of a program: what it concerns, and its message. -/
structure Rejection where
  /-- What the rejection concerns. -/
  subject : Subject
  /-- The message. -/
  message : String

/-- A stage's optional result, or its rejection. -/
def required (t : Tree) (why : Unit → Rejection) : Except Rejection Tree :=
  if (GebBoot.«Prelude.isSome» t).label ≠ 0 then .ok (GebBoot.«Prelude.get» t) else .error (why ())

/-- The position of the first element whose prefix a test of prefixes rejects. -/
def firstRejected (ok : List Tree → Bool) (es : List Tree) : Option Nat :=
  (List.range es.length).find? fun k ↦ !ok (es.take (k + 1))

/-- A nonempty name a tree holds. -/
def nameString? (t : Tree) : Option String :=
  match ofNameTree t with
  | some (c :: cs) => some (String.ofList (c :: cs))
  | _ => none

/-- The name of a form: the atom after its head, where it has one. -/
def formName? (e : Tree) : Option String :=
  e.children[1]?.bind fun n ↦
    if (GebBoot.«Reader.isAtom» n).label ≠ 0 then nameString? (GebBoot.«Reader.nameOf» n)
    else none

/-- A form of a program at a position, as a rejection's subject and in words: the declaration
of the atom after its head, at its position among the forms before it of that name, where it has
one. -/
def formAt (es : List Tree) (k : Nat) : Subject × String :=
  match es[k]?.bind formName? with
  | some n => (.declaration n ((es.take k).countP (formName? · == some n)), n)
  | none => (.program, s!"form {k + 1}")

/-- The rejection of the first form a test of a program's prefixes rejects, its message that of
the form in words. -/
def firstFormRejected (ok : List Tree → Bool) (es : List Tree) (msg : String → String) :
    Rejection :=
  match firstRejected ok es with
  | some k => ⟨(formAt es k).1, msg (formAt es k).2⟩
  | none => ⟨.program, msg "the program"⟩

/-- The message of the seed's elaboration of a program's modules, which the elaboration in the
compiler agrees with on what it rejects and which alone says why. -/
def modulesFailure (file : Tree) : String :=
  let unknown := "the modules do not elaborate"
  match readSExps (file.children.map fun c ↦ Char.ofNat c.label) with
  | none => unknown
  | some es =>
    match elabModules es with
    | .error msg => msg
    | .ok _ => unknown

/-- The failure of a definition the typing names. Module elaboration writes a template's instance
at opaque arguments under a prefix holding the reserved {lit}`%generic`, which no source writes. -/
def checkFailure (n : String) : Rejection :=
  let marker := "%generic"
  if (n.splitOn marker).length > 1 then
    let name := "".intercalate (n.splitOn marker)
    ⟨.declaration name 0, s!"{name} does not check at its template's opaque parameters"⟩
  else ⟨.declaration n 0, s!"{n} does not check"⟩

/-- The first stage of the compiler that rejects a program, with what the rejection concerns.
The modules that do not elaborate are those of the first form among the program's, as written,
with which they do not. -/
def rejection (file : Tree) : Except Rejection Unit := do
  let sx ← required (GebBoot.«Reader.readSExps» file.children) fun _ ↦
    ⟨.text, "the text is not well formed or its parentheses do not balance"⟩
  if (GebBoot.«Compile.userSource» sx).label = 0 then
    throw ⟨.reserved,
      "an atom outside a quotation or a datum begins with %, which the implementation reserves"⟩
  let elaborates (fs : List Tree) := (GebBoot.«Modules.expandModules» fs).label ≠ 0
  let mx ← required (GebBoot.«Modules.expandModules» sx.children) fun _ ↦
    ⟨match firstRejected elaborates sx.children with
      | some k => .form k
      | none => .program, modulesFailure file⟩
  let es := mx.children
  if let some n := nameString? (GebBoot.«Datatype.typeErrorOfForms» es) then
    throw (checkFailure n)
  let expands (fs : List Tree) := (GebBoot.«Datatype.expandProgram» fs).label ≠ 0
  let kx ← required (GebBoot.«Datatype.expandProgram» es) fun _ ↦
    firstFormRejected expands es (s!"{·} does not expand")
  let rx ← required (GebBoot.«Recognize.insertRecognizers» kx.children) fun _ ↦
    ⟨.program, "the recognizers of the program's datatypes cannot be written"⟩
  let fs := rx.children
  let reads (gs : List Tree) := (GebBoot.«Reader.readProgram» gs).label ≠ 0
  let b ← required (GebBoot.«Reader.readProgram» fs) fun _ ↦
    firstFormRejected reads fs
      (s!"{·} does not read: its name is reserved or declared before, " ++
        "or a name in it does not resolve")
  let terms := (b.children.getD 0 (mk 0 [])).children
  let names := (b.children.getD 1 (mk 0 [])).children
  let checks (ts : List Tree) := (GebBoot.«Check.checkProgram» ts).label ≠ 0
  if !checks terms then
    throw <| match firstRejected checks terms with
      | some k =>
        match names[k]?.bind nameString? with
        | some n => ⟨.declaration n 0, s!"{n} is ill-typed"⟩
        | none => ⟨.program, s!"definition {k + 1} is ill-typed"⟩
      | none => ⟨.program, "the program is ill-typed"⟩

/-- What rejects a program, or that no stage does and the backend wrote nothing. -/
def rejectionOf (file : Tree) : Rejection :=
  match rejection file with
  | .error r => r
  | .ok () => ⟨.program, "the backend writes nothing for the program"⟩

/-! ## Diagnostics -/

/-- A source of a program: its path, and its text as written. -/
structure Source where
  /-- The path. -/
  path : String
  /-- The text, a byte to a character. -/
  text : List Char

/-- The source of a file. -/
def Source.read (path : System.FilePath) : IO Source :=
  return ⟨path.toString, Command.chars (← IO.FS.readBinFile path)⟩

/-- A failure with its source occurrence: the file that holds it, or what was compiled where
none is found, the span of the occurrence, and the message. -/
structure Diagnostic where
  /-- The file. -/
  file : String
  /-- The span of the occurrence in the file. -/
  span : Option Span
  /-- The message. -/
  message : String

/-- A diagnostic's line: the file, the line and column at which the occurrence begins, each from
one, and the message, as compilers write an error; without an occurrence, the file and the
message, as the drivers write the failures of reading a manifest or a source. -/
def Diagnostic.render (d : Diagnostic) : String :=
  match d.span with
  | some sp => s!"{d.file}:{sp.start.line}:{sp.start.col}: error: {d.message}"
  | none => s!"{d.file}: {d.message}"

/-- The span at which a form is reported: of its name, the atom after its head, where it has one,
and else of its opening parenthesis. -/
def nameSpan (t : Located) : Span :=
  match t.children[1]? with
  | some n => if n.label.2.isSome then n.label.1 else .at t.label.1.start
  | none => .at t.label.1.start

/-- The occurrence a rejection concerns in a program's sources, in the order the program reads
them, with the message at it: where a source does not read, what rejects its text; the atom
reserved; the form of a position among the sources' forms; and the declaration of a name, at its
position among those of the name or the last of them, or else the declaration that the name is
written after. -/
def occurrence (sources : List Source) (r : Rejection) : Option (String × Span × String) :=
  let located := sources.map fun s ↦ (s.path, locate s.text)
  let items := located.filterMap fun (p, x) ↦ x.toOption.map fun ts ↦ (p, forms ts)
  match r.subject with
  | .text => located.findSome? fun (p, x) ↦
    match x with
    | .error f => some (p, f.span, f.message)
    | .ok _ => none
  | .reserved => items.findSome? fun (p, ts) ↦ (findReserved ts).map (p, ·, r.message)
  | .form k => ((items.flatMap fun (p, ts) ↦ ts.map (p, ·))[k]?).map fun (p, t) ↦
    (p, nameSpan t, r.message)
  | .declaration name nth =>
    let exact := items.flatMap fun (p, ts) ↦ (findDeclarations ts name).map (p, ·, r.message)
    (exact[nth]? <|> exact.getLast?) <|>
      items.findSome? fun (p, ts) ↦ (findEnclosing ts name).map (p, ·, r.message)
  | .program => none

/-- The diagnostic of a rejection of what was compiled from sources. -/
def diagnostic (input : String) (sources : List Source) (r : Rejection) : Diagnostic :=
  match occurrence sources r with
  | some (p, sp, msg) => ⟨p, some sp, msg⟩
  | none => ⟨input, none, r.message⟩

/-- The definitions of a program the compiler reads. -/
def definedNames (file : Tree) : List String :=
  let b := GebBoot.«Compile.bundleOf» file
  if (GebBoot.«Prelude.isSome» b).label = 0 then []
  else (((GebBoot.«Prelude.get» b).children.getD 1 (mk 0 [])).children).filterMap nameString?

/-- What a driver compiles: the bytes the compiler reads, the sources they are read from, and
the check of the names the program defines. -/
structure Input where
  /-- The bytes the compiler reads. -/
  bytes : ByteArray
  /-- The sources, in the order the program reads them. -/
  sources : List Source
  /-- The check of the program's definitions' names. -/
  checkNames : List String → Except String Unit

/-- The input of a source file, its notes erased. -/
def Input.ofFile (path : String) : IO Input :=
  return ⟨← Command.sourceText path, [← Source.read path], fun _ ↦ .ok ()⟩

/-- The input of a list of source files, each with its notes erased. -/
def Input.ofFiles (paths : List System.FilePath) : IO Input :=
  return ⟨← Command.joinSources paths, ← paths.mapM Source.read, fun _ ↦ .ok ()⟩

/-- The input of a manifest's program, whose entry points the program defines. -/
def Input.ofManifest (path : String) : IO Input := do
  let m ← Manifest.read path
  let paths := Manifest.sourcePaths path m
  return { ← Input.ofFiles paths with checkNames := m.checkEntries }

/-- An entry point's output, or the diagnostic of what rejects the program of a named input, the
check of its definitions' names included. -/
def compiled (entry : Tree → Tree) (input : String) (sources : List Source)
    (checkNames : List String → Except String Unit) (file : Tree) : Except String Tree := do
  let out := entry file
  if out == mk 0 [] then throw (diagnostic input sources (rejectionOf file)).render
  (checkNames (definedNames file)).mapError fun msg ↦ (Diagnostic.mk input none msg).render
  return out

/-- Compile an input through an entry point, reporting a failure on standard error. -/
def compileInput (name : String) (entry : Tree → Tree) (input output : String)
    (load : IO Input) : IO UInt32 := do
  try
    let i ← load
    Command.runBytes name (compiled entry input i.sources i.checkNames) i.bytes output
    return 0
  catch e =>
    IO.eprintln e
    return 1

/-- Compile a source file through an entry point, its notes erased. -/
def compileFile (name : String) (entry : Tree → Tree) (input output : String) : IO UInt32 :=
  compileInput name entry input output (Input.ofFile input)

/-- Compile the program of a manifest through an entry point. -/
def compileManifest (name : String) (entry : Tree → Tree) (path output : String) : IO UInt32 :=
  compileInput name entry path output (Input.ofManifest path)

/-! ## Checking a source -/

/-- The compiler without a backend: a program's checked bundle, or the empty tree. -/
def checked (file : Tree) : Tree := GebBoot.«Compile.compileWith» (fun b ↦ b) file

/-- Compile an input through an entry point and write nothing, reporting a failure on standard
error. -/
def checkInput (entry : Tree → Tree) (input : String) (load : IO Input) : IO UInt32 := do
  try
    let i ← load
    discard <| IO.ofExcept
      (compiled entry input i.sources i.checkNames (ofBytes i.bytes))
    return 0
  catch e =>
    IO.eprintln e
    return 1

/-- A path and the directories above it, the nearest first: the path before each of its
separators, and the root for a separator that begins it. -/
def ancestors (path : String) : List System.FilePath :=
  let cs := path.toList
  let cuts := (List.range cs.length).filter fun i ↦
    cs[i]?.any System.FilePath.pathSeparators.contains
  path :: cuts.reverse.map fun i ↦ String.ofList (cs.take (max i 1))

/-- The manifests of a directory, by name. -/
def manifestsIn (dir : System.FilePath) : IO (List System.FilePath) := do
  let paths : List System.FilePath := match ← (dir.readDir).toBaseIO with
    | .ok es => es.toList.map fun e ↦ ⟨s!"{e.root}/{e.fileName}"⟩
    | .error _ => []
  return (paths.filter fun p ↦ ".manifest".toList.isSuffixOf p.toString.toList).mergeSort
    (·.toString ≤ ·.toString)

/-- The sources of the program a source belongs to, up to the source: those of the first
manifest that lists it, among the manifests of its directory and of each directory above, the
nearest first and by name; and the source alone where no manifest lists it. A module imports
modules declared before it, so the sources before one are a program. -/
def sourcesUpTo (source : System.FilePath) : IO (List System.FilePath) := do
  let target ← IO.FS.realPath source
  for d in (ancestors target.toString).drop 1 do
    for path in ← manifestsIn d do
      if let .ok m ← (Manifest.read path).toBaseIO then
        let paths := Manifest.sourcePaths path m
        let real ← paths.mapM fun p ↦ do
          return match ← (IO.FS.realPath p).toBaseIO with
            | .ok r => r
            | .error _ => p
        if let some k := real.findIdx? (·.toString == target.toString) then
          return paths.take (k + 1)
  return [source]

/-- Compile the program a source belongs to, up to the source, and write nothing. -/
def checkSource (entry : Tree → Tree) (source : String) : IO UInt32 :=
  checkInput entry source do Input.ofFiles (← sourcesUpTo source)

/-- Compile a manifest's program and write nothing. -/
def checkManifest (entry : Tree → Tree) (path : String) : IO UInt32 :=
  checkInput entry path (Input.ofManifest path)

end GebHost.Compiler

end
