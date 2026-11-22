/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Command
public import GebBoot
public import GebHost.Locate
public import GebHost.Typing
public import GebHost.Layers

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

The driver composes the compiler's front end {lit}`Compile.bundleOf`, the kernel's check and a
backend as the entry points {lit}`main` and {lit}`mainLean` compose them through
{lit}`Compile.compileWith`, so that the bundle the backend writes is also the one whose
definitions' names it checks. For a program the compiler rejects, the driver reports on standard
error what rejects it, exits with status 1 and leaves the output file untouched, so that an empty
output is never written for a failure. It finds what rejects the program by running the compiler's
stages in the order of {lit}`Compile.bundleOf`, each stage's definitions being those the compiled
compiler holds. {lit}`lake exe geb-compile profile [--manifest] INPUT` prints the time of each of
those stages ({lit}`GebHost.Compiler.stageTimes`).

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
* {lit}`GebHost.Compiler.disagreement`: the first difference between the stages that check a form
  against the declarations of its support and those that search every declaration.
* {lit}`GebHost.Compiler.stageTimes`: the time of each stage of the compiler on a program.

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
  /-- A kernel vertex inside a named definition. -/
  | term (name : String) (path : List Nat)
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

/-- The position of the first element whose prefix a test of prefixes rejects, where the test
rejects every prefix that extends one it rejects: the least position of an interval of positions
at which the prefix through the position is rejected, the interval halved a number of times. -/
def firstRejectedIn (ok : List Tree → Bool) (es : List Tree) (fuel lo hi : Nat) : Nat :=
  Nat.rec (motive := fun _ ↦ Nat → Nat → Nat) (fun lo _ ↦ lo)
    (fun _ rec lo hi ↦
      if hi ≤ lo then lo
      else
        let mid := (lo + hi) / 2
        if ok (es.take (mid + 1)) then rec (mid + 1) hi else rec lo mid)
    fuel lo hi

/-- The position of the first element whose prefix a test of prefixes rejects, where the test
rejects every prefix that extends one it rejects, by bisection: the test is applied to a number of
prefixes logarithmic in the list's length. -/
def firstRejected (ok : List Tree → Bool) (es : List Tree) : Option Nat :=
  if ok es then none
  else some (firstRejectedIn ok es (es.length + 1) 0 (es.length - 1))

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
  if let some n := nameString? (GebBoot.«Expansion.typeErrorOfForms» es) then
    if let some f := Typing.inProgram (file.children.map fun c ↦ Char.ofNat c.label) n then
      throw ⟨.term n f.path, s!"{n} does not check: {f.message}"⟩
    throw (checkFailure n)
  let expands (fs : List Tree) := (GebBoot.«Expansion.expandProgram» fs).label ≠ 0
  let kx ← required (GebBoot.«Expansion.expandProgram» es) fun _ ↦
    firstFormRejected expands es (s!"{·} does not expand")
  let rx ← required (GebBoot.«Recognize.insertRecognizers» kx.children) fun _ ↦
    ⟨.program, "the recognizers of the program's datatypes cannot be written"⟩
  let st := GebBoot.«Support.readMore» GebBoot.«Support.readStart» rx.children
  let named (t : Tree) (msg : String → String) : Rejection :=
    match nameString? t with
    | some n => ⟨.declaration n 0, msg n⟩
    | none => ⟨.program, msg "a form"⟩
  let unread := GebBoot.«Support.unreadOf» st
  if (GebBoot.«Prelude.isSome» unread).label ≠ 0 then
    throw <| named (GebBoot.«Prelude.get» unread)
      (s!"{·} does not read: its name is reserved or declared before, " ++
        "or a name in it does not resolve")
  let ill := GebBoot.«Support.illTypedOf» st
  if (GebBoot.«Prelude.isSome» ill).label ≠ 0 then
    throw <| named (GebBoot.«Prelude.get» ill) (s!"{·} is ill-typed")

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
  | .term name path =>
    items.findSome? fun (p, ts) ↦
      ((Typing.occurrences ts name path).head? <|>
        (findDeclarations ts name).head? <|> findEnclosing ts name).map (p, ·, r.message)
  | .program => none

/-- The diagnostic of a rejection of what was compiled from sources. -/
def diagnostic (input : String) (sources : List Source) (r : Rejection) : Diagnostic :=
  match occurrence sources r with
  | some (p, sp, msg) => ⟨p, some sp, msg⟩
  | none => ⟨input, none, r.message⟩

/-- A program's bundle, where the compiler reads it and the kernel's checker types its terms, as
{lit}`Compile.compileWith` takes it from the state {lit}`Compile.readState` gives. -/
def checkedBundle (file : Tree) : Option Tree :=
  let st := GebBoot.«Compile.readState» file
  let b := GebBoot.«Support.readBundle» st
  if (GebBoot.«Prelude.isSome» b).label = 0 then none
  else if (GebBoot.«Prelude.isSome» (GebBoot.«Support.illTypedOf» st)).label ≠ 0 then none
  else some (GebBoot.«Prelude.get» b)

/-- The names of the definitions of a bundle. -/
def definedNames (b : Tree) : List String :=
  ((b.children.getD 1 (mk 0 [])).children).filterMap nameString?

/-- What a driver compiles: the bytes the compiler reads, the sources they are read from, the
bytes by layer, and the check of the names the program defines. -/
structure Input where
  /-- The bytes the compiler reads. -/
  bytes : ByteArray
  /-- The sources, in the order the program reads them. -/
  sources : List Source
  /-- The check of the program's definitions' names. -/
  checkNames : List String → Except String Unit
  /-- The bytes the compiler reads, a layer at a time: joined, they are the bytes. -/
  layers : List ByteArray

/-- The input of a source file, its notes erased. -/
def Input.ofFile (path : String) : IO Input := do
  let bytes ← Command.sourceText path
  return ⟨bytes, [← Source.read path], fun _ ↦ .ok (), [bytes]⟩

/-- The input of lists of source files, a list to a layer, each file with its notes erased. -/
def Input.ofLayers (layers : List (List System.FilePath)) : IO Input := do
  let texts ← layers.mapM Command.joinSources
  return ⟨texts.foldl (· ++ ·) ByteArray.empty, ← layers.flatten.mapM Source.read,
    fun _ ↦ .ok (), texts⟩

/-- The input of a list of source files, each with its notes erased. -/
def Input.ofFiles (paths : List System.FilePath) : IO Input := Input.ofLayers [paths]

/-- The paths of a manifest's sources by layer, the manifest being at a path. -/
def layerPaths (path : System.FilePath) (m : Manifest) : List (List System.FilePath) :=
  m.layers.map fun l ↦ l.sources.map (Manifest.resolve path)

/-- The input of a manifest's program, whose entry points the program defines. -/
def Input.ofManifest (path : String) : IO Input := do
  let m ← Manifest.read path
  return { ← Input.ofLayers (layerPaths path m) with checkNames := m.checkEntries }

/-- A backend's output on the checked bundle of the program of a named input, as
{lit}`Compile.compileWith` gives it, or the diagnostic of what rejects the program, the check of
its definitions' names included. The bundle is computed once, for the backend and the names, and
is the one given where the program was compiled a layer at a time
({name}`GebHost.Layers.bundle`). -/
def compiled (back : Tree → Tree) (input : String) (sources : List Source)
    (checkNames : List String → Except String Unit) (file : Tree) (kept : Option Tree := none) :
    Except String Tree := do
  let reject := fun _ : Unit ↦ (diagnostic input sources (rejectionOf file)).render
  let some b := kept <|> checkedBundle file | throw (reject ())
  let out := back b
  if out == mk 0 [] then throw (reject ())
  (checkNames (definedNames b)).mapError fun msg ↦ (Diagnostic.mk input none msg).render
  return out

/-- The checked bundle of an input compiled a layer at a time, where a directory of kept states
is given and the composition gives one. -/
def keptBundle (cache : Option System.FilePath) (i : Input) : IO (Option Tree) :=
  match cache with
  | some dir => Layers.bundle dir i.layers
  | none => return none

/-- Compile an input through a backend, reporting a failure on standard error; with a directory
of kept states, a layer at a time. -/
def compileInput (name : String) (back : Tree → Tree) (input output : String)
    (load : IO Input) (cache : Option System.FilePath := none) : IO UInt32 := do
  try
    let i ← load
    let kept ← keptBundle cache i
    Command.runBytes name (compiled back input i.sources i.checkNames (kept := kept)) i.bytes
      output
    return 0
  catch e =>
    IO.eprintln e
    return 1

/-- Compile a source file through a backend, its notes erased. -/
def compileFile (name : String) (back : Tree → Tree) (input output : String)
    (cache : Option System.FilePath := none) : IO UInt32 :=
  compileInput name back input output (Input.ofFile input) cache

/-- Compile the program of a manifest through a backend. -/
def compileManifest (name : String) (back : Tree → Tree) (path output : String)
    (cache : Option System.FilePath := none) : IO UInt32 :=
  compileInput name back path output (Input.ofManifest path) cache

/-! ## Checking a source -/

/-- The backend of a check: the checked bundle itself. -/
def checked (b : Tree) : Tree := b

/-- Compile an input through a backend and write nothing, reporting a failure on standard
error. -/
def checkInput (back : Tree → Tree) (input : String) (load : IO Input)
    (cache : Option System.FilePath := none) : IO UInt32 := do
  try
    let i ← load
    let kept ← keptBundle cache i
    discard <| IO.ofExcept
      (compiled back input i.sources i.checkNames (ofBytes i.bytes) kept)
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

/-- The first elements of lists in order, a number of them in all, list by list. -/
def takeAcross {α : Type} (layers : List (List α)) (n : Nat) : List (List α) :=
  (layers.foldl (init := (([] : List (List α)), n)) fun (acc, left) l ↦
    if left = 0 then (acc, 0) else (acc ++ [l.take left], left - (l.take left).length)).1

/-- The sources of the program a source belongs to, up to the source, by layer: those of the
first manifest that lists it, among the manifests of its directory and of each directory above,
the nearest first and by name; and the source alone where no manifest lists it. A module imports
modules declared before it, so the sources before one are a program. -/
def sourcesUpTo (source : System.FilePath) : IO (List (List System.FilePath)) := do
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
          return takeAcross (layerPaths path m) (k + 1)
  return [[source]]

/-- Compile the program a source belongs to, up to the source, and write nothing. -/
def checkSource (back : Tree → Tree) (source : String)
    (cache : Option System.FilePath := none) : IO UInt32 :=
  checkInput back source (do Input.ofLayers (← sourcesUpTo source)) cache

/-- Compile a manifest's program and write nothing. -/
def checkManifest (back : Tree → Tree) (path : String)
    (cache : Option System.FilePath := none) : IO UInt32 :=
  checkInput back path (Input.ofManifest path) cache

/-! ## The agreement of the stages over supports with the stages over whole environments -/

/-- The first difference between what the compiler's stages give a program where the typing and
the reading check each form against the declarations of its support ({lit}`Expansion.check`,
{lit}`Support.readMore`) and where they search the lists of every declaration before it
({lit}`Typing.checkForms`, {lit}`Reader.readProgram`, {lit}`Check.checkProgram`): the name of
the first definition the typing rejects, the kernel forms the expansion writes, the bundle the
reading gives, and whether the kernel's checker types every term. No difference where a stage
before them rejects the program. -/
def disagreement (file : Tree) : Option String := Id.run do
  let sx := GebBoot.«Reader.readSExps» file.children
  if (GebBoot.«Prelude.isSome» sx).label = 0 then return none
  if (GebBoot.«Compile.userSource» (GebBoot.«Prelude.get» sx)).label = 0 then return none
  let mx := GebBoot.«Modules.expandModules» (GebBoot.«Prelude.get» sx).children
  if (GebBoot.«Prelude.isSome» mx).label = 0 then return none
  let es := (GebBoot.«Prelude.get» mx).children
  let whole := GebBoot.«Datatype.typeErrorOfForms» es
  let over := GebBoot.«Expansion.typeErrorOfForms» es
  if whole != over then
    return some s!"the typing rejects {nameString? whole} over whole environments and \
      {nameString? over} over supports"
  let kx := GebBoot.«Datatype.expandProgram» es
  if kx != GebBoot.«Expansion.expandProgram» es then
    return some "the expansions write different kernel forms"
  if (GebBoot.«Prelude.isSome» kx).label = 0 then return none
  let rx := GebBoot.«Recognize.insertRecognizers» (GebBoot.«Prelude.get» kx).children
  if (GebBoot.«Prelude.isSome» rx).label = 0 then return none
  let fs := (GebBoot.«Prelude.get» rx).children
  let b := GebBoot.«Reader.readProgram» fs
  let st := GebBoot.«Support.readMore» GebBoot.«Support.readStart» fs
  if b != GebBoot.«Support.readBundle» st then
    return some "the readings give different bundles"
  if (GebBoot.«Prelude.isSome» b).label = 0 then return none
  let terms := ((GebBoot.«Prelude.get» b).children.getD 0 (mk 0 [])).children
  let typed := (GebBoot.«Prelude.isSome» (GebBoot.«Check.checkProgram» terms)).label != 0
  let typedOver := (GebBoot.«Prelude.isSome» (GebBoot.«Support.illTypedOf» st)).label == 0
  if typed != typedOver then
    return some s!"the kernel's checker types the program over whole environments: {typed}; \
      over supports: {typedOver}"
  return none

/-- Compare the compiler's stages over supports with its stages over whole environments on an
input, reporting a difference on standard error. -/
def agreeInput (input : String) (load : IO Input) : IO UInt32 := do
  try
    let i ← load
    match disagreement (ofBytes i.bytes) with
    | some d =>
      IO.eprintln s!"{input}: {d}"
      return 1
    | none => return 0
  catch e =>
    IO.eprintln e
    return 1

/-! ## The time of each stage -/

/-- A value computed in {name}`IO`, with the milliseconds its computation took. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0) / 1000000)

/-- The stages of {lit}`Compile.compileWith` composed as {lit}`Compile.readState` and
{lit}`Expansion.expandProgram` compose them, each stage's milliseconds and the number of trees it
gives, or the name of the first stage that rejects the program. The expansion of the datatype
language is divided into the decoding of the forms by their recognizer, the expansion with their
datatypes, the typing and the erasure; the reading resolves each definition's term and types it
by the kernel's checker. -/
def stageTimes (file : Tree) : IO (List (String × Nat × Nat) × Option String) := do
  let mut rows : List (String × Nat × Nat) := []
  let (sx, t) ← timed fun _ ↦ GebBoot.«Reader.readSExps» file.children
  if (GebBoot.«Prelude.isSome» sx).label = 0 then return (rows, some "read")
  let es := (GebBoot.«Prelude.get» sx).children
  rows := rows ++ [("read", t, es.length)]
  let (u, t) ← timed fun _ ↦ GebBoot.«Compile.userSource» (GebBoot.«Prelude.get» sx)
  rows := rows ++ [("reserved", t, 1)]
  if u.label = 0 then return (rows, some "reserved")
  let (mx, t) ← timed fun _ ↦ GebBoot.«Modules.expandModules» es
  if (GebBoot.«Prelude.isSome» mx).label = 0 then return (rows, some "modules")
  let ms := (GebBoot.«Prelude.get» mx).children
  rows := rows ++ [("modules", t, ms.length)]
  let (d, t) ← timed fun _ ↦ GebBoot.«Typing.Tx.member» (mk 2 ms)
  rows := rows ++ [("decode", t, 1)]
  if d.label = 0 then return (rows, some "decode")
  let (x, t) ← timed fun _ ↦ GebBoot.«Datatype.expandTyped» ms
  rows := rows ++ [("expand", t, x.2.length)]
  if x.1.label = 0 then return (rows, some "expand")
  let (c, t) ← timed fun _ ↦ GebBoot.«Expansion.check» (GebBoot.«Datatype.markersFirst» x.2)
  rows := rows ++ [("typing", t, 1)]
  if c.label = 1 then return (rows, some "typing")
  let (ks, t) ← timed fun _ ↦ GebBoot.«Datatype.kernelForms» x.2
  rows := rows ++ [("erase", t, ks.length)]
  let (rx, t) ← timed fun _ ↦ GebBoot.«Recognize.insertRecognizers» ks
  if (GebBoot.«Prelude.isSome» rx).label = 0 then return (rows, some "recognizers")
  let fs := (GebBoot.«Prelude.get» rx).children
  rows := rows ++ [("recognizers", t, fs.length)]
  let (st, t) ← timed fun _ ↦ GebBoot.«Support.readMore» GebBoot.«Support.readStart» fs
  let b := GebBoot.«Support.readBundle» st
  if (GebBoot.«Prelude.isSome» b).label = 0 then return (rows, some "reading")
  let terms := ((GebBoot.«Prelude.get» b).children.getD 0 (mk 0 [])).children
  rows := rows ++ [("reading", t, terms.length)]
  if (GebBoot.«Prelude.isSome» (GebBoot.«Support.illTypedOf» st)).label ≠ 0 then
    return (rows, some "reading")
  return (rows, none)

/-- Print the time of each stage of the compiler on an input, one line a stage: its name, its
milliseconds and the number of trees it gives. -/
def profileInput (input : String) (load : IO Input) : IO UInt32 := do
  try
    let i ← load
    let (rows, rejected) ← stageTimes (ofBytes i.bytes)
    for (name, ms, n) in rows do
      IO.println s!"{name}\t{ms}\t{n}"
    IO.println s!"total\t{(rows.map (·.2.1)).sum}"
    match rejected with
    | some s =>
      IO.eprintln s!"{input}: the stage {s} rejects the program"
      return 1
    | none => return 0
  catch e =>
    IO.eprintln e
    return 1

end GebHost.Compiler

end
