/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
import Geb.Prototypes.Kernel.Command
import Geb.Prototypes.Kernel.MarkupVerso
import GebMeta

/-!
# The check of comments

`lake exe geb-doc --check MANIFEST...` checks the comments and notes of each manifest and of the
sources of its program (`Geb.Kernel.Markup.check`): their prose is in the recorded subset of
Verso's markup, Verso's parser in Lean's core reads it as the subset does
(`Geb.Kernel.Markup.versoBlocks`), and each reference resolves: to a definition the program
declares, to a constant of the `Geb` library, or to an entry of `docs/references.bib`. It names
each failure with the file holding it and exits 1 when there is one.

## Implementation notes

The constants are those of the environment of the `Geb` library, imported from its built
modules, so the library is built first; `lake exe` supplies the path of the modules, and runs
in the package's directory, whose `docs/references.bib` is the bibliography. The import
initializes no environment extension, which would run the interpreter, so Verso's parser reads
with the tokens of Lean's core; the tests compare it with the subset under every token of their
environment. A source
that several manifests list is checked against each of their programs, and a failure it has in
several is named once, with the first manifest in which it occurs.

## Main definitions

* `main`: check the comments of the manifests named.

## Tags

documentation, markup, comment, reference, command line
-/

open Lean Geb.Kernel Geb.Kernel.Markup

namespace GebDocMain

/-- A source document of a file, or what rejects it, the file read as bytes, one character per
byte, as the host driver reads sources. -/
def readFile (path : System.FilePath) : IO (Except String Document.Doc) := do
  return match Document.readDoc (Command.chars (← IO.FS.readBinFile path)) with
    | some d => .ok d
    | none => .error "not well formed, or its parentheses do not balance"

/-- The failures where Verso's reading of a document's prose is not the subset's: those blocks the
subset reads that Verso reads otherwise. -/
def versoFailures (env : Environment) (d : Document.Doc) : List String :=
  (sitesOf d).filterMap fun s ↦
    match s.lines.mapM proseOf with
    | .error _ => none
    | .ok ls =>
      match parseProse ls with
      | .error _ => none
      | .ok bs =>
        let text := "\n".intercalate (ls.map String.ofList)
        match versoBlocks env text with
        | .ok vs => if vs == bs then none
          else some s!"the comment {s.place}: Verso reads its prose otherwise"
        | .error e => some s!"the comment {s.place}: {e}"

/-- The failures of a manifest's comments and of its program's sources, each with its file. -/
def manifestFailures (env : Environment) (R : Resolver) (path : System.FilePath) :
    IO (List (String × String)) := do
  let m ← Manifest.read path
  let files := path :: Manifest.sourcePaths path m
  let docs ← files.mapM fun f ↦ return (f, ← readFile f)
  let decls := docs.flatMap fun (_, d) ↦ match d with
    | .ok d => declsOf d
    | .error _ => []
  return docs.flatMap fun (f, d) ↦
    match d with
    | .ok d => (check decls R d ++ versoFailures env d).map (f.toString, ·)
    | .error e => [(f.toString, e)]

end GebDocMain

open GebDocMain in
/-- Check the comments of the manifests named, naming each failure; exit 1 when there is one. -/
def main : List String → IO UInt32
  | "--check" :: manifests@(_ :: _) => do
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Geb }] {}
    let (_, bib) ← GebMeta.loadBibliography GebMeta.referencesBib
    let R : Resolver :=
      ⟨fun s ↦ env.contains (String.ofList s).toName, fun s ↦ bib.contains (String.ofList s)⟩
    let mut seen : Std.HashSet (String × String) := {}
    for m in manifests do
      for (f, e) in ← manifestFailures env R m do
        unless seen.contains (f, e) do
          seen := seen.insert (f, e)
          IO.eprintln s!"{f}: {e} ({m})"
    return if seen.isEmpty then 0 else 1
  | _ => do
    IO.eprintln "usage: geb-doc --check MANIFEST..."
    return 2
