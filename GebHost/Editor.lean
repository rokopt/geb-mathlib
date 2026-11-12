/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebHost.Navigation
public import Geb.Prototypes.Kernel.Holes

set_option doc.verso true in
/-!
# Editor formatting and kernel obligations

Formatting reads an editor buffer and returns the existing document formatter's bytes without
writing a file. Kernel obligations are checked over a manifest's source snapshots and located
in those same snapshots. Recovered syntax is never passed to the hole checker.

## Main definitions

* {lit}`format` — format a buffer through the document formatter.
* {lit}`holes` — check kernel holes and report their types, contexts and source occurrences.
* {lit}`run` — the JSON command-line interface.

## Tags

editor, formatting, holes, source locations
-/

set_option doc.verso true

open Geb Geb.Kernel Geb.Kernel.Document

public section

namespace GebHost.Editor

/-- Bytes of source text, decoded as UTF-8 by the editor. -/
def charsJson (cs : List Char) : Lean.Json := Lean.toJson (cs.map Char.toNat)

/-- The snapshots in an editor request. -/
def snapshotsOf (request : Lean.Json) : Except String (List (String × String)) := do
  let docs ← request.getObjValAs? (Array Lean.Json) "documents"
  docs.toList.mapM fun d ↦ do
    return (← d.getObjValAs? String "path", ← d.getObjValAs? String "text")

/-- Format the buffer with the document layout, retaining decorations and rejecting incomplete
input. In a CRLF editor buffer, escape newlines inside atoms so the editor's normalization of
inserted line endings changes only separators. This operation writes no file. -/
def format (request : Lean.Json) : Except String Lean.Json := do
  let text ← request.getObjValAs? String "text"
  let some doc := readDoc (Command.chars text.toUTF8)
    | .error "the document is unfinished or malformed; formatting left it unchanged"
  unless doc.wf do throw "the document is malformed; formatting left it unchanged"
  let crlf := (request.getObjValAs? Bool "crlf").toOption.getD false
  let formatted := Navigation.printDocument doc crlf
  return Json.object [("text", charsJson formatted)]

/-- The source occurrences of a hole, excluding quoted data and annotation forms. -/
def occurrences (name : Ident) : Locate.Located → List Locate.Span :=
  RoseTree.para fun l rs ↦
    let t := RoseTree.node l (rs.map Prod.fst)
    if Locate.headIs "quote".toList t || Locate.headIs kwNote t then []
    else if Locate.headIs "datum".toList t then []
    else if Locate.headIs kwHole t then
      if t.children[1]?.any (·.label.2 == some name) then [l.1] else []
    else rs.flatMap Prod.snd

/-- Kernel holes over the exact snapshots supplied by the editor. Each obligation has its
declaring context and every source occurrence; a complete report has no obligations. -/
def holes (manifest : String) (request : Lean.Json) : IO Lean.Json := do
  let snapshots ← IO.ofExcept (snapshotsOf request)
  let sources ← Navigation.readSources manifest snapshots
  let text := ['\n'].intercalate (sources.map fun src ↦
    let doc := src.doc.eraseNotes
    printAt (defaultLayout .profile 100 doc) doc)
  let report ← IO.ofExcept (Holes.check Command.holesBudget text)
  let metas := (report.holes.flatMap fun h ↦ Holes.metasOf h.target).foldl
    (fun ms m ↦ if ms.contains m then ms else ms ++ [m]) []
  let hs := report.holes.map fun h ↦
    let sites := sources.flatMap fun src ↦
      src.forms.flatMap fun t ↦ (occurrences h.name t).map fun span ↦
        Json.object [("file", Lean.toJson src.file), ("span", Navigation.spanJson span)]
    let context := h.context.reverse.map fun (name, ty) ↦
      Json.object [("name", charsJson name),
        ("type", charsJson (Holes.textOf (printType ty)))]
    Json.object [("name", charsJson h.name),
      ("target", charsJson (Holes.textOf (Holes.showType metas h.target))),
      ("context", Lean.toJson context), ("occurrences", Lean.toJson sites)]
  return Json.object [("complete", Lean.toJson report.complete), ("holes", Lean.toJson hs)]

/-- Read one editor request and return its result without modifying the development. -/
def run (action : String) (manifest := "") : IO UInt32 := do
  let request ← IO.ofExcept (Json.parse (← Json.readInput (← IO.getStdin)))
  let result ← if action == "format" then IO.ofExcept (format request)
    else holes manifest request
  IO.println result.compress
  return 0

end GebHost.Editor
