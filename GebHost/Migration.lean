/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebHost.Authoring
import GebHost.Json

set_option doc.verso true in
/-!
# Migration of proof documents from version 1 to version 2

The source transformation replaces the version atom and retains every other node and
decoration. Both versions use a theorem followed by its companion, over the same translated
program. Migration replays the saved certificate against the old source and the transformed
source, using the same certificate payload, before changing its format envelope.
No prover is run. The host returns the two artifacts as bytes; the development-record workflow
publishes them together in a new immutable record.

## Main definitions

* {lit}`promote` — the document transformation, retaining its decorations.
* {lit}`run` — checked migration, returning source and certificate bytes as JSON.

## Implementation notes

Only a single version-1 proof document is accepted. This transformation changes neither the
program's semantic edition nor datatype encodings. Its acceptance is replay under both proof
versions, rather than a general theorem about future language versions.

## Tags

authoring, migration, proof document, certificate, replay
-/

set_option doc.verso true

open Geb Geb.Kernel Geb.Kernel.Document
open scoped FinEnum

public section

namespace GebHost.Migration

/-- Replace the version atom of one version-1 proof document, retaining its comments and all
other forms. Version 1 admits no document imports. -/
def promote (d : Doc) : Except String Doc :=
  match d.items with
  | [root] => match root.label.2, root.children with
    | none, head :: version :: body =>
      if atomIs Authoring.kwProofs head && atomIs ['1'] version then
        let v := RoseTree.node (version.label.1, some ['2']) []
        .ok { d with items := [RoseTree.node root.label (head :: v :: body)] }
      else .error "migration requires a proof document of version 1"
    | _, _ => .error "migration requires one (proofs 1 ...) form"
  | _ => .error "migration requires one (proofs 1 ...) form"

/-- An unchanged certificate payload must replay under the specified source and version. -/
def replay (session : Authoring.Session) (certificate : Tree) : IO Unit := do
  let result := GebMirror.Metalogic.«Authoring.replay» session.program session.input certificate
  unless result.label == 1 do
    throw <| IO.userError "the saved certificate does not replay against the migration's source"

/-- Read and replay the old certificate, transform the decorated source, and replay the same
payload against its new statements. Return bytes without writing either input or output files. -/
def run (manifest proofs saved : String) : IO UInt32 := do
  let session ← Authoring.Session.read manifest proofs
  let document ← Authoring.readDocument proofs session.profile
  let doc ← IO.ofExcept (promote document.doc)
  unless decide (session.format = Authoring.formatOf (leaf 1)) do
    throw <| IO.userError "migration requires the version-1 certificate format"
  let some image := readImage (← IO.FS.readBinFile saved)
    | throw <| IO.userError "the saved certificate is not a kernel image"
  let certificate ← IO.ofExcept
    (Authoring.certificateOf session.format session.profile session.program image)
  replay session certificate
  let next := { session with
    input := Authoring.sourcesTree [(proofs, { document with doc })]
    format := Authoring.formatOf (leaf 2) }
  replay next certificate
  let source := Authoring.sourceBytes doc
  let image := writeImage
    (Authoring.envelope next.format next.profile next.program certificate)
  IO.println (Json.object
    [("source", Lean.toJson (source.data.map UInt8.toNat)),
      ("certificate", Lean.toJson (image.data.map UInt8.toNat))]).compress
  return 0

end GebHost.Migration
