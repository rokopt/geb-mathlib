/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebHost.Authoring

/-! # The command-line entry point of the proof-source runner -/

open Geb.Kernel Geb.Kernel.Document

/-- Execute proofs or convert a document without discarding its decorations. -/
public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["compile", manifest, output] =>
      let (m, text, b) ← GebHost.Authoring.readProgram manifest
      GebHost.Authoring.checkExamples manifest m text
      IO.FS.writeBinFile output (writeImage b)
      return 0
    | [mode, manifest, proofs, certificate] =>
      GebHost.Authoring.execute mode manifest proofs certificate
    | ["convert", spelling, manifest, input, output] =>
      let m ← Manifest.read manifest
      let d ← GebHost.Authoring.readDocument input m.profile
      unless d.wf do throw <| IO.userError s!"{input}: document has no strict encoding"
      let text ← IO.ofExcept <| match spelling with
        | "canonical" => .ok (printCanonDurable d)
        | "advanced" => .ok (printAdvancedDurable 100 d)
        | "authoring" => .ok (printAt (defaultLayout .profile 100 d.doc) d.doc)
        | _ => .error "expected canonical, advanced, or authoring"
      IO.FS.writeBinFile output (GebHost.Authoring.bytesOf text)
      return 0
    | _ =>
      IO.eprintln "usage: geb-author compile MANIFEST IMAGE\n\
        geb-author prove|replay MANIFEST PROOFS CERTIFICATE\n\
        geb-author convert canonical|advanced|authoring MANIFEST INPUT OUTPUT"
      return 2
  catch e =>
    IO.eprintln e
    return 1
