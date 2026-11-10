/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebHost.Authoring

/-! # The command-line entry point of the proof-source runner -/

open Geb.Kernel Geb.Kernel.Document

/-- Execute proofs, check a file, list the documents of a development, or convert a document
without discarding its decorations. A proof document is proved against the manifest given, or
else against that of the program it names. -/
public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["compile", manifest, output] =>
      let (m, text, b) ← GebHost.Authoring.readProgram manifest
      GebHost.Authoring.checkExamples manifest m text
      IO.FS.writeBinFile output (writeImage b)
      return 0
    | ["documents", manifest, proofs] =>
      let m ← Manifest.read manifest
      for d in ← GebHost.Authoring.development proofs m.profile do IO.println d.1
      return 0
    | ["check", file] => GebHost.Authoring.checkFile file
    | ["prove", proofs, certificate] =>
      let manifest ← GebHost.Authoring.manifestOf proofs
      GebHost.Authoring.execute "prove" manifest.toString proofs certificate
    | ["replay", proofs, certificate] =>
      let manifest ← GebHost.Authoring.manifestOf proofs
      GebHost.Authoring.execute "replay" manifest.toString proofs certificate
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
        geb-author prove|replay [MANIFEST] PROOFS CERTIFICATE\n\
        geb-author check FILE\n\
        geb-author documents MANIFEST PROOFS\n\
        geb-author convert canonical|advanced|authoring MANIFEST INPUT OUTPUT"
      return 2
  catch e =>
    IO.eprintln e
    return 1
