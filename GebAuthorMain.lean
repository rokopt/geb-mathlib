/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebHost.Authoring
import GebHost.Migration
import GebHost.Navigation
import GebHost.Editor

/-! # The command-line entry point of the proof-source runner -/

open Geb.Kernel Geb.Kernel.Document

/-- The directory of caches that the option {lit}`--cache DIRECTORY` names among the arguments,
and the arguments without the option. -/
def cacheOption (args : List String) : Option System.FilePath × List String :=
  match args.idxOf? "--cache" with
  | some i =>
    match args[i + 1]? with
    | some dir => (some dir, args.take i ++ args.drop (i + 2))
    | none => (none, args)
  | none => (none, args)

/-- Execute proofs, check a file, list the documents of a development, or convert a document
without discarding its decorations. A proof document is proved against the manifest given, or
else against that of the program it names; with {lit}`--cache DIRECTORY`, {lit}`prove` and
{lit}`check` resume its development from its cache in that directory, and {lit}`transport`
writes the certificate of the present program that a certificate of another program gives. -/
public def main (args : List String) : IO UInt32 := do
  try
    let (caches, args) := cacheOption args
    match args with
    | ["format-buffer"] => GebHost.Editor.run "format"
    | ["editor-holes", manifest] => GebHost.Editor.run "holes" manifest
    | ["migrate-proof-v2", manifest, proofs, certificate] =>
      GebHost.Migration.run manifest proofs certificate
    | ["navigation", manifest] => GebHost.Navigation.run manifest
    | ["compile", manifest, output] =>
      let (m, text, b) ← GebHost.Authoring.readProgram manifest
      GebHost.Authoring.checkExamples manifest m text
      IO.FS.writeBinFile output (writeImage b)
      return 0
    | ["documents", manifest, proofs] =>
      let m ← Manifest.read manifest
      for d in ← GebHost.Authoring.development proofs m.profile do IO.println d.1
      return 0
    | ["check", file] => GebHost.Authoring.checkFile file caches
    | ["prove", proofs, certificate] =>
      let manifest ← GebHost.Authoring.manifestOf proofs
      GebHost.Authoring.execute "prove" manifest.toString proofs certificate caches
    | ["replay", proofs, certificate] =>
      let manifest ← GebHost.Authoring.manifestOf proofs
      GebHost.Authoring.execute "replay" manifest.toString proofs certificate
    | ["transport", proofs, certificate, output] =>
      let manifest ← GebHost.Authoring.manifestOf proofs
      GebHost.Authoring.transport manifest.toString proofs certificate output
    | ["transport", manifest, proofs, certificate, output] =>
      GebHost.Authoring.transport manifest proofs certificate output
    | [mode, manifest, proofs, certificate] =>
      GebHost.Authoring.execute mode manifest proofs certificate
        (if mode == "prove" then caches else none)
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
        geb-author prove [--cache DIRECTORY] [MANIFEST] PROOFS CERTIFICATE\n\
        geb-author replay [MANIFEST] PROOFS CERTIFICATE\n\
        geb-author transport [MANIFEST] PROOFS CERTIFICATE OUTPUT\n\
        geb-author check [--cache DIRECTORY] FILE\n\
        geb-author documents MANIFEST PROOFS\n\
        geb-author navigation MANIFEST < REQUEST.json\n\
        geb-author format-buffer < REQUEST.json\n\
        geb-author editor-holes MANIFEST < REQUEST.json\n\
        geb-author migrate-proof-v2 MANIFEST PROOFS CERTIFICATE\n\
        geb-author convert canonical|advanced|authoring MANIFEST INPUT OUTPUT"
      return 2
  catch e =>
    IO.eprintln e
    return 1
