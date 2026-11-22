/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebHost.Compiler

/-! # The command-line entry point of the bootstrap compiler -/

/-- Run the compiled bootstrap compiler on a file. The option {lit}`--cache DIRECTORY`, anywhere
among the arguments, names a directory of kept states, with which a program is compiled a layer
at a time ({name}`GebHost.Layers.bundle`). -/
public def main (args : List String) : IO UInt32 :=
  let cache : Option System.FilePath :=
    (args.idxOf? "--cache").bind fun i ↦ (args[i + 1]?).map (⟨·⟩)
  let rest := match args.idxOf? "--cache" with
    | some i => args.take i ++ args.drop (i + 2)
    | none => args
  match rest with
  | ["image", input, output] =>
    GebHost.Compiler.compileFile "main" GebBoot.«Serialize.image» input output cache
  | ["lean", input, output] =>
    GebHost.Compiler.compileFile "mainLean" GebBoot.«LeanBackend.emitLean» input output cache
  | ["image", "--manifest", m, output] =>
    GebHost.Compiler.compileManifest "main" GebBoot.«Serialize.image» m output cache
  | ["lean", "--manifest", m, output] =>
    GebHost.Compiler.compileManifest "mainLean" GebBoot.«LeanBackend.emitLean» m output cache
  | ["check", "--manifest", m] => GebHost.Compiler.checkManifest GebHost.Compiler.checked m cache
  | ["check", source] => GebHost.Compiler.checkSource GebHost.Compiler.checked source cache
  | ["agree", "--manifest", m] =>
    GebHost.Compiler.agreeInput m (GebHost.Compiler.Input.ofManifest m)
  | ["agree", source] => GebHost.Compiler.agreeInput source (GebHost.Compiler.Input.ofFile source)
  | ["profile", "--manifest", m] =>
    GebHost.Compiler.profileInput m (GebHost.Compiler.Input.ofManifest m)
  | ["profile", source] =>
    GebHost.Compiler.profileInput source (GebHost.Compiler.Input.ofFile source)
  | _ => do
    IO.eprintln "usage: geb-compile image|lean [--cache DIRECTORY] [--manifest] INPUT OUTPUT\n\
      geb-compile check [--cache DIRECTORY] SOURCE\n\
      geb-compile check [--cache DIRECTORY] --manifest MANIFEST\n\
      geb-compile agree [--manifest] INPUT\n\
      geb-compile profile [--manifest] INPUT"
    return 2
