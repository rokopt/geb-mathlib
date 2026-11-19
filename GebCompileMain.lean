/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebHost.Compiler

/-! # The command-line entry point of the bootstrap compiler -/

/-- Run the compiled bootstrap compiler on a file. -/
public def main : List String → IO UInt32
  | ["image", input, output] =>
    GebHost.Compiler.compileFile "main" GebBoot.«Serialize.image» input output
  | ["lean", input, output] =>
    GebHost.Compiler.compileFile "mainLean" GebBoot.«LeanBackend.emitLean» input output
  | ["image", "--manifest", m, output] =>
    GebHost.Compiler.compileManifest "main" GebBoot.«Serialize.image» m output
  | ["lean", "--manifest", m, output] =>
    GebHost.Compiler.compileManifest "mainLean" GebBoot.«LeanBackend.emitLean» m output
  | ["check", "--manifest", m] => GebHost.Compiler.checkManifest GebHost.Compiler.checked m
  | ["check", source] => GebHost.Compiler.checkSource GebHost.Compiler.checked source
  | ["profile", "--manifest", m] =>
    GebHost.Compiler.profileInput m (GebHost.Compiler.Input.ofManifest m)
  | ["profile", source] =>
    GebHost.Compiler.profileInput source (GebHost.Compiler.Input.ofFile source)
  | _ => do
    IO.eprintln "usage: geb-compile image|lean [--manifest] INPUT OUTPUT\n\
      geb-compile check SOURCE\n\
      geb-compile check --manifest MANIFEST\n\
      geb-compile profile [--manifest] INPUT"
    return 2
