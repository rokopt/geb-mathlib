/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command
import GebBoot

/-!
# Compiled bootstrap compiler entry point

Run the Lean the bootstrap compiler emits from its own source with
`lake exe geb-compile image|lean INPUT OUTPUT`: `image` compiles a program's source file to its
image, and `lean` to a Lean module. The file driver is `Geb.Kernel.Command.runFile`.

## Main definitions

* `main`: select the compiler's entry point and run it on a file.

## Tags

bootstrap, compiler, command line
-/

/-- Run the compiled bootstrap compiler on a file. -/
public def main : List String → IO UInt32
  | ["image", input, output] => do
    Geb.Kernel.Command.runFile "main" (some ∘ GebBoot.«main») input output
    return 0
  | ["lean", input, output] => do
    Geb.Kernel.Command.runFile "mainLean" (some ∘ GebBoot.«mainLean») input output
    return 0
  | _ => throw <| IO.userError "usage: geb-compile image|lean INPUT OUTPUT"
