/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command
import GebHost.Requests

/-!
# Kernel executable entry point

Run the bootstrap kernel's host driver with `lake exe geb-kernel`. The command
implementation is `Geb.Kernel.Command.run`, and `interact IMAGE NAME ARGUMENT …` runs an
image's definition of that name as the step of a program that makes requests of its host,
performing them on the file system (`GebHost.Requests.interactBundle`), and exits with the
program's status. The entry point is outside the library's module prefix.

## Main definitions

* `main`: run `interact`, and forward other command-line arguments to
  `Geb.Kernel.Command.run`.

## Tags

bootstrap, kernel, command line
-/

/-- Run the kernel's host driver, or an image's definition as a program's step. -/
public def main : List String → IO UInt32
  | "interact" :: img :: name :: args => do
    let some t := Geb.Kernel.readImage (← IO.FS.readBinFile img)
      | throw <| IO.userError s!"{img}: not an image"
    GebHost.Requests.interactBundle img t name args
  | args => Geb.Kernel.Command.run args
