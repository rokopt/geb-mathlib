/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command

/-!
# Kernel executable entry point

Run the bootstrap kernel's host driver with `lake exe geb-kernel`. The command
implementation is `Geb.Kernel.Command.run`; the entry point is outside the library's module
prefix.

## Main definitions

* `main`: forward command-line arguments to `Geb.Kernel.Command.run`.

## Tags

bootstrap, kernel, command line
-/

/-- Run the kernel's host driver. -/
public def main : List String → IO UInt32 := Geb.Kernel.Command.run
