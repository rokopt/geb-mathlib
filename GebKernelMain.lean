/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command
import GebHost.Requests
import GebHost.Compiler

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

/-- Print the suspending kernel checker's obligations, or the datatype typing's located
obligations for sources outside the kernel language. -/
private def sourceHoles (what : String) (paths : List System.FilePath) : IO UInt32 := do
  let text := Geb.Kernel.Command.chars (← Geb.Kernel.Command.joinSources paths)
  if let some checked := GebHost.Compiler.kernelObligations text then
    let r ← IO.ofExcept (checked.mapError (s!"{what}: {·}"))
    IO.print (String.ofList r.render)
    return if r.complete then 0 else 2
  let hs ← IO.ofExcept (GebHost.Compiler.datatypeHoles what text
    (← paths.mapM GebHost.Compiler.Source.read))
  if hs.isEmpty then IO.println "complete"
  for (h, path, sp) in hs do
    IO.println s!"{path}:{sp.start.line}:{sp.start.col}: {GebHost.Compiler.holeMessage h}"
  return if hs.isEmpty then 0 else 2

/-- Run the kernel's host driver, or an image's definition as a program's step. -/
public def main : List String → IO UInt32
  | "interact" :: img :: name :: args => do
    let some t := Geb.Kernel.readImage (← IO.FS.readBinFile img)
      | throw <| IO.userError s!"{img}: not an image"
    GebHost.Requests.interactBundle img t name args
  | ["holes", "--manifest", path] => do
    let m ← Geb.Kernel.Manifest.readProgram path
    sourceHoles path (Geb.Kernel.Manifest.sourcePaths path m)
  | "holes" :: paths@(_ :: _) => sourceHoles s!"{paths}" (paths.map System.FilePath.mk)
  | args => Geb.Kernel.Command.run args
