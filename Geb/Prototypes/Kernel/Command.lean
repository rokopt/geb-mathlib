/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Image

set_option doc.verso true in
/-!
# The kernel's host driver

The command line of the bootstrap's host: {lit}`build SOURCE IMAGE` reads a program's
source, checks and evaluates its definitions, and writes its bundle's image;
{lit}`run IMAGE NAME INPUT OUTPUT` reads an image, applies its definition of that name to
the input file's tree, and writes the output tree's bytes. Kernel programs are pure: the
driver alone reads and writes files.

## Main definitions

* {lit}`Geb.Kernel.Command.run` — the command-line interface.

## Implementation notes

Source files and names are read byte by byte, each byte a character, so names are ASCII.
Errors are raised as {name}`IO.Error`s, which the executable's runtime reports on standard
error with a nonzero exit status; a failed command leaves its output file untouched.

## Tags

bootstrap, kernel, command line, file I/O
-/

set_option doc.verso true

public section

namespace Geb.Kernel.Command

/-- The characters of a sequence of bytes, one per byte. -/
def chars (b : ByteArray) : List Char := b.data.toList.map fun x ↦ Char.ofNat x.toNat

/-- Build an image from a program's source, or run an image's named definition on a file.
-/
def run (args : List String) : IO UInt32 := do
  match args with
  | ["build", src, img] =>
    let some ds := readProgram (chars (← IO.FS.readBinFile src))
      | throw <| IO.userError s!"{src}: the program does not read"
    let some _ := load (ds.map Prod.snd)
      | throw <| IO.userError s!"{src}: the program does not type-check"
    IO.FS.writeBinFile img (writeImage (bundle ds))
    return 0
  | ["run", img, name, input, output] =>
    let some t := readImage (← IO.FS.readBinFile img)
      | throw <| IO.userError s!"{img}: not an image"
    let some out := runEntry t (chars name.toUTF8) (ofBytes (← IO.FS.readBinFile input))
      | throw <| IO.userError s!"{img}: {name} is not a well-typed definition from trees to trees"
    let some bytes := toBytes out
      | throw <| IO.userError s!"{name}: the output has a label beyond a byte"
    IO.FS.writeBinFile output bytes
    return 0
  | _ =>
    throw <| IO.userError
      "usage: geb-kernel build SOURCE IMAGE | geb-kernel run IMAGE NAME INPUT OUTPUT"

end Geb.Kernel.Command
