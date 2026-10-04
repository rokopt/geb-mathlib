/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command
import Geb.Prototypes.Kernel.Document

/-!
# The formatter of the authoring profile

`lake exe geb-fmt FILE...` formats each file in place with
`Geb.Kernel.Document.format` within 100 columns; `lake exe geb-fmt --check FILE...` changes
nothing and names each file that formatting would change. A file is read as bytes, one
character per byte, as the host driver reads sources, so its atoms and comments keep their
bytes; each atom is written in its spelling, `Geb.Kernel.Document.spell`.

## Main definitions

* `main`: format files, or check that they are formatted.

## Tags

S-expression, formatter, command line
-/

/-- The bytes of characters, one per character. -/
def bytes (cs : List Char) : ByteArray := ⟨(cs.map fun c ↦ c.toNat.toUInt8).toArray⟩

/-- Format files in place, or with `--check` name those formatting would change; exit 1 when a
file does not read, or with `--check` when one would change. -/
public def main (args : List String) : IO UInt32 := do
  let (check, files) := match args with
    | "--check" :: fs => (true, fs)
    | fs => (false, fs)
  if files.isEmpty then
    IO.eprintln "usage: geb-fmt [--check] FILE..."
    return 2
  let mut status : UInt32 := 0
  for f in files do
    let text := Geb.Kernel.Command.chars (← IO.FS.readBinFile f)
    match Geb.Kernel.Document.format 100 text with
    | none =>
      IO.eprintln s!"geb-fmt: {f}: not well formed, or its parentheses do not balance"
      status := 1
    | some out =>
      if out != text then
        if check then
          IO.println s!"{f}: not formatted"
          status := 1
        else
          IO.FS.writeBinFile f (bytes out)
  return status
