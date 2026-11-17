/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Chains
import Geb.Prototypes.Kernel.Command

/-!
# The formatter of the authoring profile

`lake exe geb-fmt FILE...` formats each file in place with
`Geb.Kernel.Document.format` within 100 columns; `lake exe geb-fmt --check FILE...` changes
nothing and names each file that formatting would change. After `--chains`, each file is first
converted by `Geb.Kernel.Document.Doc.chains`, which writes each sequence of nested `let` forms
as a `let*` and of nested conditionals as a `cond`, so that `--check --chains` names each file
that holds such a sequence. In place of files, `--manifest MANIFEST`
names a manifest and the sources of its program. A file is read as bytes, one
character per byte, as the host driver reads sources, so its atoms and comments keep their
bytes; each atom is written in its spelling, `Geb.Kernel.Document.spell`.

## Main definitions

* `main`: format files, or check that they are formatted.

## Tags

S-expression, formatter, command line
-/

/-- The bytes of characters, one per character. -/
def bytes (cs : List Char) : ByteArray := ⟨(cs.map fun c ↦ c.toNat.toUInt8).toArray⟩

/-- Format files in place, after `--chains` converting their sequences of bindings and of tests,
or with `--check` name those that would change; exit 1 when a file does not read, or with
`--check` when one would change. -/
public def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let chains := args.contains "--chains"
  let rest := args.filter fun a ↦ a != "--check" && a != "--chains"
  let files ← match rest with
    | ["--manifest", path] =>
      let m ← Geb.Kernel.Manifest.read path
      pure (path :: (Geb.Kernel.Manifest.sourcePaths path m).map toString)
    | fs => pure fs
  if files.isEmpty then
    IO.eprintln "usage: geb-fmt [--check] [--chains] FILE... | \
      geb-fmt [--check] [--chains] --manifest MANIFEST"
    return 2
  let mut status : UInt32 := 0
  for f in files do
    let text := Geb.Kernel.Command.chars (← IO.FS.readBinFile f)
    match (if chains then Geb.Kernel.Document.formatChains else Geb.Kernel.Document.format)
        100 text with
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
