/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Image
public import Geb.Prototypes.Kernel.Manifest

set_option doc.verso true in
/-!
# The kernel's host driver

The command line of the bootstrap's host: {lit}`build SOURCE … IMAGE` reads a program's
source files in order as one program, checks and evaluates its definitions, and writes its
bundle's image, and {lit}`build --manifest MANIFEST IMAGE` does so for the program of a manifest
({name}`Geb.Kernel.Manifest`), checking that it defines the manifest's entry points;
{lit}`join MANIFEST OUTPUT` writes the text of a manifest's program, and {lit}`layers MANIFEST`
prints a line for each of its layers, the layer's name followed by the paths of its sources;
{lit}`run IMAGE NAME INPUT OUTPUT` reads an image, applies its definition of that name to
the input file's tree, and writes the output tree's bytes. Kernel programs are pure: the
driver alone reads and writes files.

## Main definitions

* {lit}`Geb.Kernel.Command.run` — the command-line interface.
* {lit}`Geb.Kernel.Command.joinSources` — a program's text: its source files, each followed by a
  newline.
* {lit}`Geb.Kernel.Command.runFile` — a function of trees applied to a file, which the
  executable of the compiled bootstrap compiler shares.

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

/-- The bytes of a program's source files in order, each followed by a newline. -/
def joinSources (srcs : List System.FilePath) : IO ByteArray :=
  srcs.foldlM (fun acc src ↦ return (acc ++ (← IO.FS.readBinFile src)).push 10) ByteArray.empty

/-- Apply a function of trees to an input's tree and write the output tree's bytes, raising the
message of the function's failure and leaving the output untouched; the name of the function
identifies it in errors. -/
def runBytes (name : String) (f : Tree → Except String Tree) (input : ByteArray) (output : String) :
    IO Unit := do
  let out ← IO.ofExcept (f (ofBytes input))
  let some bytes := toBytes out
    | throw <| IO.userError s!"{name}: the output has a label beyond a byte"
  IO.FS.writeBinFile output bytes

/-- Apply a function of trees to an input file's tree and write the output tree's bytes, as
{name}`runBytes` does. -/
def runFile (name : String) (f : Tree → Except String Tree) (input output : String) : IO Unit := do
  runBytes name f (← IO.FS.readBinFile input) output

/-- Write the image of a program's text, the checks of its definitions' names passing; what names
the program identifies it in errors. -/
def buildImage (what : String) (text : List Char) (checkNames : List String → Except String Unit)
    (img : String) : IO Unit := do
  if let some msg := diagnose text then throw <| IO.userError s!"{what}: {msg}"
  let some ds := readProgram text
    | throw <| IO.userError s!"{what}: the program does not read"
  if let .error msg := checkNames (ds.map fun d ↦ String.ofList d.1) then
    throw <| IO.userError s!"{what}: {msg}"
  IO.FS.writeBinFile img (writeImage (bundle ds))

/-- Build an image from a program's source or manifest, write or list a manifest's sources, or run
an image's named definition on a file. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | ["build", "--manifest", path, img] =>
    let m ← Manifest.read path
    let text := chars (← joinSources (Manifest.sourcePaths path m))
    buildImage path text m.checkEntries img
    return 0
  | "build" :: files@(_ :: _ :: _) =>
    let srcs := files.dropLast
    let text := chars (← joinSources (srcs.map System.FilePath.mk))
    buildImage s!"{srcs}" text (fun _ ↦ .ok ()) files.getLast!
    return 0
  | ["join", path, output] =>
    let m ← Manifest.read path
    IO.FS.writeBinFile output (← joinSources (Manifest.sourcePaths path m))
    return 0
  | ["layers", path] =>
    let m ← Manifest.read path
    for l in m.layers do
      IO.println (" ".intercalate (l.name :: l.sources.map (toString <| Manifest.resolve path ·)))
    return 0
  | ["run", img, name, input, output] =>
    let some t := readImage (← IO.FS.readBinFile img)
      | throw <| IO.userError s!"{img}: not an image"
    let entry := s!"{img}: {name}"
    runFile entry (fun x ↦ match runEntry t (chars name.toUTF8) x with
      | some y => .ok y
      | none => .error s!"{entry} is not a well-typed definition from trees to trees")
      input output
    return 0
  | _ =>
    throw <| IO.userError <|
      "usage: geb-kernel build SOURCE... IMAGE | geb-kernel build --manifest MANIFEST IMAGE | " ++
        "geb-kernel join MANIFEST OUTPUT | geb-kernel layers MANIFEST | " ++
        "geb-kernel run IMAGE NAME INPUT OUTPUT"

end Geb.Kernel.Command
